/-
Free Markov categories, Stage 7: the value of a class respects the operations of `F_s(G)`
(Joyal–Street, Theorem 2.2: the value is a strict monoidal functor), and the comparison map
`Syn_s(G) → F_s(G)` is injective.

* `value_oneNode`, `value_idD`, `value_braidD`: generators, identities and symmetries;
* `value_tensor`, `value_glue`: disjoint union and gluing;
* `FsC.value_toDHom`: the value of the class of a formal composite is that composite, so the
  value is a left inverse of `FsC.toDHom` (`FsC.toDHom_injective`).
-/
module

public import FreeMarkov.Stage7.Value
public import FreeMarkov.Stage7.Passive

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open CategoryTheory StrictSMC FreeGraphMonoid Wires

open scoped Classical

attribute [local instance 2000] Classical.propDecidable

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

theorem obj_vdata_letters {E : Type u₂} (Γ : Diagram G Empty E) {a : FreeMonoid S} (l : List E)
    (h : FreeMonoid.ofList (l.map Γ.val.v₀) = a) : obj Γ.vdata.lab l = Syn.of G a := by
  rw [obj_vdata, h]; rfl

/-- The value of a one-node diagram is its generator. -/
theorem value_oneNode (x : G.A) : (oneNode x).value = Arrow.mk (Syn.gen x) := by
  set Γ := oneNode x
  have hV := Γ.vdata_good
  have hrest : Γ.vdata.rest Γ.dom () = [] := by
    simp only [VData.rest, List.filter_eq_nil_iff, decide_eq_true_eq, not_not]
    intro e he; exact he
  have hnext : Γ.vdata.next Γ.dom () = Γ.cod := by
    rw [VData.next, hrest, List.append_nil]; rfl
  have hins : Γ.vdata.ins () = Γ.dom := rfl
  have hok : Γ.vdata.Ok Γ.dom [()] := by
    refine ⟨Γ.dom_nodup, fun e he => he, fun e he he' => ?_, ?_⟩
    · have h₁ := (Γ.mem_dom e).1 he'
      have h₂ := (Γ.mem_outs () e).1 he
      rw [h₁] at h₂; cases h₂
    · rw [hnext]; exact Γ.cod_nodup
  have hc₀ : (Γ.vdata.wend Γ.dom [()]).Perm Γ.cod := by
    rw [VData.wend_cons, hnext]; rfl
  rw [Γ.value_eq (xs := [()]) (List.nodup_singleton _) (fun u => List.mem_singleton.2 rfl) hok,
    VData.val_cons _ hV hok hc₀, VData.step, hrest, hnext, List.append_nil, hins, perm_self,
    obj_nil, AArr.tensor_id_one, AArr.id_comp (by rw [hV.gen_left, hins]),
    VData.val_nil _ (List.Perm.refl _), perm_self, AArr.comp_id]
  · rfl
  · rw [hV.gen_right]; rfl

/-- The value of an identity diagram is the identity. -/
theorem value_idD (a : FreeMonoid S) : (idD G a).value = Arrow.mk (𝟙 (Syn.of G a)) := by
  set Γ := idD G a
  have hok : Γ.vdata.Ok Γ.dom [] := Γ.dom_nodup
  have hp : Γ.dom.Perm Γ.cod := List.Perm.refl _
  rw [Γ.value_eq List.nodup_nil (fun x => x.elim) hok, VData.val_nil _ hp]
  show perm Γ.vdata.lab Γ.dom Γ.dom = _
  rw [perm_self, obj_vdata_letters Γ _ (idD_domWord a)]
  rfl

/-- The value of a symmetry diagram is the symmetry. -/
theorem value_braidD (a b : FreeMonoid S) :
    (braidD G a b).value = Arrow.mk (σ_ (Syn.of G a) (Syn.of G b)) := by
  set Γ := braidD G a b
  have hok : Γ.vdata.Ok Γ.dom [] := Γ.dom_nodup
  have hd : Γ.dom = (List.finRange (wlen a)).map Sum.inl ++ (List.finRange (wlen b)).map Sum.inr :=
    rfl
  have hc : Γ.cod = (List.finRange (wlen b)).map Sum.inr ++ (List.finRange (wlen a)).map Sum.inl :=
    rfl
  have ha : obj Γ.vdata.lab ((List.finRange (wlen a)).map Sum.inl) = Syn.of G a :=
    obj_vdata_letters Γ _ (by simp only [List.map_map]; exact ofList_map_letters a)
  have hb : obj Γ.vdata.lab ((List.finRange (wlen b)).map Sum.inr) = Syn.of G b :=
    obj_vdata_letters Γ _ (by simp only [List.map_map]; exact ofList_map_letters b)
  have hp : Γ.dom.Perm Γ.cod := by
    rw [hd, hc]; exact List.perm_append_comm
  have hn : ((List.finRange (wlen a)).map Sum.inl ++
      (List.finRange (wlen b)).map Sum.inr : List (Fin (wlen a) ⊕ Fin (wlen b))).Nodup := by
    rw [← hd]; exact Γ.dom_nodup
  rw [Γ.value_eq List.nodup_nil (fun x => x.elim) hok, VData.val_nil _ hp, hd, hc,
    perm_swap _ hn, ha, hb]
  rfl

/-! ### Disjoint union -/

section Tensor

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄} [Fintype N] [Fintype N']

omit [Fintype N] [Fintype N'] in
theorem isMap_tensorL (Γ : Diagram G N E) (Δ : Diagram G N' E') :
    VData.IsMap Γ.vdata (Γ.tensor Δ).vdata Sum.inl Sum.inl where
  inj := Sum.inl_injective
  ins _ := rfl
  outs _ := rfl
  lab _ := rfl
  gen _ := rfl

omit [Fintype N] [Fintype N'] in
theorem isMap_tensorR (Γ : Diagram G N E) (Δ : Diagram G N' E') :
    VData.IsMap Δ.vdata (Γ.tensor Δ).vdata Sum.inr Sum.inr where
  inj := Sum.inr_injective
  ins _ := rfl
  outs _ := rfl
  lab _ := rfl
  gen _ := rfl

/-- The value of a disjoint union is the monoidal product of the values. -/
theorem value_tensor (Γ : Diagram G N E) (Δ : Diagram G N' E') :
    (Γ.tensor Δ).value = AArr.tensor Γ.value Δ.value := by
  obtain ⟨xs, hn, hall, hok, hc, hΓ⟩ := Γ.value_spec
  obtain ⟨ys, hn', hall', hok', hc', hΔ⟩ := Δ.value_spec
  set T := Γ.tensor Δ
  have mL := isMap_tensorL Γ Δ
  have mR := isMap_tensorR Γ Δ
  have hV := Γ.vdata_good
  have hV' := Δ.vdata_good
  have hVT := T.vdata_good
  have hB : ∀ b ∈ Δ.dom.map Sum.inr, ∀ e : E, (Sum.inl e : E ⊕ E') ≠ b := by
    intro b hb e he; obtain ⟨d, -, rfl⟩ := List.mem_map.1 hb; cases he
  have hA : ∀ a ∈ (Γ.vdata.wend Γ.dom xs).map Sum.inl, ∀ e : E', (Sum.inr e : E ⊕ E') ≠ a := by
    intro a ha e he; obtain ⟨d, -, rfl⟩ := List.mem_map.1 ha; cases he
  have hA' : ∀ a ∈ Γ.cod.map Sum.inl, ∀ e : E', (Sum.inr e : E ⊕ E') ≠ a := by
    intro a ha e he; obtain ⟨d, -, rfl⟩ := List.mem_map.1 ha; cases he
  have hdT : T.dom = Γ.dom.map Sum.inl ++ Δ.dom.map Sum.inr := rfl
  have hcT : T.cod = Γ.cod.map Sum.inl ++ Δ.cod.map Sum.inr := rfl
  have hwnd' : (Γ.vdata.wend Γ.dom xs).Nodup := Γ.vdata.wend_nodup hV hok
  have hwnd2 : ((Γ.vdata.wend Γ.dom xs).map Sum.inl : List (E ⊕ E')).Nodup :=
    List.Nodup.map Sum.inl_injective hwnd'
  have hcnd : ((Γ.cod).map Sum.inl : List (E ⊕ E')).Nodup :=
    List.Nodup.map Sum.inl_injective Γ.cod_nodup
  have ok₁ : T.vdata.Ok T.dom (xs.map Sum.inl) := by
    rw [hdT]; exact mL.ok_append_right hB (List.Nodup.map Sum.inr_injective Δ.dom_nodup) hok
  have hw₁ : T.vdata.wend T.dom (xs.map Sum.inl) =
      (Γ.vdata.wend Γ.dom xs).map Sum.inl ++ Δ.dom.map Sum.inr := by
    rw [hdT]; exact mL.wend_append_right hB _ _
  have ok₂ : T.vdata.Ok ((Γ.vdata.wend Γ.dom xs).map Sum.inl ++ Δ.dom.map Sum.inr)
      (ys.map Sum.inr) := mR.ok_append_left hA hwnd2 hok'
  have okT : T.vdata.Ok T.dom (xs.map Sum.inl ++ ys.map Sum.inr) :=
    (VData.ok_append _).2 ⟨ok₁, by rw [hw₁]; exact ok₂⟩
  have hp₁ : ((Γ.vdata.wend Γ.dom xs).map Sum.inl ++ Δ.dom.map Sum.inr).Perm
      (Γ.cod.map Sum.inl ++ Δ.dom.map Sum.inr) :=
    List.Perm.append_right _ (List.Perm.map _ hc)
  have hcT' : (T.vdata.wend T.dom (xs.map Sum.inl ++ ys.map Sum.inr)).Perm T.cod := by
    rw [VData.wend_append, hw₁]
    exact (T.vdata.wend_perm hp₁ _).trans ((mR.wend_append_left hA' _ _).trans
      (by rw [hcT]; exact List.Perm.append_left _ (List.Perm.map _ hc')))
  have hcT₂ : (T.vdata.wend (Γ.cod.map Sum.inl ++ Δ.dom.map Sum.inr) (ys.map Sum.inr)).Perm
      (Γ.cod.map Sum.inl ++ Δ.cod.map Sum.inr) :=
    (mR.wend_append_left hA' _ _).trans (List.Perm.append_left _ (List.Perm.map _ hc'))
  have hcT₃ : (T.vdata.wend ((Γ.vdata.wend Γ.dom xs).map Sum.inl ++ Δ.dom.map Sum.inr)
      (ys.map Sum.inr)).Perm T.cod := by
    have := hcT'
    rw [VData.wend_append, hw₁] at this
    exact this
  rw [T.value_eq (List.nodup_append.2 ⟨List.Nodup.map Sum.inl_injective hn,
      List.Nodup.map Sum.inr_injective hn', by simp⟩)
    (by rintro (x | y) <;> simp [hall, hall']) okT, T.vdata.val_append hVT okT hcT', hw₁,
    hdT, mL.steps_append_right hV hB hok, T.vdata.val_perm hVT ok₂ hp₁ hcT₃, hcT,
    mR.val_append_left hV' hVT hA' (List.Nodup.map Sum.inl_injective Γ.cod_nodup) hok' hc',
    perm_append _ (List.Perm.map _ hc) (List.Perm.refl _), perm_self, perm_map _ _ mL.inj,
    mL.lab_comp, ← AArr.comp_assoc, ← AArr.tensor_comp_id, ← AArr.tensor_comp, AArr.comp_id,
    AArr.id_comp, hΓ, hΔ]
  · rfl
  all_goals simp [T, mL.obj_map, mR.obj_map, Γ.vdata.steps_right hV hok, perm_left _ hc,
    perm_right _ hc, Δ.vdata.val_left hV' hok']

end Tensor

/-! ### Gluing -/

section Glue

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄} [Fintype N] [Fintype N']

omit [Fintype N] [Fintype N'] in
theorem isMap_glueL (Γ : Diagram G N E) (Δ : Diagram G N' E') (h : Γ.codWord = Δ.domWord) :
    VData.IsMap Γ.vdata (Γ.glue Δ h).vdata Sum.inl Sum.inl where
  inj := Sum.inl_injective
  ins _ := rfl
  outs _ := rfl
  lab _ := rfl
  gen _ := rfl

omit [Fintype N] [Fintype N'] in
theorem isMap_glueR (Γ : Diagram G N E) (Δ : Diagram G N' E') (h : Γ.codWord = Δ.domWord) :
    VData.IsMap Δ.vdata (Γ.glue Δ h).vdata (PEmb.gIn h) Sum.inr where
  inj := PGraph.glueIn_injective _
  ins _ := rfl
  outs _ := rfl
  lab e := congrArg (fun s => Syn.of G (FreeMonoid.of s))
    (Valuation.glueIn_v₀ _ Γ.val Δ.val (matching_v₀ h) e)
  gen _ := rfl

/-- The value of a gluing is the composite of the values. -/
theorem value_glue (Γ : Diagram G N E) (Δ : Diagram G N' E') (h : Γ.codWord = Δ.domWord) :
    (Γ.glue Δ h).value = AArr.comp Γ.value Δ.value := by
  obtain ⟨xs, hn, hall, hok, hc, hΓ⟩ := Γ.value_spec
  obtain ⟨ys, hn', hall', hok', hc', hΔ⟩ := Δ.value_spec
  set X := Γ.glue Δ h
  have mL := isMap_glueL Γ Δ h
  have mR := isMap_glueR Γ Δ h
  have hV := Γ.vdata_good
  have hV' := Δ.vdata_good
  have hVX := X.vdata_good
  have hdX : X.dom = Γ.dom.map Sum.inl := rfl
  have hcX : X.cod = Δ.cod.map (PEmb.gIn h) := rfl
  have hgl : Γ.cod.map Sum.inl = Δ.dom.map (PEmb.gIn h) := (PEmb.dom_map_gIn Γ Δ h).symm
  have hw₁ : X.vdata.wend X.dom (xs.map Sum.inl) = (Γ.vdata.wend Γ.dom xs).map Sum.inl := by
    rw [hdX]; exact mL.wend _ _
  have hp₁ : ((Γ.vdata.wend Γ.dom xs).map Sum.inl).Perm (Δ.dom.map (PEmb.gIn h)) := by
    rw [← hgl]; exact List.Perm.map _ hc
  have ok₁ : X.vdata.Ok X.dom (xs.map Sum.inl) := by rw [hdX]; exact mL.ok hok
  have ok₂' : X.vdata.Ok (Δ.dom.map (PEmb.gIn h)) (ys.map Sum.inr) := mR.ok hok'
  have ok₂ : X.vdata.Ok ((Γ.vdata.wend Γ.dom xs).map Sum.inl) (ys.map Sum.inr) :=
    X.vdata.ok_of_perm ok₂' hp₁.symm
  have okX : X.vdata.Ok X.dom (xs.map Sum.inl ++ ys.map Sum.inr) :=
    (VData.ok_append _).2 ⟨ok₁, by rw [hw₁]; exact ok₂⟩
  have hc₂ : (X.vdata.wend (Δ.dom.map (PEmb.gIn h)) (ys.map Sum.inr)).Perm X.cod := by
    rw [mR.wend, hcX]; exact List.Perm.map _ hc'
  have hc₁ : (X.vdata.wend ((Γ.vdata.wend Γ.dom xs).map Sum.inl) (ys.map Sum.inr)).Perm X.cod :=
    (X.vdata.wend_perm hp₁ _).trans hc₂
  have hcX' : (X.vdata.wend X.dom (xs.map Sum.inl ++ ys.map Sum.inr)).Perm X.cod := by
    rw [VData.wend_append, hw₁]; exact hc₁
  rw [X.value_eq (List.nodup_append.2 ⟨List.Nodup.map Sum.inl_injective hn,
      List.Nodup.map Sum.inr_injective hn', by simp⟩)
    (by rintro (x | y) <;> simp [hall, hall']) okX, X.vdata.val_append hVX okX hcX', hw₁,
    hdX, mL.steps, X.vdata.val_perm hVX ok₂ hp₁ hc₁, hcX, mR.val, ← hgl, perm_map _ _ mL.inj,
    mL.lab_comp, ← AArr.comp_assoc, hΓ, hΔ]
  · rfl
  all_goals
    have hobj : obj Γ.vdata.lab Γ.cod = obj Δ.vdata.lab Δ.dom := by
      rw [obj_vdata, obj_vdata]; exact h
    simp [Γ.vdata.steps_right hV hok, perm_left _ hc, perm_right _ hc,
      Δ.vdata.val_left hV' hok', hobj]

end Glue

end Diagram

namespace DClass

open Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

theorem value_tensor (c d : DClass G) : (c.tensor d).value = AArr.tensor c.value d.value := by
  induction c using ind with
  | h _ _ Γ => induction d using ind with
    | h _ _ Δ => rw [mk_tensor, value_mk, value_mk, value_mk, Diagram.value_tensor]

theorem value_comp {c d : DClass G} (h : c.cod = d.dom) :
    (c.comp d).value = AArr.comp c.value d.value := by
  induction c using ind with
  | h _ _ Γ => induction d using ind with
    | h _ _ Δ =>
      simp only [cod_mk, dom_mk] at h
      rw [mk_comp _ _ h, value_mk, value_mk, value_mk, Diagram.value_glue]

end DClass

namespace FsC

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-- **The value of the class of a formal composite is that composite**: the value is a left
inverse of the comparison map `Syn_s(G) → F_s(G)`. -/
theorem value_toDHom {a b : FreeMonoid S} (f : Syn.of G a ⟶ Syn.of G b) :
    (toDHom f).1.value = Arrow.mk f := by
  refine Syn.induction (P := fun {a b} f => (toDHom (a := a) (b := b) f).1.value = Arrow.mk f)
    ?_ ?_ ?_ ?_ ?_ f
  · intro x
    exact (congrArg (fun t : DHom G _ _ => t.1.value) (toDHom_gen x)).trans
      ((DClass.value_mk _).trans (Diagram.value_oneNode x))
  · intro a
    exact (congrArg (fun t : DHom G _ _ => t.1.value) (toDHom_id (G := G) a)).trans
      ((DClass.value_mk _).trans (Diagram.value_idD a))
  · intro a b
    exact (congrArg (fun t : DHom G _ _ => t.1.value) (toDHom_braid (G := G) a b)).trans
      ((DClass.value_mk _).trans (Diagram.value_braidD a b))
  · intro a b c f g hf hg
    refine (congrArg (fun t : DHom G _ _ => t.1.value) (toDHom_comp f g)).trans ?_
    refine (DClass.value_comp ((toDHom f).2.2.trans (toDHom g).2.1.symm)).trans ?_
    rw [hf, hg]
    exact AArr.comp_mk f g
  · intro a b c d f g hf hg
    refine (congrArg (fun t : DHom G _ _ => t.1.value) (toDHom_tensor f g)).trans ?_
    refine (DClass.value_tensor _ _).trans ?_
    rw [hf, hg]
    rfl

/-- The comparison map `Syn_s(G)(a, b) → {[Γ, v] : dom = a, cod = b}` is injective. -/
theorem toDHom_injective {a b : FreeMonoid S} :
    Function.Injective (toDHom (G := G) (a := a) (b := b)) := fun f g hfg =>
  Arrow.eq_of_mk_eq ((value_toDHom f).symm.trans ((congrArg (fun t => t.1.value) hfg).trans
    (value_toDHom g)))

end FsC

end FreeMarkov
