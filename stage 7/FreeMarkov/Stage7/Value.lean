/-
Free Markov categories, Stage 7: the value of a diagram in `Syn_s(G)`, and its independence of
all choices (Joyal–Street, Proposition 2.1 and the invariance under isomorphism in Theorem 2.2,
for the combinatorial diagrams of Stage 1).

For a diagram `Γ`, `Γ.vdata` is its incidence data with values in `Syn_s(G)` (edges labelled by
one-letter words, nodes by generators).  A *processing order* is a list of all nodes in which
every node comes after the nodes its inputs come from; `exists_order` constructs one by taking
minimal nodes (a chain of levels with one node per step).  `Diagram.value Γ` is the value
computed along a processing order; by `Wires.VData.val_indep` it does not depend on the order
(`value_eq`), and by renaming (`Wires.VData.IsMap.val`) it is invariant under isomorphism
(`value_eq_of_iso`).  Hence it is defined on classes, `DClass.value`.
-/
module

public import FreeMarkov.Stage7.Steps2
public import FreeMarkov.Stage7.FsCat

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open CategoryTheory StrictSMC FreeGraphMonoid Wires

open scoped Classical

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

/-- The incidence data of a diagram, with values in `Syn_s(G)`. -/
def vdata (Γ : Diagram G N E) : VData G.Syn N E where
  ins := Γ.ins
  outs := Γ.outs
  lab e := Syn.of G (FreeMonoid.of (Γ.val.v₀ e))
  gen x := Arrow.mk (Syn.gen (Γ.val.v₁ x))

theorem obj_vdata (Γ : Diagram G N E) (l : List E) :
    obj Γ.vdata.lab l = FreeMonoid.ofList (l.map Γ.val.v₀) := by
  induction l with
  | nil => rfl
  | cons e l ih => rw [obj_cons, ih]; rfl

theorem vdata_good (Γ : Diagram G N E) : Γ.vdata.Good where
  gen_left x := by
    show G.s (Γ.val.v₁ x) = _
    rw [Γ.val.s_v₁, obj_vdata]; rfl
  gen_right x := by
    show G.t (Γ.val.v₁ x) = _
    rw [Γ.val.t_v₁, obj_vdata]; rfl
  ins_nodup x := Γ.ins_nodup x
  outs_nodup x := Γ.outs_nodup x
  ins_disj {x y} hxy e hx hy := by
    have h₁ := (Γ.mem_ins x e).1 hx
    have h₂ := (Γ.mem_ins y e).1 hy
    exact hxy (Option.some.inj (h₁.symm.trans h₂))
  outs_disj {x y} hxy e hx hy := by
    have h₁ := (Γ.mem_outs x e).1 hx
    have h₂ := (Γ.mem_outs y e).1 hy
    exact hxy (Option.some.inj (h₁.symm.trans h₂))

/-! ### Processing orders -/

/-- The edges crossing the cut below the set `R` of nodes still to be processed. -/
def InCut (Γ : Diagram G N E) (R : Finset N) (e : E) : Prop :=
  (∀ x, Γ.src e = some x → x ∉ R) ∧ (∀ y, Γ.tgt e = some y → y ∈ R)

theorem exists_order_aux (Γ : Diagram G N E) [Finite N] :
    ∀ (n : ℕ) (R : Finset N), R.card = n → ∀ W : List E, W.Nodup → (∀ e, e ∈ W ↔ Γ.InCut R e) →
      (∀ x y, x ∈ R → Γ.Adj x y → y ∈ R) →
      ∃ xs : List N, xs.Nodup ∧ (∀ x, x ∈ xs ↔ x ∈ R) ∧ Γ.vdata.Ok W xs ∧
        (Γ.vdata.wend W xs).Perm Γ.cod := by
  intro n
  induction n with
  | zero =>
    intro R hR W hW hWc _
    rw [Finset.card_eq_zero] at hR
    subst hR
    refine ⟨[], List.nodup_nil, by simp, hW, ?_⟩
    refine (List.perm_ext_iff_of_nodup hW Γ.cod_nodup).2 fun e => ?_
    rw [hWc, Γ.mem_cod]
    constructor
    · rintro ⟨-, h⟩
      cases ht : Γ.tgt e with
      | none => rfl
      | some y => exact absurd (h y ht) (Finset.notMem_empty y)
    · intro h
      refine ⟨fun x _ => Finset.notMem_empty x, fun y hy => ?_⟩
      rw [h] at hy; cases hy
  | succ n ih =>
    intro R hR W hW hWc hup
    have hne : R.Nonempty := Finset.card_pos.1 (by omega)
    have : IsTrans N Γ.Lt := ⟨fun _ _ _ => Γ.lt_trans⟩
    have : Std.Irrefl Γ.Lt := ⟨Γ.lt_irrefl⟩
    have wf := Finite.wellFounded_of_trans_of_irrefl Γ.Lt
    obtain ⟨x, hxR, hmin⟩ := wf.has_min (R : Set N) hne
    have hmin' : ∀ z ∈ R, ¬ Γ.Lt z x := fun z hz => hmin z hz
    have hV := Γ.vdata_good
    have hI : ∀ e ∈ Γ.vdata.ins x, e ∈ W := by
      intro e he
      have ht : Γ.tgt e = some x := (Γ.mem_ins x e).1 he
      refine (hWc e).2 ⟨fun z hz hzR => hmin' z hzR (Γ.lt_of_edge hz ht), fun y hy => ?_⟩
      rw [ht] at hy; cases hy; exact hxR
    have hO : ∀ e ∈ Γ.vdata.outs x, e ∉ W := by
      intro e he heW
      exact ((hWc e).1 heW).1 x ((Γ.mem_outs x e).1 he) hxR
    have hWc' : ∀ e, e ∈ Γ.vdata.next W x ↔ Γ.InCut (R.erase x) e := by
      intro e
      rw [VData.mem_next]
      constructor
      · rintro (he | ⟨heW, hex⟩)
        · have hs : Γ.src e = some x := (Γ.mem_outs x e).1 he
          refine ⟨fun z hz => ?_, fun y hy => ?_⟩
          · rw [hs] at hz; cases hz; simp
          · have hxy : Γ.Adj x y := ⟨e, hs, hy⟩
            refine Finset.mem_erase.2 ⟨fun h => ?_, hup x y hxR hxy⟩
            subst h; exact Γ.lt_irrefl _ (Relation.TransGen.single hxy)
        · obtain ⟨h₁, h₂⟩ := (hWc e).1 heW
          refine ⟨fun z hz hz' => h₁ z hz (Finset.mem_of_mem_erase hz'), fun y hy => ?_⟩
          refine Finset.mem_erase.2 ⟨fun h => ?_, h₂ y hy⟩
          subst h; exact hex ((Γ.mem_ins _ e).2 hy)
      · rintro ⟨h₁, h₂⟩
        by_cases hs : Γ.src e = some x
        · exact Or.inl ((Γ.mem_outs x e).2 hs)
        · right
          refine ⟨(hWc e).2 ⟨fun z hz hzR => ?_, fun y hy => Finset.mem_of_mem_erase (h₂ y hy)⟩,
            fun hex => ?_⟩
          · have hzx : z ≠ x := fun h => hs (h ▸ hz)
            exact h₁ z hz (Finset.mem_erase.2 ⟨hzx, hzR⟩)
          · have := h₂ x ((Γ.mem_ins x e).1 hex)
            simp at this
    have hup' : ∀ a b, a ∈ R.erase x → Γ.Adj a b → b ∈ R.erase x := by
      intro a b ha hab
      refine Finset.mem_erase.2 ⟨fun h => ?_, hup a b (Finset.mem_of_mem_erase ha) hab⟩
      subst h
      exact hmin' a (Finset.mem_of_mem_erase ha) (Relation.TransGen.single hab)
    obtain ⟨xs, hn, hmem, hok, hc⟩ := ih (R.erase x) (by rw [Finset.card_erase_of_mem hxR]; omega)
      (Γ.vdata.next W x) (Γ.vdata.next_nodup hV hW hO) hWc' hup'
    refine ⟨x :: xs, List.nodup_cons.2 ⟨fun h => by simpa using (hmem x).1 h, hn⟩, fun y => ?_,
      ⟨hW, hI, hO, hok⟩, hc⟩
    rw [List.mem_cons, hmem]
    constructor
    · rintro (rfl | h)
      · exact hxR
      · exact Finset.mem_of_mem_erase h
    · intro h
      by_cases hy : y = x
      · exact Or.inl hy
      · exact Or.inr (Finset.mem_erase.2 ⟨hy, h⟩)

/-- A processing order exists (a chain of levels with one node per step). -/
theorem exists_order (Γ : Diagram G N E) [Fintype N] :
    ∃ xs : List N, xs.Nodup ∧ (∀ x, x ∈ xs) ∧ Γ.vdata.Ok Γ.dom xs ∧
      (Γ.vdata.wend Γ.dom xs).Perm Γ.cod := by
  obtain ⟨xs, hn, hmem, hok, hc⟩ := Γ.exists_order_aux _ Finset.univ rfl Γ.dom Γ.dom_nodup
    (fun e => by
      rw [Γ.mem_dom]
      constructor
      · intro h
        exact ⟨fun x hx => (by rw [h] at hx; cases hx), fun y _ => Finset.mem_univ y⟩
      · rintro ⟨h, -⟩
        cases hs : Γ.src e with
        | none => rfl
        | some x => exact absurd (Finset.mem_univ x) (h x hs))
    (fun _ _ _ _ => Finset.mem_univ _)
  exact ⟨xs, hn, fun x => (hmem x).2 (Finset.mem_univ x), hok, hc⟩

/-! ### The value -/

/-- **The value of a diagram** in `Syn_s(G)`, computed along a processing order. -/
noncomputable def value (Γ : Diagram G N E) [Fintype N] : Arrow G.Syn :=
  Γ.vdata.val Γ.dom (Classical.choose Γ.exists_order) Γ.cod

/-- The value does not depend on the processing order. -/
theorem value_eq (Γ : Diagram G N E) [Fintype N] {xs : List N} (hn : xs.Nodup)
    (hall : ∀ x, x ∈ xs) (hok : Γ.vdata.Ok Γ.dom xs) :
    Γ.value = Γ.vdata.val Γ.dom xs Γ.cod := by
  obtain ⟨hn', hall', hok', hc'⟩ := Classical.choose_spec Γ.exists_order
  have hp : (Classical.choose Γ.exists_order).Perm xs :=
    (List.perm_ext_iff_of_nodup hn' hn).2 fun x => iff_of_true (hall' x) (hall x)
  exact ((Γ.vdata.val_indep Γ.vdata_good hn' hp hok' hok).2 Γ.cod hc')

theorem value_spec (Γ : Diagram G N E) [Fintype N] : ∃ xs : List N, xs.Nodup ∧ (∀ x, x ∈ xs) ∧
    Γ.vdata.Ok Γ.dom xs ∧ (Γ.vdata.wend Γ.dom xs).Perm Γ.cod ∧
    Γ.value = Γ.vdata.val Γ.dom xs Γ.cod :=
  let h := Classical.choose_spec Γ.exists_order
  ⟨_, h.1, h.2.1, h.2.2.1, h.2.2.2, rfl⟩

theorem value_left (Γ : Diagram G N E) [Fintype N] : Γ.value.left = Syn.of G Γ.domWord := by
  obtain ⟨xs, -, -, hok, -, h⟩ := Γ.value_spec
  rw [h, VData.val_left _ Γ.vdata_good hok, obj_vdata]; rfl

theorem value_right (Γ : Diagram G N E) [Fintype N] : Γ.value.right = Syn.of G Γ.codWord := by
  obtain ⟨xs, -, -, hok, hc, h⟩ := Γ.value_spec
  rw [h, VData.val_right _ Γ.vdata_good hok hc, obj_vdata]; rfl

variable {N' : Type u₃} {E' : Type u₄}

theorem isMap_of_iso {Γ : Diagram G N E} {Γ' : Diagram G N' E'} (i : Γ.Iso Γ') :
    VData.IsMap Γ.vdata Γ'.vdata (⇑i.eE) (⇑i.eN) where
  inj := i.eE.injective
  ins x := i.ins_map x
  outs x := i.outs_map x
  lab e := by simp only [vdata, i.v₀_map]
  gen x := congrArg (fun a => Arrow.mk (Syn.gen a)) (i.v₁_map x)

/-- **The value is invariant under isomorphism.** -/
theorem value_eq_of_iso {Γ : Diagram G N E} {Γ' : Diagram G N' E'} [Fintype N] [Fintype N']
    (i : Γ.Iso Γ') : Γ'.value = Γ.value := by
  obtain ⟨xs, hn, hall, hok, -, h⟩ := Γ.value_spec
  have hm := isMap_of_iso i
  have hok' : Γ'.vdata.Ok Γ'.dom (xs.map i.eN) := by rw [i.dom_map]; exact hm.ok hok
  rw [Γ'.value_eq (List.Nodup.map i.eN.injective hn) (fun x => List.mem_map.2
    ⟨i.eN.symm x, hall _, by simp⟩) hok', i.dom_map, i.cod_map, hm.val, h]

end Diagram

namespace DClass

open Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-- **The value of a class of diagrams** in `Syn_s(G)`. -/
noncomputable def value (c : DClass G) : Arrow G.Syn :=
  Quotient.lift (fun Γ : FinDiag G => Γ.2.value)
    (fun _ _ h => (show Nonempty (Iso _ _) from h).elim fun i => (value_eq_of_iso i).symm) c

theorem value_mk {N : Type u₁} {E : Type u₂} (Γ : Diagram G N E) [Fintype N] [Finite E] :
    (mk Γ).value = Γ.value :=
  value_eq_of_iso Γ.isoToFin

theorem value_left (c : DClass G) : c.value.left = Syn.of G c.dom := by
  induction c using ind with
  | h n m Γ => rw [value_mk, Diagram.value_left, dom_mk]

theorem value_right (c : DClass G) : c.value.right = Syn.of G c.cod := by
  induction c using ind with
  | h n m Γ => rw [value_mk, Diagram.value_right, cod_mk]

end DClass

end FreeMarkov
