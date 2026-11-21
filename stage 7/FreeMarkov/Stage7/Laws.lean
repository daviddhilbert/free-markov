/-
Free Markov categories, Stage 7: the laws of `F_s(G)` on isomorphism classes of diagrams,
without the cited result C1 (first item of Stage 7).

Gluing is associative and unital with the node-free identity diagrams, disjoint union is
associative and unital, the interchange law holds, and the node-free symmetry diagrams are
natural, involutive and satisfy the hexagon.  Each law is one embedding of the diagram on one
side into the diagram on the other (`PEmb`, Stage 4), checked to be an isomorphism by counting
nodes and edges (`PEmb.mk_eq`).
-/
module

public import FreeMarkov.Stage7.Embedding

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

theorem dom_length {N : Type u₁} {E : Type u₂} (Γ : Diagram G N E) :
    Γ.dom.length = wlen Γ.domWord := by
  simp [domWord, wlen]

theorem cod_length {N : Type u₁} {E : Type u₂} (Γ : Diagram G N E) :
    Γ.cod.length = wlen Γ.codWord := by
  simp [codWord, wlen]

theorem wlen_mul (a b : FreeMonoid S) : wlen (a * b) = wlen a + wlen b := by
  simp [wlen]

@[simp] theorem wlen_one : wlen (1 : FreeMonoid S) = 0 := rfl

theorem toList_eq_map_v₀_dom {N : Type u₁} {E : Type u₂} (Γ : Diagram G N E) {a : FreeMonoid S}
    (h : Γ.domWord = a) : Γ.dom.map Γ.val.v₀ = FreeMonoid.toList a := by
  rw [← h]; rfl

theorem toList_eq_map_v₀_cod {N : Type u₁} {E : Type u₂} (Γ : Diagram G N E) {a : FreeMonoid S}
    (h : Γ.codWord = a) : Γ.cod.map Γ.val.v₀ = FreeMonoid.toList a := by
  rw [← h]; rfl

/-- The first `wlen a` positions of the word `a * b`. -/
def posL (a b : FreeMonoid S) : List (Fin (wlen (a * b))) :=
  (List.finRange (wlen (a * b))).take (wlen a)

/-- The last `wlen b` positions of the word `a * b`. -/
def posR (a b : FreeMonoid S) : List (Fin (wlen (a * b))) :=
  (List.finRange (wlen (a * b))).drop (wlen a)

theorem posL_append_posR (a b : FreeMonoid S) :
    posL a b ++ posR a b = List.finRange (wlen (a * b)) := List.take_append_drop _ _

theorem nodup_posL_append_posR (a b : FreeMonoid S) : (posL a b ++ posR a b).Nodup := by
  rw [posL_append_posR]; exact List.nodup_finRange _

theorem map_letters_finRange (a : FreeMonoid S) :
    (List.finRange (wlen a)).map (letters a) = FreeMonoid.toList a :=
  List.map_getElem_finRange _

theorem posL_map (a b : FreeMonoid S) : (posL a b).map (letters (a * b)) = FreeMonoid.toList a := by
  rw [posL, List.map_take, map_letters_finRange]
  simp [wlen]

theorem posR_map (a b : FreeMonoid S) : (posR a b).map (letters (a * b)) = FreeMonoid.toList b := by
  rw [posR, List.map_drop, map_letters_finRange]
  simp [wlen]

theorem posL_map_idD (a b : FreeMonoid S) :
    (posL a b).map (idD G (a * b)).val.v₀ = FreeMonoid.toList a := posL_map a b

theorem posR_map_idD (a b : FreeMonoid S) :
    (posR a b).map (idD G (a * b)).val.v₀ = FreeMonoid.toList b := posR_map a b

end Diagram

namespace DClass

open Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-! ### Associativity and units of gluing -/

section Assoc

variable {N₁ : Type u₁} {E₁ : Type u₂} {N₂ : Type u₃} {E₂ : Type u₄} {N₃ : Type u₅} {E₃ : Type u₆}
  [Finite N₁] [Finite E₁] [Finite N₂] [Finite E₂] [Finite N₃] [Finite E₃]

theorem mk_glue_assoc (Γ : Diagram G N₁ E₁) (Δ : Diagram G N₂ E₂) (Ε : Diagram G N₃ E₃)
    (h₁ : Γ.codWord = Δ.domWord) (h₂ : Δ.codWord = Ε.domWord) :
    mk ((Γ.glue Δ h₁).glue Ε (by rw [glue_codWord]; exact h₂)) =
      mk (Γ.glue (Δ.glue Ε h₂) (by rw [glue_domWord]; exact h₁)) := by
  have h₁' : Γ.codWord = (Δ.glue Ε h₂).domWord := by rw [glue_domWord]; exact h₁
  have h₂' : (Γ.glue Δ h₁).codWord = Ε.domWord := by rw [glue_codWord]; exact h₂
  set X := Γ.glue (Δ.glue Ε h₂) h₁'
  let eΓ : PEmb Γ X := PEmb.glueL _ _ h₁'
  let eΔ : PEmb Δ X := (PEmb.glueL Δ Ε h₂).comp (PEmb.glueR _ _ h₁')
  let eΕ : PEmb Ε X := (PEmb.glueR Δ Ε h₂).comp (PEmb.glueR _ _ h₁')
  have hc₁ : Γ.cod.map eΓ.ιE = Δ.dom.map eΔ.ιE := by
    have := PEmb.dom_map_gIn Γ (Δ.glue Ε h₂) h₁'
    simp only [eΓ, eΔ, PEmb.comp, PEmb.glueL, PEmb.glueR] at this ⊢
    rw [← this, ← List.map_map]
    rfl
  have hdom₁ : ∀ d, Γ.src d = none → ∀ z, X.src (eΓ.ιE d) ≠ some (eΔ.ιN z) := by
    intro d hd z
    simp [X, eΓ, eΔ, PEmb.comp, PEmb.glueL, PEmb.glueR, Diagram.glue, AGraph.glue, hd]
  let e₁ := PEmb.glueS eΓ eΔ h₁ hc₁ (fun _ _ => Sum.inl_ne_inr) hdom₁
  have hc₂ : (Γ.glue Δ h₁).cod.map e₁.ιE = Ε.dom.map eΕ.ιE := by
    refine (PEmb.glueS_cod eΓ eΔ h₁ hc₁ _ hdom₁).trans ?_
    have := PEmb.dom_map_gIn Δ Ε h₂
    simp only [eΕ, eΔ, PEmb.comp, PEmb.glueL, PEmb.glueR] at this ⊢
    rw [← List.map_map (g := PEmb.gIn h₁') (f := PEmb.gIn h₂), this, List.map_map]
  have hN₂ : ∀ z z', e₁.ιN z ≠ eΕ.ιN z' := by
    rintro (z | z) z' <;> simp [e₁, eΓ, eΔ, eΕ, PEmb.glueS, PEmb.glue, PEmb.comp, PEmb.glueL,
      PEmb.glueR]
  have hdom₂ : ∀ d, (Γ.glue Δ h₁).src d = none → ∀ z, X.src (e₁.ιE d) ≠ some (eΕ.ιN z) := by
    rintro (d | d) hd z
    · simp only [Diagram.glue, AGraph.glue, PGraph.glue_src_inl, Option.map_eq_none_iff] at hd
      simp [X, e₁, eΓ, eΕ, PEmb.glueS, PEmb.glue, PEmb.comp, PEmb.glueL, PEmb.glueR,
        Diagram.glue, AGraph.glue, hd]
    · exact absurd (by simpa [Diagram.glue, AGraph.glue] using hd) d.2
  let e := PEmb.glueS e₁ eΕ h₂' hc₂ hN₂ hdom₂
  refine e.mk_eq ?_ ?_ ?_ ?_
  · simp only [Nat.card_sum]; omega
  · have k₁ := card_glue_edges Γ Δ h₁
    have k₂ := card_glue_edges (Γ.glue Δ h₁) Ε h₂'
    have k₃ := card_glue_edges Δ Ε h₂
    have k₄ := card_glue_edges Γ (Δ.glue Ε h₂) h₁'
    have k₅ : (Δ.glue Ε h₂).dom.length = Δ.dom.length := List.length_map _
    omega
  · exact (PEmb.glueS_dom e₁ eΕ h₂' hc₂ hN₂ hdom₂).trans
      ((PEmb.glueS_dom eΓ eΔ h₁ hc₁ _ hdom₁).trans rfl)
  · refine (PEmb.glueS_cod e₁ eΕ h₂' hc₂ hN₂ hdom₂).trans ?_
    simp only [eΕ, PEmb.comp, PEmb.glueR, X, Diagram.glue, AGraph.glue, List.map_map]

end Assoc

section Units

variable {N : Type u₁} {E : Type u₂} [Finite N] [Finite E]

theorem mk_idD_glue (Γ : Diagram G N E) (h : (idD G Γ.domWord).codWord = Γ.domWord) :
    mk ((idD G Γ.domWord).glue Γ h) = mk Γ := by
  let eI : PEmb (idD G Γ.domWord) Γ :=
    PEmb.idD Γ.domWord Γ.dom Γ.dom_nodup (toList_eq_map_v₀_dom Γ rfl)
  have hc : (idD G Γ.domWord).cod.map eI.ιE = Γ.dom.map (PEmb.refl Γ).ιE := by
    rw [PEmb.idD_cod]; exact (List.map_id _).symm
  let e := PEmb.glueS eI (PEmb.refl Γ) h hc (fun z => z.elim) (fun d _ z => by
    have hd : Γ.src (eI.ιE d) = none := (Γ.mem_dom _).1 (List.getElem_mem _)
    rw [hd]; simp)
  refine e.mk_eq ?_ ?_ ?_ ?_
  · simp
  · have k := card_glue_edges (idD G Γ.domWord) Γ h
    have k' : (idD G Γ.domWord).cod.length = Γ.dom.length := cod_length_eq_dom_length h
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at k ⊢
    have k'' : (idD G Γ.domWord).cod.length = wlen Γ.domWord := by simp [idD, nodeFree]
    omega
  · exact (PEmb.glueS_dom _ _ _ _ _ _).trans (PEmb.idD_dom _ _ _ _)
  · exact (PEmb.glueS_cod _ _ _ _ _ _).trans (List.map_id _)

theorem mk_glue_idD (Γ : Diagram G N E) (h : Γ.codWord = (idD G Γ.codWord).domWord) :
    mk (Γ.glue (idD G Γ.codWord) h) = mk Γ := by
  let eI : PEmb (idD G Γ.codWord) Γ :=
    PEmb.idD Γ.codWord Γ.cod Γ.cod_nodup (toList_eq_map_v₀_cod Γ rfl)
  have hc : Γ.cod.map (PEmb.refl Γ).ιE = (idD G Γ.codWord).dom.map eI.ιE := by
    rw [PEmb.idD_dom]; exact List.map_id _
  let e := PEmb.glueS (PEmb.refl Γ) eI h hc (fun _ z => z.elim) (fun _ _ z => z.elim)
  refine e.mk_eq ?_ ?_ ?_ ?_
  · simp
  · have k := card_glue_edges Γ (idD G Γ.codWord) h
    have k' : Γ.cod.length = (idD G Γ.codWord).dom.length := cod_length_eq_dom_length h
    have k'' : (idD G Γ.codWord).dom.length = wlen Γ.codWord := by simp [idD, nodeFree]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at k ⊢
    omega
  · exact (PEmb.glueS_dom _ _ _ _ _ _).trans (List.map_id _)
  · exact (PEmb.glueS_cod _ _ _ _ _ _).trans (PEmb.idD_cod _ _ _ _)

end Units

/-! ### Disjoint union -/

section Tensor

variable {N₁ : Type u₁} {E₁ : Type u₂} {N₂ : Type u₃} {E₂ : Type u₄} {N₃ : Type u₅} {E₃ : Type u₆}
  [Finite N₁] [Finite E₁] [Finite N₂] [Finite E₂] [Finite N₃] [Finite E₃]

theorem mk_tensor_assoc (Γ : Diagram G N₁ E₁) (Δ : Diagram G N₂ E₂) (Ε : Diagram G N₃ E₃) :
    mk ((Γ.tensor Δ).tensor Ε) = mk (Γ.tensor (Δ.tensor Ε)) := by
  set X := Γ.tensor (Δ.tensor Ε)
  let eΓ : PEmb Γ X := PEmb.tensorL _ _
  let eΔ : PEmb Δ X := (PEmb.tensorL Δ Ε).comp (PEmb.tensorR _ _)
  let eΕ : PEmb Ε X := (PEmb.tensorR Δ Ε).comp (PEmb.tensorR _ _)
  let e₁ := PEmb.tensor eΓ eΔ (fun _ _ => Sum.inl_ne_inr) (fun _ _ => Sum.inl_ne_inr)
  let e := PEmb.tensor e₁ eΕ (by rintro (z | z) z' <;> simp [e₁, eΓ, eΔ, eΕ, PEmb.tensor,
    PEmb.comp, PEmb.tensorL, PEmb.tensorR]) (by rintro (z | z) z' <;> simp [e₁, eΓ, eΔ, eΕ,
    PEmb.tensor, PEmb.comp, PEmb.tensorL, PEmb.tensorR])
  refine e.mk_eq ?_ ?_ ?_ ?_
  · simp only [Nat.card_sum]; omega
  · simp only [Nat.card_sum]; omega
  · refine (PEmb.tensor_dom e₁ eΕ _ _).trans ?_
    have k : (Γ.tensor Δ).dom.map e₁.ιE = Γ.dom.map eΓ.ιE ++ Δ.dom.map eΔ.ιE :=
      PEmb.tensor_dom _ _ _ _
    rw [k]
    simp [X, eΓ, eΔ, eΕ, PEmb.comp, PEmb.tensorL, PEmb.tensorR, Diagram.tensor, AGraph.tensor,
      Function.comp_def]
  · refine (PEmb.tensor_cod e₁ eΕ _ _).trans ?_
    have k : (Γ.tensor Δ).cod.map e₁.ιE = Γ.cod.map eΓ.ιE ++ Δ.cod.map eΔ.ιE :=
      PEmb.tensor_cod _ _ _ _
    rw [k]
    simp [X, eΓ, eΔ, eΕ, PEmb.comp, PEmb.tensorL, PEmb.tensorR, Diagram.tensor, AGraph.tensor,
      Function.comp_def]

theorem mk_idD_one_tensor (Γ : Diagram G N₁ E₁) : mk ((idD G 1).tensor Γ) = mk Γ := by
  let eI : PEmb (idD G 1) Γ := PEmb.idD 1 [] List.nodup_nil rfl
  let e := PEmb.tensor eI (PEmb.refl Γ) (fun z => z.elim) (fun i => i.elim0)
  refine e.mk_eq ?_ ?_ ?_ ?_
  · simp
  · simp
  · refine (PEmb.tensor_dom _ _ _ _).trans ?_
    have k : (idD G 1).dom.map eI.ιE = [] := PEmb.idD_dom _ _ _ _
    rw [k]; exact List.map_id _
  · refine (PEmb.tensor_cod _ _ _ _).trans ?_
    have k : (idD G 1).cod.map eI.ιE = [] := PEmb.idD_cod _ _ _ _
    rw [k]; exact List.map_id _

theorem mk_tensor_idD_one (Γ : Diagram G N₁ E₁) : mk (Γ.tensor (idD G 1)) = mk Γ := by
  let eI : PEmb (idD G 1) Γ := PEmb.idD 1 [] List.nodup_nil rfl
  let e := PEmb.tensor (PEmb.refl Γ) eI (fun _ z => z.elim) (fun _ i => i.elim0)
  refine e.mk_eq ?_ ?_ ?_ ?_
  · simp
  · simp
  · refine (PEmb.tensor_dom _ _ _ _).trans ?_
    have k : (idD G 1).dom.map eI.ιE = [] := PEmb.idD_dom _ _ _ _
    rw [k, List.append_nil]; exact List.map_id _
  · refine (PEmb.tensor_cod _ _ _ _).trans ?_
    have k : (idD G 1).cod.map eI.ιE = [] := PEmb.idD_cod _ _ _ _
    rw [k, List.append_nil]; exact List.map_id _

theorem mk_idD_tensor_idD (a c : FreeMonoid S) :
    mk ((idD G a).tensor (idD G c)) = mk (idD G (a * c)) := by
  have hl := nodup_posL_append_posR a c
  let e := PEmb.tensor (X := idD G (a * c)) (PEmb.idD a (posL a c) (List.nodup_append.1 hl).1
      (posL_map_idD a c)) (PEmb.idD c (posR a c) (List.nodup_append.1 hl).2.1 (posR_map_idD a c))
    (fun z => z.elim) (fun i j h => (List.nodup_append.1 hl).2.2 _ (List.getElem_mem _) _
      (List.getElem_mem _) h)
  refine e.mk_eq ?_ ?_ ?_ ?_
  · simp
  · simp [wlen_mul]
  · refine (PEmb.tensor_dom _ _ _ _).trans ?_
    rw [PEmb.idD_dom, PEmb.idD_dom, posL_append_posR]; rfl
  · refine (PEmb.tensor_cod _ _ _ _).trans ?_
    rw [PEmb.idD_cod, PEmb.idD_cod, posL_append_posR]; rfl

end Tensor

/-! ### The symmetry -/

theorem mk_braid_braid (a b : FreeMonoid S)
    (h : (braidD G a b).codWord = (braidD G b a).domWord) :
    mk ((braidD G a b).glue (braidD G b a) h) = mk (idD G (a * b)) := by
  have hl := nodup_posL_append_posR a b
  have hl' : (posR a b ++ posL a b).Nodup := List.nodup_append_comm.1 hl
  let e₁ : PEmb (braidD G a b) (idD G (a * b)) :=
    PEmb.braidD a b (posL a b) (posR a b) hl (posL_map_idD a b) (posR_map_idD a b)
  let e₂ : PEmb (braidD G b a) (idD G (a * b)) :=
    PEmb.braidD b a (posR a b) (posL a b) hl' (posR_map_idD a b) (posL_map_idD a b)
  have k₁ : (braidD G a b).cod.map e₁.ιE = posR a b ++ posL a b := PEmb.braidD_cod _ _ _ _ _ _ _
  have k₂ : (braidD G b a).dom.map e₂.ιE = posR a b ++ posL a b := PEmb.braidD_dom _ _ _ _ _ _ _
  have k₃ : (braidD G a b).dom.map e₁.ιE = posL a b ++ posR a b := PEmb.braidD_dom _ _ _ _ _ _ _
  have k₄ : (braidD G b a).cod.map e₂.ιE = posL a b ++ posR a b := PEmb.braidD_cod _ _ _ _ _ _ _
  have hc : (braidD G a b).cod.map e₁.ιE = (braidD G b a).dom.map e₂.ιE := by
    rw [k₁, k₂]
  let e := PEmb.glueS e₁ e₂ h hc (fun z => z.elim) (fun _ _ z => z.elim)
  refine e.mk_eq ?_ ?_ ?_ ?_
  · simp
  · have k := card_glue_edges (braidD G a b) (braidD G b a) h
    have k' : (braidD G b a).dom.length = wlen b + wlen a := by
      simp [braidD, nodeFree, braidDom]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_sum] at k ⊢
    rw [wlen_mul]; omega
  · refine (PEmb.glueS_dom _ _ _ _ _ _).trans ?_
    rw [k₃, posL_append_posR]; rfl
  · refine (PEmb.glueS_cod _ _ _ _ _ _).trans ?_
    rw [k₄, posL_append_posR]; rfl

end DClass

end FreeMarkov
