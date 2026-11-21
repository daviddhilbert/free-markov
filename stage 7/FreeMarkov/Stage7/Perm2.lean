/-
Free Markov categories, Stage 7: composition of permutations of wires,
`perm d c ∘ perm c c' = perm d c'` (`Wires.perm_comp`), from the two-wire identity `AArr.dm_obj`.
-/
module

public import FreeMarkov.Stage7.Perm

@[expose] public section

universe v u w

namespace FreeMarkov

open CategoryTheory StrictSMC

namespace Wires

open AArr (comp tensor)

variable {C : Type u} [Monoid C] [CategoryTheory.Category.{v} C] [StrictSMC C]
variable {E : Type w} [DecidableEq E] (ℓ : E → C)

theorem mv_cons_ne {f e : E} {c : List E} (hef : e ≠ f) (he : e ∈ c) :
    mv ℓ (f :: c) e = comp (tensor (AArr.id (ℓ f)) (mv ℓ c e))
      (tensor (AArr.braid (ℓ f) (ℓ e)) (AArr.id (obj ℓ (c.erase e)))) := by
  obtain ⟨P, Q, rfl, hP⟩ := split_first he
  have h₀ : f :: (P ++ e :: Q) = (f :: P) ++ e :: Q := rfl
  rw [h₀, mv_eq ℓ (by simp [hP, hef]), mv_eq ℓ hP, erase_eq hP, obj_cons, AArr.hexagon_reverse,
    AArr.tensor_comp_id, AArr.tensor_assoc, AArr.tensor_assoc, AArr.tensor_id, obj_append]
  aobj

/-- The two-wire identity when `e` comes before `f`. -/
theorem dm_split {P B Q : List E} {e f : E} (heP : e ∉ P) (hfP : f ∉ P) (hfB : f ∉ B)
    (hef : e ≠ f) :
    comp (comp (mv ℓ (P ++ e :: (B ++ f :: Q)) f)
        (tensor (AArr.id (ℓ f)) (mv ℓ ((P ++ e :: (B ++ f :: Q)).erase f) e)))
      (tensor (AArr.braid (ℓ f) (ℓ e))
        (AArr.id (obj ℓ (((P ++ e :: (B ++ f :: Q)).erase f).erase e)))) =
    comp (mv ℓ (P ++ e :: (B ++ f :: Q)) e)
      (tensor (AArr.id (ℓ e)) (mv ℓ ((P ++ e :: (B ++ f :: Q)).erase e) f)) := by
  have hf' : f ∉ P ++ e :: B := by simp [hfP, hfB, Ne.symm hef]
  have l₁ : P ++ e :: (B ++ f :: Q) = (P ++ e :: B) ++ f :: Q := by simp
  have l₂ : (P ++ e :: (B ++ f :: Q)).erase f = P ++ e :: (B ++ Q) := by
    rw [l₁, erase_eq hf']; simp
  have l₃ : (P ++ e :: (B ++ Q)).erase e = P ++ (B ++ Q) := erase_eq heP
  have l₄ : (P ++ e :: (B ++ f :: Q)).erase e = (P ++ B) ++ f :: Q := by
    rw [erase_eq heP]; simp
  have m₁ : mv ℓ (P ++ e :: (B ++ f :: Q)) f =
      tensor (AArr.braid (obj ℓ P * (ℓ e * obj ℓ B)) (ℓ f)) (AArr.id (obj ℓ Q)) := by
    rw [l₁, mv_eq ℓ hf']; simp
  have m₂ : mv ℓ (P ++ e :: (B ++ Q)) e =
      tensor (AArr.braid (obj ℓ P) (ℓ e)) (AArr.id (obj ℓ B * obj ℓ Q)) := by
    rw [mv_eq ℓ heP, obj_append]
  have m₃ : mv ℓ (P ++ e :: (B ++ f :: Q)) e =
      tensor (AArr.braid (obj ℓ P) (ℓ e)) (AArr.id (obj ℓ B * (ℓ f * obj ℓ Q))) := by
    rw [mv_eq ℓ heP]; simp
  have m₄ : mv ℓ ((P ++ B) ++ f :: Q) f =
      tensor (AArr.braid (obj ℓ P * obj ℓ B) (ℓ f)) (AArr.id (obj ℓ Q)) := by
    rw [mv_eq ℓ (by simp [hfP, hfB]), obj_append]
  rw [l₂, l₃, l₄, m₁, m₂, m₃, m₄, obj_append, obj_append]
  exact AArr.dm_obj _ _ _ _ _

theorem erase_erase_mem {d : List E} {e f : E} (he : e ∈ d) (hef : e ≠ f) : e ∈ d.erase f :=
  (List.mem_erase_of_ne hef).2 he

/-- The two-wire identity: bringing `f` and then `e` to the front and swapping them is bringing
`e` and then `f` to the front. -/
theorem dm {d : List E} (hd : d.Nodup) {e f : E} (he : e ∈ d) (hf : f ∈ d) (hef : e ≠ f) :
    comp (comp (mv ℓ d f) (tensor (AArr.id (ℓ f)) (mv ℓ (d.erase f) e)))
      (tensor (AArr.braid (ℓ f) (ℓ e)) (AArr.id (obj ℓ ((d.erase f).erase e)))) =
    comp (mv ℓ d e) (tensor (AArr.id (ℓ e)) (mv ℓ (d.erase e) f)) := by
  obtain ⟨P, Q, rfl, hP⟩ := split_first he
  rcases List.mem_append.1 hf with hfP | hfQ
  · -- `f` comes first: use the other case and cancel the swap.
    obtain ⟨A, B, rfl, hA⟩ := split_first hfP
    have heA : e ∉ A := fun h => hP (by simp [h])
    have heB : e ∉ B := fun h => hP (by simp [h])
    have l : A ++ f :: B ++ e :: Q = A ++ f :: (B ++ e :: Q) := by simp
    rw [l] at hd ⊢
    have S := dm_split ℓ (Q := Q) hA heA heB (Ne.symm hef)
    have hR : ((A ++ f :: (B ++ e :: Q)).erase e).erase f =
        ((A ++ f :: (B ++ e :: Q)).erase f).erase e := List.erase_comm _ _
    rw [hR] at S
    rw [← S, AArr.comp_assoc, ← AArr.tensor_comp, AArr.braid_braid, AArr.id_comp, AArr.tensor_id,
      AArr.comp_id]
    all_goals
      simp [mv_left, mv_right, mul_assoc, hef, Ne.symm hef, List.erase_comm]
  · obtain ⟨B, Q', rfl, hB⟩ := split_first ((List.mem_cons.1 hfQ).resolve_left (Ne.symm hef))
    have hfP : f ∉ P := by
      intro h
      have := (List.nodup_append.1 hd).2.2 f h f (by simp) rfl
      exact this
    exact dm_split ℓ hP hfP hB hef

omit [DecidableEq E] in
theorem swap_past {f e : E} (P : Arrow C) (X : C) (h : P.right = X) :
    comp (tensor (AArr.id (ℓ f)) (tensor (AArr.id (ℓ e)) P))
        (tensor (AArr.braid (ℓ f) (ℓ e)) (AArr.id X)) =
      comp (tensor (AArr.braid (ℓ f) (ℓ e)) (AArr.id P.left))
        (tensor (AArr.id (ℓ e)) (tensor (AArr.id (ℓ f)) P)) := by
  rw [← AArr.tensor_assoc, AArr.tensor_id, ← AArr.tensor_assoc, AArr.tensor_id,
    ← AArr.tensor_comp, ← AArr.tensor_comp, AArr.id_comp, AArr.comp_id, AArr.comp_id, AArr.id_comp]
  all_goals simp [h]

/-- Moving a wire to the front after a permutation. -/
theorem kl {d c : List E} (hd : d.Nodup) (h : d.Perm c) {e : E} (he : e ∈ c) :
    comp (perm ℓ d c) (mv ℓ c e) =
      comp (mv ℓ d e) (tensor (AArr.id (ℓ e)) (perm ℓ (d.erase e) (c.erase e))) := by
  induction c generalizing d with
  | nil => simp at he
  | cons f c ih =>
    have hc : (f :: c).Nodup := h.nodup_iff.1 hd
    have hfd : f ∈ d := mem_of_perm h
    have h' : (d.erase f).Perm c := perm_erase h
    by_cases hfe : f = e
    · subst hfe
      rw [mv_self, AArr.comp_id (by rw [perm_right ℓ h]; simp), List.erase_cons_head]
      rfl
    · have hec : e ∈ c := (List.mem_cons.1 he).resolve_left (Ne.symm hfe)
      have hed : e ∈ d := h.symm.subset he
      have hd' : (d.erase f).Nodup := hd.erase f
      have hP' := (h'.erase e)
      have k₁ : (perm ℓ ((d.erase f).erase e) (c.erase e)).right = obj ℓ (c.erase e) :=
        perm_right ℓ hP'
      have k₂ : (perm ℓ ((d.erase f).erase e) (c.erase e)).left = obj ℓ ((d.erase f).erase e) :=
        perm_left ℓ hP'
      have hc2 : (d.erase e).erase f = (d.erase f).erase e := List.erase_comm _ _
      rw [perm_cons, mv_cons_ne ℓ (Ne.symm hfe) hec, AArr.comp_assoc, ← AArr.comp_assoc (f := tensor _ _),
        ← AArr.tensor_id_comp, ih hd' h' hec, AArr.tensor_id_comp, AArr.comp_assoc,
        ← k₁, swap_past ℓ _ _ rfl, k₂, ← AArr.comp_assoc, ← AArr.comp_assoc,
        dm ℓ hd hed hfd (Ne.symm hfe), AArr.comp_assoc, ← AArr.tensor_id_comp, List.erase_cons_tail
          (by simpa using hfe), perm_cons, List.erase_comm]
      all_goals simp [mv_left, mv_right, perm_left ℓ h', perm_right ℓ h', k₁, k₂, mul_assoc,
        hed, hfd, hec, hfe, Ne.symm hfe, hc2]

/-- `perm d c ∘ perm c c' = perm d c'`. -/
theorem perm_comp {d c c' : List E} (hd : d.Nodup) (h : d.Perm c) (h' : c.Perm c') :
    comp (perm ℓ d c) (perm ℓ c c') = perm ℓ d c' := by
  induction c' generalizing d c with
  | nil =>
    rw [List.perm_nil.1 h', List.perm_nil.1 (h.trans h')]
    rw [perm_nil, AArr.comp_id (by simp)]
  | cons e c' ih =>
    have hec : e ∈ c := mem_of_perm h'
    have hc' : (c.erase e).Perm c' := perm_erase h'
    have hdc : (d.erase e).Perm (c.erase e) := h.erase e
    rw [perm_cons ℓ c, ← AArr.comp_assoc, kl ℓ hd h hec, AArr.comp_assoc, ← AArr.tensor_id_comp,
      ih (hd.erase e) hdc hc', perm_cons]
    all_goals simp [mv_left, mv_right, perm_left ℓ hdc, perm_right ℓ hdc, perm_left ℓ hc',
      perm_right ℓ h, hec, h.symm.subset hec]

end Wires

end FreeMarkov
