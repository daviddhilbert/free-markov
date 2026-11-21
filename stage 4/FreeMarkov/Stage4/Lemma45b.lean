/-
Free Markov categories, Stage 4: subwords (for the words `a''`, `a'` of Lemma 4.5).

* `subword l P`: the letters of `l` at the positions satisfying `P`, in order; `subword_eq`,
  `subword_eq_filter`, `filter_map_eq_subword` relate it to filters.

The words `liveW`, `deadW` and the symmetry `τ` are in `Lemma45c.lean`.
-/
module

public import FreeMarkov.Stage4.Lemma45a

@[expose] public section

universe w v u₁ u₂

namespace FreeMarkov

open Relation

open scoped Classical

section Subword

variable {α : Type*} {β : Type*}

/-- The elements of `l` at the positions satisfying `P`, in order. -/
noncomputable def subword (l : List α) (P : ℕ → Prop) : List α :=
  (l.zipIdx.filter fun p => decide (P p.2)).map Prod.fst

theorem zipIdx_eq_map_finRange (l : List α) :
    l.zipIdx = (List.finRange l.length).map fun i => (l[i], i.1) := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp [List.getElem_zipIdx]

theorem subword_eq (l : List α) (P : ℕ → Prop) :
    subword l P = ((List.finRange l.length).filter fun i => decide (P i.1)).map fun i => l[i] := by
  unfold subword
  rw [zipIdx_eq_map_finRange, List.filter_map, List.map_map]
  rfl

theorem subword_eq_filter (l : List α) (Q : α → Prop) (P : ℕ → Prop)
    (hP : ∀ (j : ℕ) (hj : j < l.length), P j ↔ Q l[j]) :
    subword l P = l.filter fun x => decide (Q x) := by
  rw [subword_eq]
  conv_rhs => rw [← List.map_getElem_finRange l]
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun i _ => ?_
  simp [hP i.1 i.2]

theorem subword_map (l : List α) (f : α → β) (P : ℕ → Prop) :
    subword (l.map f) P = (subword l P).map f := by
  unfold subword
  rw [List.zipIdx_map, List.filter_map, List.map_map, List.map_map]
  rfl

/-- Filtering a list by a property of its elements is taking the subword at the positions of the
elements with the property. -/
theorem filter_map_eq_subword (l : List α) (f : α → β) (Q : α → Prop) (P : ℕ → Prop)
    (hP : ∀ (j : ℕ) (hj : j < l.length), P j ↔ Q l[j]) :
    (l.filter fun x => decide (Q x)).map f = subword (l.map f) P := by
  rw [subword_map, subword_eq_filter l Q P hP]

end Subword

end FreeMarkov
