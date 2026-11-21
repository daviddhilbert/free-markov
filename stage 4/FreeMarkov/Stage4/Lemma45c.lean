/-
Free Markov categories, Stage 4: the symmetry `τ` of Lemma 4.5 and the diagram of
`(1_{a''} ⊗ ε_{a'}) ∘ τ`.

* `livePos n P`: the positions `< n` outside `P`, in increasing order; `tauPos n P`: the positions
  outside `P` followed by those in `P` (the permutation `τ`).
* `liveW a P`, `deadW a P`: the subwords `a''`, `a'` of `a` at the positions outside, inside `P`.
* `tauTarget a P`: the diagram `1_{a''} ⊗ (ε_{a'_1} ⊗ ⋯ ⊗ ε_{a'_k})`; gluing the node-free diagram
  of `τ` on its left gives `tauTarget a P` with its domain reordered (`tauRe a P`).
* `tauRe_pos`: in `tauRe a P` the `i`-th edge of the codomain is the `j`-th edge of the domain iff
  `j` is the `i`-th position outside `P`.
-/
module

public import FreeMarkov.Stage4.TensorSkel

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

open scoped Classical

/-! ### Positions -/

/-- The positions `< n` outside `P`, in increasing order. -/
noncomputable def livePos (n : ℕ) (P : ℕ → Prop) : List ℕ :=
  ((List.finRange n).filter fun i => @decide (¬ P i.1) (Classical.propDecidable _)).map Fin.val

theorem lt_of_mem_livePos {n : ℕ} {P : ℕ → Prop} {j : ℕ} (h : j ∈ livePos n P) : j < n := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
  exact i.2

theorem livePos_congr {n n' : ℕ} (h : n = n') (P : ℕ → Prop) : livePos n P = livePos n' P := by
  subst h; rfl

/-- In a list without repetition, the `i`-th element of the sublist of the elements with property
`Q` is the `j`-th element of the list iff `j` is the `i`-th position with property `Q`. -/
theorem getElem?_filter_iff {α : Type*} {l : List α} (hl : l.Nodup) (Q : α → Prop) (P : ℕ → Prop)
    (hP : ∀ (k : ℕ) (hk : k < l.length), ¬ P k ↔ Q l[k]) {i : ℕ} {x : α}
    (hx : (l.filter fun y => decide (Q y))[i]? = some x) (j : ℕ) :
    l[j]? = some x ↔ (livePos l.length P)[i]? = some j := by
  have h₁ := subword_eq_filter l Q (fun k => ¬ P k) hP
  rw [subword_eq] at h₁
  rw [← h₁, List.getElem?_map] at hx
  unfold livePos
  rw [List.getElem?_map]
  cases hk : ((List.finRange l.length).filter
      fun i => @decide (¬ P i.1) (Classical.propDecidable _))[i]? with
  | none => rw [hk] at hx; cases hx
  | some k =>
    rw [hk] at hx
    simp only [Option.map_some, Option.some.injEq] at hx ⊢
    subst hx
    constructor
    · intro h
      exact nodup_idx_eq hl (List.getElem?_eq_getElem k.2) h
    · rintro rfl
      exact List.getElem?_eq_getElem k.2

/-- The positions outside `P` followed by those in `P`. -/
noncomputable def tauPos (n : ℕ) (P : ℕ → Prop) : List (Fin n) :=
  (List.finRange n).filter (fun i => @decide (¬ P i.1) (Classical.propDecidable _)) ++
    (List.finRange n).filter (fun i => @decide (P i.1) (Classical.propDecidable _))

theorem tauPos_nodup (n : ℕ) (P : ℕ → Prop) : (tauPos n P).Nodup := by
  refine List.nodup_append.2 ⟨(List.nodup_finRange n).filter _, (List.nodup_finRange n).filter _,
    fun i hi i' hi' h => ?_⟩
  subst h
  simp only [List.mem_filter, decide_eq_true_eq] at hi hi'
  exact hi.2 hi'.2

theorem mem_tauPos (n : ℕ) (P : ℕ → Prop) (i : Fin n) : i ∈ tauPos n P := by
  by_cases h : P i.1 <;> simp [tauPos, h]

theorem length_livePos_le (n : ℕ) (P : ℕ → Prop) : (livePos n P).length ≤ n := by
  unfold livePos
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_finRange).le

theorem tauPos_getElem?_iff {n : ℕ} {P : ℕ → Prop} {i : ℕ} (hi : i < (livePos n P).length) (j : ℕ)
    (hj : j < n) : (tauPos n P)[i]? = some ⟨j, hj⟩ ↔ (livePos n P)[i]? = some j := by
  have hi' : i < ((List.finRange n).filter
      fun i => @decide (¬ P i.1) (Classical.propDecidable _)).length := by
    simpa [livePos] using hi
  unfold tauPos livePos
  rw [List.getElem?_append_left hi', List.getElem?_map]
  cases ((List.finRange n).filter fun i => @decide (¬ P i.1) (Classical.propDecidable _))[i]? with
  | none => simp
  | some k =>
    simp only [Option.map_some, Option.some.injEq]
    exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩

theorem idxOf_eq_iff {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup) {x : α} (hx : x ∈ l)
    (i : ℕ) : l.idxOf x = i ↔ l[i]? = some x := by
  constructor
  · rintro rfl
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hx), List.getElem_idxOf]
  · intro h
    exact nodup_idx_eq hl (by rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hx),
      List.getElem_idxOf]) h

/-! ### The subwords `a''`, `a'` -/

variable {S : Type w}

/-- `a''`: the subword of `a` at the positions outside `P`. -/
noncomputable def liveW (a : FreeMonoid S) (P : ℕ → Prop) : FreeMonoid S :=
  FreeMonoid.ofList (subword (FreeMonoid.toList a) fun j => ¬ P j)

/-- `a'`: the subword of `a` at the positions in `P`. -/
noncomputable def deadW (a : FreeMonoid S) (P : ℕ → Prop) : FreeMonoid S :=
  FreeMonoid.ofList (subword (FreeMonoid.toList a) P)

theorem wlen_liveW (a : FreeMonoid S) (P : ℕ → Prop) :
    Diagram.wlen (liveW a P) = (livePos (Diagram.wlen a) P).length := by
  simp only [Diagram.wlen, liveW, FreeMonoid.toList_ofList, subword_eq, livePos, List.length_map]

theorem liveW_eq_ofList_filter {E : Type*} (l : List E) (v₀ : E → S) (Q : E → Prop) (P : ℕ → Prop)
    (hP : ∀ (j : ℕ) (hj : j < l.length), ¬ P j ↔ Q l[j]) :
    liveW (FreeMonoid.ofList (l.map v₀)) P =
      FreeMonoid.ofList ((l.filter fun e => decide (Q e)).map v₀) := by
  unfold liveW
  rw [FreeMonoid.toList_ofList, filter_map_eq_subword l v₀ Q (fun j => ¬ P j) hP]

namespace Diagram

variable {G : FreeDDGraphMonoid.{w, v} S}

theorem permNF_tauPos_codWord (a : FreeMonoid S) (P : ℕ → Prop) :
    (permNF (G := G) a (tauPos (wlen a) P) (tauPos_nodup _ _) (mem_tauPos _ _)).codWord =
      liveW a P * deadW a P := by
  rw [permNF_codWord, tauPos, List.map_append, liveW, deadW, subword_eq, subword_eq]
  rfl

/-- The diagram `1_{a''} ⊗ (ε_{a'_1} ⊗ ⋯ ⊗ ε_{a'_k})`. -/
noncomputable def tauTarget (a : FreeMonoid S) (P : ℕ → Prop) :=
  (idD G.toFreeGraphMonoid (liveW a P)).tensor (G.discListD (FreeMonoid.toList (deadW a P)))

theorem tauTarget_domWord (a : FreeMonoid S) (P : ℕ → Prop) :
    (tauTarget (G := G) a P).domWord = liveW a P * deadW a P := by
  rw [tauTarget, tensor_domWord, idD_domWord, G.discListD_domWord, FreeMonoid.ofList_toList]

theorem tauTarget_codWord (a : FreeMonoid S) (P : ℕ → Prop) :
    (tauTarget (G := G) a P).codWord = liveW a P := by
  rw [tauTarget, tensor_codWord, idD_codWord, G.discListD_codWord, mul_one]

theorem tauHΘ (a : FreeMonoid S) (P : ℕ → Prop) :
    (permNF (G := G) a (tauPos (wlen a) P) (tauPos_nodup _ _) (mem_tauPos _ _)).codWord =
      (tauTarget (G := G) a P).domWord := by
  rw [permNF_tauPos_codWord, tauTarget_domWord]

/-- `tauTarget a P` with its domain reordered by `τ`. -/
noncomputable def tauRe (a : FreeMonoid S) (P : ℕ → Prop) :=
  (tauTarget (G := G) a P).reanchor (reorder _ (tauHΘ a P)) (reorder_perm (tauHΘ a P))

theorem discListD_cod (l : List S) : (G.discListD l).cod = [] := by
  have h := G.discListD_codWord l
  have h' : (G.discListD l).cod.map (G.discListD l).val.v₀ = [] := FreeMonoid.ofList.injective h
  exact List.map_eq_nil_iff.1 h'

theorem finRange_getElem?_eq_some {n m : ℕ} {i : Fin n} : (List.finRange n)[m]? = some i ↔ m = i.1 := by
  by_cases hm : m < n
  · rw [List.getElem?_eq_getElem (by simpa using hm), Option.some.injEq, List.getElem_finRange]
    exact ⟨fun h => by rw [← h]; rfl, fun h => Fin.ext (by simp [h])⟩
  · rw [List.getElem?_eq_none (by simpa using hm)]
    simp only [reduceCtorEq, false_iff]
    intro h
    exact hm (h ▸ i.2)

theorem tauTarget_cod_getElem? (a : FreeMonoid S) (P : ℕ → Prop) {i : ℕ} {e}
    (h : (tauTarget (G := G) a P).cod[i]? = some e) :
    ∃ hi : i < wlen (liveW a P), e = .inl ⟨i, hi⟩ := by
  change ((idD G.toFreeGraphMonoid (liveW a P)).cod.map Sum.inl ++
    (G.discListD (FreeMonoid.toList (deadW a P))).cod.map Sum.inr)[i]? = some e at h
  rw [discListD_cod, List.map_nil, List.append_nil, List.getElem?_map] at h
  change ((List.finRange _)[i]?).map Sum.inl = some e at h
  by_cases hi : i < wlen (liveW a P)
  · refine ⟨hi, ?_⟩
    rw [List.getElem?_eq_getElem (by simpa using hi)] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h, List.getElem_finRange]
    rfl
  · rw [List.getElem?_eq_none (by simpa using hi)] at h
    cases h

theorem tauTarget_dom_getElem?_inl (a : FreeMonoid S) (P : ℕ → Prop) (m : ℕ)
    (i : Fin (wlen (liveW a P))) :
    (tauTarget (G := G) a P).dom[m]? = some (.inl i) ↔ m = i.1 := by
  change ((idD G.toFreeGraphMonoid (liveW a P)).dom.map Sum.inl ++
    (G.discListD (FreeMonoid.toList (deadW a P))).dom.map Sum.inr)[m]? = some (.inl i) ↔ _
  rw [List.getElem?_append_map_inl]
  exact finRange_getElem?_eq_some

/-- In `tauRe a P` the `i`-th edge of the codomain is the `j`-th edge of the domain iff `j` is the
`i`-th position outside `P`. -/
theorem tauRe_pos (a : FreeMonoid S) (P : ℕ → Prop) {i : ℕ} {e}
    (he : (tauRe (G := G) a P).cod[i]? = some e) (j : ℕ) :
    (tauRe (G := G) a P).dom[j]? = some e ↔ (livePos (wlen a) P)[i]? = some j := by
  obtain ⟨hi, rfl⟩ := tauTarget_cod_getElem? a P he
  change (reorder _ (tauHΘ a P))[j]? = _ ↔ _
  rw [reorder_getElem?, tauTarget_dom_getElem?_inl]
  have hi' : i < (livePos (wlen a) P).length := wlen_liveW a P ▸ hi
  unfold reorderPos
  split_ifs with hj
  · rw [idxOf_eq_iff (tauPos_nodup _ _) (mem_tauPos _ _ _), tauPos_getElem?_iff hi' j hj]
  · simp only
    constructor
    · rintro rfl
      exact absurd (hi'.trans_le (length_livePos_le _ _)) hj
    · intro h
      exact absurd (lt_of_mem_livePos (List.mem_of_getElem? h)) hj

end Diagram

end FreeMarkov
