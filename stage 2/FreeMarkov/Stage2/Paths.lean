/-
Free Markov categories, Stage 2: facts about directed paths used in Section 3.

A directed path `p` is a list of edges in which consecutive edges meet at an inner
node (`PGraph.IsPath`, Stage 1).  The conditions of Definition 3.1 speak about
paths; the proofs of Section 3 only use the order in which two edges occur on a
path.  The relation `Reach e e'` ("`e(1) ≤ e'(0)`") captures it: two distinct edges
lie on a common directed path, `e` before `e'`, exactly when `Reach e e'`
(`reach_of_mem_path`, `exists_path_of_reach`).
-/
module

public import FreeMarkov.Stage1

@[expose] public section

universe u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

namespace PGraph

variable {N : Type u₁} {E : Type u₂} (Γ : PGraph N E)

/-! ### The order on nodes -/

variable {Γ}

theorem le_refl' (x : N) : Γ.Le x x := Or.inr rfl

theorem Le.trans {x y z : N} (h : Γ.Le x y) (h' : Γ.Le y z) : Γ.Le x z := by
  rcases h with h | rfl
  · rcases h' with h' | rfl
    · exact Or.inl (h.trans h')
    · exact Or.inl h
  · exact h'

theorem Le.trans_lt {x y z : N} (h : Γ.Le x y) (h' : Γ.Lt y z) : Γ.Lt x z := by
  rcases h with h | rfl
  · exact h.trans h'
  · exact h'

theorem Lt.trans_le {x y z : N} (h : Γ.Lt x y) (h' : Γ.Le y z) : Γ.Lt x z := by
  rcases h' with h' | rfl
  · exact h.trans h'
  · exact h

theorem Lt.le {x y : N} (h : Γ.Lt x y) : Γ.Le x y := Or.inl h

theorem Lt.ne {x y : N} (h : Γ.Lt x y) : x ≠ y := by
  rintro rfl
  exact Γ.lt_irrefl x h

theorem not_lt_of_le {x y : N} (h : Γ.Le x y) : ¬ Γ.Lt y x := fun h' =>
  Γ.lt_irrefl x (h.trans_lt h')

theorem IsLevel.mem_of_le {L : Set N} (hL : Γ.IsLevel L) {x y : N} (h : Γ.Le x y)
    (hy : y ∈ L) : x ∈ L := by
  rcases h with h | rfl
  · exact hL x y h hy
  · exact hy

theorem IsLevel.not_mem_of_le {L : Set N} (hL : Γ.IsLevel L) {x y : N} (h : Γ.Le x y)
    (hx : x ∉ L) : y ∉ L := fun hy => hx (hL.mem_of_le h hy)

/-! ### `Reach` -/

variable (Γ)

/-- `Reach e e'`: the target of `e` and the source of `e'` are inner nodes with
`e(1) ≤ e'(0)`; equivalently (for `e ≠ e'`), some directed path passes through `e`
and then through `e'`. -/
def Reach (e e' : E) : Prop := ∃ x y, Γ.tgt e = some x ∧ Γ.src e' = some y ∧ Γ.Le x y

variable {Γ}

theorem Reach.trans {e e' e'' : E} (h : Γ.Reach e e') (h' : Γ.Reach e' e'') :
    Γ.Reach e e'' := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  obtain ⟨x', y', hx', hy', hxy'⟩ := h'
  exact ⟨x, y', hx, hy', Or.inl (hxy.trans_lt ((Γ.lt_of_edge hy hx').trans_le hxy'))⟩

theorem Reach.ne {e e' : E} (h : Γ.Reach e e') : e ≠ e' := by
  rintro rfl
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  exact Γ.not_lt_of_le hxy (Γ.lt_of_edge hy hx)

theorem reach_of_rel {e e' : E} (h : ∃ x, Γ.tgt e = some x ∧ Γ.src e' = some x) :
    Γ.Reach e e' := by
  obtain ⟨x, hx, hx'⟩ := h
  exact ⟨x, x, hx, hx', le_refl' x⟩

theorem isChain_reach : ∀ (l : List E) (a : E),
    (a :: l).IsChain (fun e e' => ∃ x, Γ.tgt e = some x ∧ Γ.src e' = some x) →
      ∀ b ∈ l, Γ.Reach a b
  | [], _, _, b, hb => (List.not_mem_nil hb).elim
  | c :: l, a, h, b, hb => by
    obtain ⟨hac, hc⟩ := List.isChain_cons_cons.1 h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact reach_of_rel hac
    · exact (reach_of_rel hac).trans (isChain_reach l c hc b hb)

/-- On a directed path, an edge reaches every later edge. -/
theorem IsPath.pairwise_reach {p : List E} (hp : Γ.IsPath p) : p.Pairwise Γ.Reach := by
  have key : ∀ l : List E,
      l.IsChain (fun e e' => ∃ x, Γ.tgt e = some x ∧ Γ.src e' = some x) → l.Pairwise Γ.Reach := by
    intro l hl
    induction l with
    | nil => exact List.Pairwise.nil
    | cons a l ih =>
      exact List.Pairwise.cons (isChain_reach l a hl) (ih (List.IsChain.tail hl))
  exact key p hp.2

theorem reach_or_reach_of_pairwise {p : List E} (hp : p.Pairwise Γ.Reach) {e e' : E} (he : e ∈ p)
    (he' : e' ∈ p) (hne : e ≠ e') : Γ.Reach e e' ∨ Γ.Reach e' e := by
  induction p with
  | nil => exact (List.not_mem_nil he).elim
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 hp
    rcases List.mem_cons.1 he with h₁ | h₁
    · subst h₁
      rcases List.mem_cons.1 he' with h₂ | h₂
      · exact (hne h₂.symm).elim
      · exact Or.inl (ha _ h₂)
    · rcases List.mem_cons.1 he' with h₂ | h₂
      · subst h₂
        exact Or.inr (ha _ h₁)
      · exact ih hl h₁ h₂

/-- Two distinct edges on a directed path occur in one of the two orders. -/
theorem reach_of_mem_path {p : List E} (hp : Γ.IsPath p) {e e' : E} (he : e ∈ p) (he' : e' ∈ p)
    (hne : e ≠ e') : Γ.Reach e e' ∨ Γ.Reach e' e :=
  reach_or_reach_of_pairwise hp.pairwise_reach he he' hne

/-- If `e(1) ≤ e'(0)` then some directed path contains `e` and `e'`. -/
theorem exists_path_of_reach {e e' : E} (h : Γ.Reach e e') :
    ∃ p, Γ.IsPath p ∧ e ∈ p ∧ e' ∈ p := by
  obtain ⟨x, y, hx, hy, hxy | rfl⟩ := h
  · obtain ⟨q, hq, hq₁, hq₂⟩ := Γ.exists_path_of_lt hxy
    refine ⟨e :: (q ++ [e']), ⟨List.cons_ne_nil _ _, ?_⟩, List.mem_cons_self, ?_⟩
    · refine List.IsChain.cons (List.IsChain.append hq.2 (List.isChain_singleton _) ?_) ?_
      · intro a ha b hb
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
        subst hb
        refine ⟨y, ?_, hy⟩
        unfold pathTgt at hq₂
        rw [Option.mem_def] at ha
        rw [ha] at hq₂
        simpa using hq₂
      · intro b hb
        obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hq.1
        simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
        subst hb
        refine ⟨x, hx, ?_⟩
        simpa [pathSrc] using hq₁
    · simp
  · exact ⟨[e, e'], ⟨List.cons_ne_nil _ _, List.isChain_pair.2 ⟨x, hx, hy⟩⟩, by simp, by simp⟩

/-- A directed path from `x` through the node `z` to `y`. -/
theorem exists_path_through {x y z : N} (h₁ : Γ.Lt x z) (h₂ : Γ.Lt z y) :
    ∃ p, Γ.IsPath p ∧ Γ.pathSrc p = some x ∧ Γ.pathTgt p = some y ∧
      ∃ e ∈ p, Γ.src e = some z := by
  obtain ⟨p, hp, hp₁, hp₂⟩ := Γ.exists_path_of_lt h₁
  obtain ⟨q, hq, hq₁, hq₂⟩ := Γ.exists_path_of_lt h₂
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hq.1
  refine ⟨p ++ c :: cs, ⟨by simp, List.IsChain.append hp.2 hq.2 ?_⟩, ?_, ?_, c, by simp, ?_⟩
  · intro a ha b hb
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst hb
    refine ⟨z, ?_, by simpa [pathSrc] using hq₁⟩
    unfold pathTgt at hp₂
    rw [Option.mem_def] at ha
    rw [ha] at hp₂
    simpa using hp₂
  · obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hp.1
    simpa [pathSrc] using hp₁
  · unfold pathTgt at hq₂ ⊢
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    exact hq₂
  · simpa [pathSrc] using hq₁

/-- Every edge on a directed path from `x` to `y` has an inner source `z` with `x ≤ z`
and an inner target `z'` with `z' ≤ y`. -/
theorem src_tgt_of_mem_path {p : List E} (hp : Γ.IsPath p) {x y : N}
    (hx : Γ.pathSrc p = some x) (hy : Γ.pathTgt p = some y) {e : E} (he : e ∈ p) :
    (∃ z, Γ.src e = some z ∧ Γ.Le x z) ∧ (∃ z, Γ.tgt e = some z ∧ Γ.Le z y) := by
  have hpw := hp.pairwise_reach
  constructor
  · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hp.1
    have hxa : Γ.src a = some x := by simpa [pathSrc] using hx
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨x, hxa, le_refl' x⟩
    · obtain ⟨b, c, hb, hc, hbc⟩ := (List.pairwise_cons.1 hpw).1 e he
      obtain ⟨b', hb'⟩ : ∃ b', Γ.src a = some b' := ⟨x, hxa⟩
      exact ⟨c, hc, Or.inl ((Γ.lt_of_edge hxa hb).trans_le hbc)⟩
  · have hl : p = p.dropLast ++ [p.getLast hp.1] := (List.dropLast_append_getLast hp.1).symm
    have hya : Γ.tgt (p.getLast hp.1) = some y := by
      unfold pathTgt at hy
      rw [List.getLast?_eq_some_getLast hp.1] at hy
      simpa using hy
    by_cases hlast : e = p.getLast hp.1
    · exact ⟨y, hlast ▸ hya, le_refl' y⟩
    · have he' : e ∈ p.dropLast := by
        rw [hl] at he
        rcases List.mem_append.1 he with h | h
        · exact h
        · exact (hlast (List.mem_singleton.1 h)).elim
      rw [hl] at hpw
      obtain ⟨b, c, hb, hc, hbc⟩ :=
        (List.pairwise_append.1 hpw).2.2 e he' _ (List.mem_singleton_self _)
      exact ⟨b, hb, Or.inl (hbc.trans_lt (Γ.lt_of_edge hc hya))⟩

end PGraph

end FreeMarkov
