/-
Free Markov categories, Stage 4: the structure of a Markov minimal diagram whose trees of
duplicates are combs sorted by a rank (proof of Lemma 4.4, second claim).

"Then a node of `Γ` is either live or a duplicate in `Δ̃_Γ` or a discard. Let `q` be an edge in
`dom(Γ)` or an output of a live node, and consider the edges with the origin `q`. They form a tree
with the root `q` that branches at duplicates, and each of its leaves is a consumer or ends at a
discard. ... So either no consumer has the origin `q` and `q` itself ends at a discard, or the
tree is a binary tree of duplicates whose leaves are the consumers with the origin `q`."

For a sorted comb: the first leaf of a duplicate is the leaf of smallest rank below it
(`lt_of_mem_leafSet`), and the leaves below the input of a duplicate are exactly the leaves of its
tree whose rank is at least that of its first leaf (`leafSet_input`).
-/
module

public import FreeMarkov.Stage4.MoveSkeleton

@[expose] public section

universe w v u₁ u₂

namespace FreeMarkov

open Relation

namespace Diagram

open scoped Classical

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

theorem wellFounded_lt' [Finite N] (X : Diagram G.toFreeGraphMonoid N E) : WellFounded X.Lt := by
  have : IsTrans N X.Lt := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  have : Std.Irrefl X.Lt := ⟨fun a h => X.lt_irrefl a h⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

section Leaves

variable [Fintype E] (X : Diagram G.toFreeGraphMonoid N E)

/-- The consumers following `e` through duplicates: the leaves of the tree below `e`. -/
noncomputable def leafSet (e : E) : Finset E :=
  Finset.univ.filter fun c => X.Sub e c ∧ X.Consumer c

variable {X}

theorem mem_leafSet {e c : E} : c ∈ X.leafSet e ↔ X.Sub e c ∧ X.Consumer c := by
  classical
  simp [leafSet]

omit [Fintype E] in
theorem not_dupStep_of_consumer {e e' : E} (he : X.Consumer e) : ¬ X.DupStep X.val.IsDup e e' := by
  rintro ⟨x, hx, h₁, -⟩
  rcases he with h | ⟨y, hy, hl⟩
  · rw [h] at h₁; cases h₁
  · rw [hy, Option.some.injEq] at h₁
    exact hl.1 (h₁ ▸ hx)

theorem leafSet_consumer {c : E} (hc : X.Consumer c) : X.leafSet c = {c} := by
  ext c'
  rw [mem_leafSet, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    exact PGraph.reflTransGen_dup_of_not_step (fun e' => not_dupStep_of_consumer hc) h
  · rintro rfl
    exact ⟨ReflTransGen.refl, hc⟩

theorem leafSet_disc {e : E} {x : N} (he : X.tgt e = some x) (hx : X.val.IsDisc x) :
    X.leafSet e = ∅ := by
  ext c
  rw [mem_leafSet]
  simp only [Finset.notMem_empty, iff_false, not_and]
  intro h hc
  have hc' : c = e := PGraph.reflTransGen_dup_of_not_step (fun e' hst => by
    obtain ⟨y, hy, h₁, -⟩ := hst
    rw [he, Option.some.injEq] at h₁
    exact X.val.not_isDup_of_isDisc hx (h₁ ▸ hy)) h
  subst hc'
  rcases hc with h' | ⟨y, hy, hl⟩
  · rw [he] at h'; cases h'
  · rw [he, Option.some.injEq] at hy
    subst hy
    obtain ⟨-, f, hf, -⟩ := hl
    obtain ⟨b, hb⟩ := hx
    rw [X.val.outs_eq_nil_of_disc hb] at hf
    cases hf

theorem leafSet_dup {e : E} {d : N} {a : S} (hte : X.tgt e = some d) (hd : X.val.v₁ d = G.dup a)
    {ℓ o : E} (ho : X.outs d = [ℓ, o]) : X.leafSet e = X.leafSet ℓ ∪ X.leafSet o := by
  have hD : X.val.IsDup d := ⟨a, hd⟩
  have hnc : ¬ X.Consumer e := not_consumer_of_tgt_dup hte hD
  ext c
  rw [Finset.mem_union, mem_leafSet, mem_leafSet, mem_leafSet, sub_of_tgt_some X hte]
  simp only [hD, true_and, ho, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]
  constructor
  · rintro ⟨rfl | h | h, hc⟩
    · exact (hnc hc).elim
    · exact Or.inl ⟨h, hc⟩
    · exact Or.inr ⟨h, hc⟩
  · rintro (⟨h, hc⟩ | ⟨h, hc⟩)
    · exact ⟨Or.inr (Or.inl h), hc⟩
    · exact ⟨Or.inr (Or.inr h), hc⟩

theorem not_mem_leafSet_sibling [Finite E] {e : E} {d : N} {a : S} (hte : X.tgt e = some d)
    (hd : X.val.v₁ d = G.dup a) {ℓ o : E} (ho : X.outs d = [ℓ, o]) : ℓ ∉ X.leafSet o := by
  intro h
  rw [mem_leafSet] at h
  have hD : X.val.IsDup d := ⟨a, hd⟩
  have hne : ℓ ≠ o := by
    have := X.outs_nodup d
    rw [ho] at this
    simpa using this
  exact PGraph.not_reflTransGen_sibling X.dupCond
    (⟨d, hD, hte, (X.mem_outs d o).1 (by rw [ho]; simp)⟩ : X.DupStep X.val.IsDup e o)
    (⟨d, hD, hte, (X.mem_outs d ℓ).1 (by rw [ho]; simp)⟩ : X.DupStep X.val.IsDup e ℓ) hne.symm h.1

theorem leafSet_nonempty [Finite E] {e : E} (h : X.ReachCod e) : (X.leafSet e).Nonempty := by
  obtain ⟨c, hc, hc'⟩ := (PGraph.useful_iff_reachCod (D := X.val.IsDup) e).2 h
  exact ⟨c, mem_leafSet.2 ⟨hc, hc'⟩⟩

theorem leafSet_subset_of_sub {e e' : E} (h : X.Sub e e') : X.leafSet e' ⊆ X.leafSet e := by
  intro c hc
  rw [mem_leafSet] at hc ⊢
  exact ⟨h.trans hc.1, hc.2⟩

end Leaves

/-! ### Sorted combs -/

section Sorted

variable [Fintype N] [Fintype E] {X : Diagram G.toFreeGraphMonoid N E} {rk : E → ℕ}

omit [Fintype N] [Fintype E] in
/-- The input of a duplicate. -/
theorem input_of_dup (X : Diagram G.toFreeGraphMonoid N E) {d : N} {a : S}
    (hd : X.val.v₁ d = G.dup a) : ∃ f, X.ins d = [f] ∧ X.tgt f = some d := by
  obtain ⟨f, hf, -⟩ := X.val.ins_eq_of_dup hd
  exact ⟨f, hf, (X.mem_ins d f).1 (by rw [hf]; simp)⟩

/-- **The first leaf is the smallest.** In a sorted comb, every leaf below the second prong of a
duplicate has a larger rank than its first leaf. -/
theorem lt_of_mem_leafSet (hX : X.MarkovMinimal) (hc : X.IsComb) (hs : Sorted rk X) :
    ∀ (d : N) (a : S), X.val.v₁ d = G.dup a → ∀ ℓ o, X.outs d = [ℓ, o] →
      ∀ c ∈ X.leafSet o, rk ℓ < rk c := by
  intro d
  induction d using (wellFounded_lt_flip (X := X)).induction with
  | _ d ih =>
    intro a hd ℓ o ho c hcm
    rcases out_cases hX hd (by rw [ho]; simp : o ∈ X.outs d) with hco | ⟨d', b, hto, hd'⟩
    · rw [leafSet_consumer hco, Finset.mem_singleton] at hcm
      subst hcm
      exact (hs d a hd ℓ c ho).1 hco
    · obtain ⟨ℓ', o', ho'⟩ : ∃ ℓ' o', X.outs d' = [ℓ', o'] := by
        obtain ⟨ℓ', o', h, -⟩ := X.val.outs_eq_of_t_dup hd'
        exact ⟨ℓ', o', h⟩
      have hlt := (hs d a hd ℓ o ho).2 d' b ℓ' o' hto hd' ho'
      rw [leafSet_dup hto hd' ho', leafSet_consumer (hc d' b hd' ℓ' o' ho'), Finset.mem_union,
        Finset.mem_singleton] at hcm
      rcases hcm with rfl | hcm
      · exact hlt
      · exact hlt.trans (ih d' (X.lt_of_edge ((X.mem_outs d o).1 (by rw [ho]; simp)) hto) b hd' ℓ' o'
          ho' c hcm)

/-- **The leaves below a duplicate form an interval of its tree.** If `q` is the origin of the input
`f` of a duplicate `d` with first leaf `ℓ`, the leaves below `f` are the leaves below `q` of rank at
least that of `ℓ`. -/
theorem leafSet_input (hX : X.MarkovMinimal) (hc : X.IsComb) (hs : Sorted rk X) :
    ∀ (d : N) (a : S), X.val.v₁ d = G.dup a → ∀ f ℓ o q, X.ins d = [f] → X.outs d = [ℓ, o] →
      X.IsOrigin q f → X.leafSet f = (X.leafSet q).filter fun c => rk ℓ ≤ rk c := by
  intro d
  induction d using X.wellFounded_lt'.induction with
  | _ d ih =>
    intro a hd f ℓ o q hf ho hq
    have hfd : X.tgt f = some d := (X.mem_ins d f).1 (by rw [hf]; simp)
    have hℓ : X.Consumer ℓ := hc d a hd ℓ o ho
    -- every leaf below `f` has rank at least that of `ℓ`
    have hmin : ∀ c ∈ X.leafSet f, rk ℓ ≤ rk c := by
      intro c hcm
      rw [leafSet_dup hfd hd ho, leafSet_consumer hℓ, Finset.mem_union, Finset.mem_singleton] at hcm
      rcases hcm with rfl | hcm
      · exact le_rfl
      · exact (lt_of_mem_leafSet hX hc hs d a hd ℓ o ho c hcm).le
    have hℓf : ℓ ∈ X.leafSet f := by
      rw [leafSet_dup hfd hd ho, leafSet_consumer hℓ]; simp
    rcases hq.1.cases_tail with rfl | ⟨g, hqg, hgf⟩
    · -- `f` is the root
      ext c
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨h, hmin c h⟩, fun h => h.1⟩
    · -- `f` is the second prong of the duplicate `d₀` above `d`
      obtain ⟨d₀, hD₀, hgd₀, hfd₀⟩ := hgf
      obtain ⟨a₀, ha₀⟩ := hD₀
      obtain ⟨ℓ₀, o₀, ho₀, -⟩ := X.val.outs_eq_of_t_dup ha₀
      have hℓ₀ : X.Consumer ℓ₀ := hc d₀ a₀ ha₀ ℓ₀ o₀ ho₀
      have hfo₀ : f = o₀ := by
        have : f ∈ X.outs d₀ := (X.mem_outs d₀ f).2 hfd₀
        rw [ho₀] at this
        rcases List.mem_pair.1 this with rfl | rfl
        · exact (not_consumer_of_tgt_dup hfd ⟨a, hd⟩ hℓ₀).elim
        · rfl
      subst hfo₀
      have hgi : X.ins d₀ = [g] := by
        obtain ⟨g', hg', -⟩ := X.val.ins_eq_of_dup ha₀
        have : g ∈ X.ins d₀ := (X.mem_ins d₀ g).2 hgd₀
        rw [hg', List.mem_singleton] at this
        rw [hg', this]
      have ih₀ := ih d₀ (X.lt_of_edge hfd₀ hfd) a₀ ha₀ g ℓ₀ f q hgi ho₀ ⟨hqg, hq.2⟩
      rw [leafSet_dup hgd₀ ha₀ ho₀, leafSet_consumer hℓ₀] at ih₀
      have hℓ₀f := not_mem_leafSet_sibling hgd₀ ha₀ ho₀
      ext c
      simp only [Finset.mem_filter]
      constructor
      · intro h
        have h₁ : c ∈ ({ℓ₀} ∪ X.leafSet f : Finset E) := Finset.mem_union_right _ h
        rw [ih₀, Finset.mem_filter] at h₁
        exact ⟨h₁.1, hmin c h⟩
      · rintro ⟨h₁, h₂⟩
        have hlt₀ : rk ℓ₀ < rk ℓ := lt_of_mem_leafSet hX hc hs d₀ a₀ ha₀ ℓ₀ f ho₀ ℓ hℓf
        have h₃ : c ∈ ({ℓ₀} ∪ X.leafSet f : Finset E) := by
          rw [ih₀, Finset.mem_filter]
          exact ⟨h₁, hlt₀.le.trans h₂⟩
        rcases Finset.mem_union.1 h₃ with h₄ | h₄
        · rw [Finset.mem_singleton] at h₄
          subst h₄
          exact absurd h₂ (not_le.2 hlt₀)
        · exact h₄

end Sorted

end Diagram

end FreeMarkov
