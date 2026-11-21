/-
Free Markov categories, Stage 4: in a Markov minimal sorted comb, the codes of the edges at ports and
of the second prongs of duplicates are determined by the leaves of the trees and the rank; the first
leaves and the discards are characterised by the leaves of the trees.
-/
module

public import FreeMarkov.Stage4.CodingC

@[expose] public section

universe w v u₁ u₂

namespace FreeMarkov

open Relation

namespace Diagram

open scoped Classical

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  [Fintype N] [Fintype E] {D : Diagram G.toFreeGraphMonoid N E} {rk : E → ℕ}

omit [Fintype N] [Fintype E] in
theorem card_ge_two {L : Finset E} {ℓ : E} (h : ℓ ∉ L) (hL : L.Nonempty) : (insert ℓ L).card ≠ 1 := by
  rw [Finset.card_insert_of_notMem h]
  have := hL.card_pos
  omega

variable (hX : D.MarkovMinimal) (hc : D.IsComb) (hs : Sorted rk D) (hrk : Function.Injective rk)
include hX hc hs

include hrk in
/-- **The code of the edge at a port.** -/
theorem codeE_port (p : D.PortT) :
    D.codeE (D.portEdge p) = D.ofLeaves rk (D.leafSet (D.portEdge p)) p := by
  set q := D.portEdge p
  by_cases hcq : D.Consumer q
  · rw [codeE_consumer hcq, leafSet_consumer hcq]
    have hne : ({q} : Finset E).Nonempty := Finset.singleton_nonempty q
    simp only [ofLeaves, dite_eq_left hne, Finset.card_singleton, ite_true]
    rw [show minR rk {q} hne = q from Finset.mem_singleton.1 (minR_mem rk _ hne)]
  cases hte : D.tgt q with
  | none => exact (hcq (Or.inl hte)).elim
  | some x =>
    by_cases hD : D.val.IsDup x
    · obtain ⟨a, ha⟩ := hD
      obtain ⟨ℓ, o, ho, -⟩ := D.val.outs_eq_of_t_dup ha
      have hℓ : D.Consumer ℓ := hc x a ha ℓ o ho
      have hL : D.leafSet q = insert ℓ (D.leafSet o) := by
        rw [leafSet_dup hte ha ho, leafSet_consumer hℓ]; rfl
      have hne := leafSet_nonempty (reachCod_out hX ha (by rw [ho]; simp : o ∈ D.outs x))
      have hnm := not_mem_leafSet_sibling hte ha ho
      rw [codeE_dupIn hte ha ho, ofLeaves, hL, dite_eq_left (Finset.insert_nonempty _ _),
        ite_eq_right (card_ge_two hnm hne)]
      congr 3
      refine (minR_eq hrk _ (Finset.mem_insert_self _ _) fun c hc' => ?_).symm
      rcases Finset.mem_insert.1 hc' with rfl | hc'
      · exact le_rfl
      · exact (lt_of_mem_leafSet hX hc hs x a ha ℓ o ho c hc').le
    · have hl : ¬ D.Live x := fun hl => hcq (Or.inr ⟨x, hte, hl⟩)
      have hx := disc_of_not_live hX x hl hD
      rw [codeE_discIn hte hx p rfl, ofLeaves, leafSet_disc hte hx]
      simp

omit [Fintype N] [Fintype E] hX hc hs in
theorem origin_port_of_reachCod {q e : E} (hq : D.IsOrigin q e) (he : D.ReachCod e) :
    ∃ p, D.portEdge p = q := by
  have hqc : D.ReachCod q := he.of_reflTransGen (PGraph.reflTransGen_step_of_dup hq.1)
  cases hs' : D.src q with
  | none =>
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ((D.mem_dom q).2 hs')
    exact ⟨.inl ⟨⟨j, hj⟩⟩, rfl⟩
  | some z =>
    have hzo : q ∈ D.outs z := (D.mem_outs z q).2 hs'
    have hl : D.Live z := ⟨hq.2 z hs', q, hzo, hqc⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hzo
    exact ⟨.inr ⟨⟨z, hl⟩, ⟨j, hj⟩⟩, rfl⟩

include hrk in
/-- **The code of the second prong of a duplicate.** -/
theorem codeE_second {d : N} {a : S} (hd : D.val.v₁ d = G.dup a) {f ℓ o q : E}
    (hf : D.ins d = [f]) (ho : D.outs d = [ℓ, o]) (hq : D.IsOrigin q f) :
    D.codeE o = D.nextOf rk ((D.leafSet q).filter fun c => rk ℓ < rk c) := by
  have hfd : D.tgt f = some d := (D.mem_ins d f).1 (by rw [hf]; simp)
  have hℓ : D.Consumer ℓ := hc d a hd ℓ o ho
  have hset : D.leafSet o = (D.leafSet q).filter fun c => rk ℓ < rk c := by
    have h₁ := leafSet_input hX hc hs d a hd f ℓ o q hf ho hq
    rw [leafSet_dup hfd hd ho, leafSet_consumer hℓ] at h₁
    have hnm := not_mem_leafSet_sibling hfd hd ho
    ext c
    simp only [Finset.mem_filter]
    constructor
    · intro hco
      have h₂ : c ∈ ({ℓ} ∪ D.leafSet o : Finset E) := Finset.mem_union_right _ hco
      rw [h₁, Finset.mem_filter] at h₂
      exact ⟨h₂.1, lt_of_mem_leafSet hX hc hs d a hd ℓ o ho c hco⟩
    · rintro ⟨h₂, h₃⟩
      have h₄ : c ∈ ({ℓ} ∪ D.leafSet o : Finset E) := by rw [h₁, Finset.mem_filter]; exact ⟨h₂, h₃.le⟩
      rcases Finset.mem_union.1 h₄ with h₅ | h₅
      · rw [Finset.mem_singleton] at h₅
        subst h₅
        exact absurd h₃ (lt_irrefl _)
      · exact h₅
  rw [← hset]
  rcases out_cases hX hd (by rw [ho]; simp : o ∈ D.outs d) with hco | ⟨d', b, hto, hd'⟩
  · rw [codeE_consumer hco, leafSet_consumer hco]
    have hne : ({o} : Finset E).Nonempty := Finset.singleton_nonempty o
    simp only [nextOf, dite_eq_left hne, Finset.card_singleton, ite_true]
    rw [show minR rk {o} hne = o from Finset.mem_singleton.1 (minR_mem rk _ hne)]
  · obtain ⟨ℓ', o', ho', -⟩ := D.val.outs_eq_of_t_dup hd'
    have hℓ' : D.Consumer ℓ' := hc d' b hd' ℓ' o' ho'
    have hL : D.leafSet o = insert ℓ' (D.leafSet o') := by
      rw [leafSet_dup hto hd' ho', leafSet_consumer hℓ']; rfl
    have hne := leafSet_nonempty (reachCod_out hX hd' (by rw [ho']; simp : o' ∈ D.outs d'))
    have hnm := not_mem_leafSet_sibling hto hd' ho'
    rw [codeE_dupIn hto hd' ho', nextOf, hL, dite_eq_left (Finset.insert_nonempty _ _),
      ite_eq_right (card_ge_two hnm hne)]
    congr 3
    refine (minR_eq hrk _ (Finset.mem_insert_self _ _) fun c hc' => ?_).symm
    rcases Finset.mem_insert.1 hc' with rfl | hc'
    · exact le_rfl
    · exact (lt_of_mem_leafSet hX hc hs d' b hd' ℓ' o' ho' c hc').le

/-- **First leaves.** A consumer is the first prong of a duplicate iff a leaf of larger rank
follows its origin. -/
theorem firstLeaf_iff {ℓ : E} :
    (∃ d a o, D.val.v₁ d = G.dup a ∧ D.outs d = [ℓ, o]) ↔
      D.Consumer ℓ ∧ ∃ q, D.IsOrigin q ℓ ∧ ∃ c ∈ D.leafSet q, rk ℓ < rk c := by
  constructor
  · rintro ⟨d, a, o, hd, ho⟩
    obtain ⟨f, hf, hfd⟩ := input_of_dup D hd
    obtain ⟨q, hq⟩ := PGraph.exists_isOrigin D.dupCond f
    have hD : D.val.IsDup d := ⟨a, hd⟩
    have hsℓ : D.DupStep D.val.IsDup f ℓ := ⟨d, hD, hfd, (D.mem_outs d ℓ).1 (by rw [ho]; simp)⟩
    have hso : D.DupStep D.val.IsDup f o := ⟨d, hD, hfd, (D.mem_outs d o).1 (by rw [ho]; simp)⟩
    obtain ⟨c, hcm⟩ := leafSet_nonempty (reachCod_out hX hd (by rw [ho]; simp : o ∈ D.outs d))
    exact ⟨hc d a hd ℓ o ho, q, ⟨hq.1.tail hsℓ, hq.2⟩, c,
      leafSet_subset_of_sub (hq.1.tail hso) hcm, lt_of_mem_leafSet hX hc hs d a hd ℓ o ho c hcm⟩
  · rintro ⟨hℓ, q, hq, c, hcm, hlt⟩
    rcases hq.1.cases_tail with rfl | ⟨g, hqg, hgℓ⟩
    · rw [leafSet_consumer hℓ, Finset.mem_singleton] at hcm
      subst hcm
      exact absurd hlt (lt_irrefl _)
    · obtain ⟨d, ⟨a, hd⟩, hgd, hℓd⟩ := hgℓ
      obtain ⟨ℓ₀, o₀, ho₀, -⟩ := D.val.outs_eq_of_t_dup hd
      have hmem : ℓ ∈ D.outs d := (D.mem_outs d ℓ).2 hℓd
      rw [ho₀] at hmem
      rcases List.mem_pair.1 hmem with rfl | rfl
      · exact ⟨d, a, o₀, hd, ho₀⟩
      · exfalso
        have hgi : D.ins d = [g] := by
          obtain ⟨g', hg', -⟩ := D.val.ins_eq_of_dup hd
          have : g ∈ D.ins d := (D.mem_ins d g).2 hgd
          rw [hg', List.mem_singleton] at this
          rw [hg', this]
        have h₁ := leafSet_input hX hc hs d a hd g ℓ₀ ℓ q hgi ho₀ ⟨hqg, hq.2⟩
        rw [leafSet_dup hgd hd ho₀, leafSet_consumer (hc d a hd ℓ₀ ℓ ho₀), leafSet_consumer hℓ] at h₁
        have hlt₀ : rk ℓ₀ < rk ℓ := lt_of_mem_leafSet hX hc hs d a hd ℓ₀ ℓ ho₀ ℓ
          (by rw [leafSet_consumer hℓ]; simp)
        have h₂ : c ∈ ({ℓ₀} ∪ {ℓ} : Finset E) := by
          rw [h₁, Finset.mem_filter]; exact ⟨hcm, (hlt₀.trans hlt).le⟩
        rcases Finset.mem_union.1 h₂ with h₃ | h₃ <;> rw [Finset.mem_singleton] at h₃ <;> subst h₃
        · exact absurd (hlt₀.trans hlt) (lt_irrefl _)
        · exact absurd hlt (lt_irrefl _)

omit [Fintype N] hc hs in
/-- **Discards.** The edge at a port ends at a discard iff no leaf follows it. -/
theorem disc_iff (p : D.PortT) :
    (∃ x, D.val.IsDisc x ∧ D.ins x = [D.portEdge p]) ↔ D.leafSet (D.portEdge p) = ∅ := by
  constructor
  · rintro ⟨x, hx, hi⟩
    exact leafSet_disc ((D.mem_ins x _).1 (by rw [hi]; simp)) hx
  · intro hL
    set q := D.portEdge p
    have hcq : ¬ D.Consumer q := by
      intro h
      rw [leafSet_consumer h] at hL
      exact Finset.singleton_ne_empty q hL
    cases hte : D.tgt q with
    | none => exact (hcq (Or.inl hte)).elim
    | some x =>
      by_cases hD : D.val.IsDup x
      · obtain ⟨a, ha⟩ := hD
        obtain ⟨ℓ, o, ho, -⟩ := D.val.outs_eq_of_t_dup ha
        obtain ⟨c, hcm⟩ := leafSet_nonempty (reachCod_out hX ha (by rw [ho]; simp : ℓ ∈ D.outs x))
        have : c ∈ D.leafSet q := by rw [leafSet_dup hte ha ho]; exact Finset.mem_union_left _ hcm
        rw [hL] at this
        exact absurd this (Finset.notMem_empty c)
      · have hl : ¬ D.Live x := fun hl => hcq (Or.inr ⟨x, hte, hl⟩)
        have hx := disc_of_not_live hX x hl hD
        obtain ⟨b, hb⟩ := hx
        obtain ⟨f, hf, -⟩ := D.val.ins_eq_of_disc hb
        have : q ∈ D.ins x := (D.mem_ins x q).2 hte
        rw [hf, List.mem_singleton] at this
        exact ⟨x, ⟨b, hb⟩, by rw [hf, this]⟩

end Diagram

end FreeMarkov
