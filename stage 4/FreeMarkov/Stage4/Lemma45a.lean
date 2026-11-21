/-
Free Markov categories, Stage 4: **Lemma 4.5**, first and second items.

"Let `(Γ, v)` be an anchored diagram in `G` from a word `a = a_1 … a_n` to a word `b`. Let `J` be the
set of those `j` such that the `j`-th edge in `dom(Γ)` is not the origin of a consumer ... Then
* `j ∉ J` if and only if there is a directed path in `Γ` that begins with the `j`-th edge in
  `dom(Γ)` and ends in `cod(Γ)`;
* the set `J` is the same for all the diagrams in the `S_M`-congruence class of `Γ`."
-/
module

public import FreeMarkov.Stage4.Lemma44

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

/-- The `j`-th edge of the domain is **dead**: it is not the origin of a consumer (Lemma 4.5, the
set `J`). -/
def Dead (Γ : Diagram G.toFreeGraphMonoid N E) (j : ℕ) : Prop :=
  ∃ e, Γ.dom[j]? = some e ∧ ∀ c, Γ.Consumer c → ¬ Γ.IsOrigin e c

/-- **Lemma 4.5, first item.** For a position `j` of the domain, `j ∉ J` iff a directed path begins
with the `j`-th edge of the domain and ends with an edge of the codomain. -/
theorem lemma_4_5_path [Finite E] (Γ : Diagram G.toFreeGraphMonoid N E) {j : ℕ}
    (hj : j < Γ.dom.length) :
    ¬ Γ.Dead j ↔ ∃ k : ℕ, Γ.toAGraph.HasPath (.edge j) (.edge k) := by
  have hroot : Γ.toPGraph.IsRoot Γ.val.IsDup Γ.dom[j] :=
    PGraph.isRoot_of_src_none ((Γ.mem_dom _).1 (List.getElem_mem _))
  simp only [Dead, List.getElem?_eq_getElem hj, Option.some.injEq, exists_eq_left', not_forall,
    not_not, exists_prop]
  constructor
  · rintro ⟨c, hc, hq⟩
    obtain ⟨c', hc', hc'n⟩ := hc.reachCod.of_reflTransGen (PGraph.reflTransGen_step_of_dup hq.1)
    obtain ⟨k, hk⟩ := exists_getElem?_of_mem ((Γ.mem_cod c').2 hc'n)
    exact ⟨k, (AGraph.hasPath_iff_dPath _ _).2 ⟨Γ.dom[j],
      by simp [AGraph.startEdges, List.getElem?_eq_getElem hj], c', by simp [AGraph.endEdges, hk], hc'⟩⟩
  · rintro ⟨k, hp⟩
    rw [AGraph.hasPath_iff_dPath] at hp
    obtain ⟨e, he, c', hc', h⟩ := hp
    have he' : e = Γ.dom[j] := by
      simpa [AGraph.startEdges, List.getElem?_eq_getElem hj, eq_comm] using he
    have hc'n : Γ.tgt c' = none := by
      have : Γ.cod[k]? = some c' := by simpa [AGraph.endEdges] using hc'
      exact (Γ.mem_cod c').1 (List.mem_of_getElem? this)
    subst he'
    obtain ⟨c, hc, hcc⟩ := PGraph.exists_consumer_of_reachCod (D := Γ.val.IsDup) (Γ := Γ.toPGraph)
      ⟨c', h, hc'n⟩
    exact ⟨c, hcc, hc, hroot⟩

/-- **Lemma 4.5, second item.** The set `J` is the same for all the diagrams in the
`S_M`-congruence class. -/
theorem lemma_4_5_dead [Finite N] [Finite E] [Finite N'] [Finite E'] {Γ : Diagram G.toFreeGraphMonoid N E}
    {Υ : Diagram G.toFreeGraphMonoid N' E'} (h : SRel G.markovTemplates (DClass.mk Γ) (DClass.mk Υ))
    (j : ℕ) : Γ.Dead j ↔ Υ.Dead j := by
  obtain ⟨hd, hc, π, hπ, -, hpath, -⟩ := lemma_4_3 h
  have hlen := dom_length_eq_of_domWord hd
  by_cases hj : j < Γ.dom.length
  · have hj' : j < Υ.dom.length := hlen ▸ hj
    rw [← not_iff_not, lemma_4_5_path Γ hj, lemma_4_5_path Υ hj']
    exact exists_congr fun k => hpath (.edge j) (.edge k)
  · have h₁ : Γ.dom[j]? = none := List.getElem?_eq_none (not_lt.1 hj)
    have h₂ : Υ.dom[j]? = none := List.getElem?_eq_none (hlen ▸ not_lt.1 hj)
    simp [Dead, h₁, h₂]

end Diagram

end FreeMarkov
