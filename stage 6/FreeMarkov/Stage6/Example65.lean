/-
Free Markov categories, Stage 6: Example 6.5, interventions.

For an object `G` of `FinODAG` and a set `V` of vertices (the atomic variables of a singular variable
`v`, `letterSet v`):

* `cut G V` (`G_{\bar v}`): the same vertices in the same order, with the arrows into the vertices of
  `V` removed except their identity loops; it is again an object of `FinODAG`, and the vertices of `V`
  have no parents in it (`pa_cut_of_mem`).
* `incl G V : G_{\bar v} → G` (`i_v`), whose fibers are singletons (`fiber_incl`).
* `intervention` (`i_v^*`), the `i_v`-refinement, and equation (6.2):
  `i_v^*(κ_u) = \bar κ_u ⊗ ε_{pa(u)}` for `u ∈ v` (`equation_6_2`), `i_v^*(κ_u) = \bar κ_u` for `u ∉ v`
  (`intervention_mech_of_not_mem`), and `i_v^*` fixes the duplicates and the discards
  (`intervention_copy`, `intervention_discard`).

The endofunctor of the enlarged signature (the last paragraph of the example) is optional in the plan
and is not formalized.  The cited result C1 enters through `JG` and `Jb`.
-/
module

public import FreeMarkov.Stage6.Theorem67

@[expose] public section

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov JoyalStreet Relation

namespace FinODAG

variable (G : FinODAG) (V : Finset (Fin G.n))

open Classical in
/-- *Example 6.5.* **`G_{\bar v}`**: the subgraph of `G` with the same vertices, in the same order,
from which the incoming arrows at the atomic variables in `v` are removed, except their identity
loops. -/
@[reducible] noncomputable def cut : FinODAG where
  n := G.n
  A := {a : G.A // G.s a = G.t a ∨ G.t a ∉ V}
  s a := G.s a.1
  t a := G.t a.1
  loop x := ⟨G.loop x, Or.inl (by rw [G.s_loop, G.t_loop])⟩
  s_loop x := G.s_loop x
  t_loop x := G.t_loop x
  eq_loop a h := Subtype.ext (G.eq_loop a.1 h)
  s_le_t a := G.s_le_t a.1

/-- *Example 6.5.* The inclusion `i_v : G_{\bar v} → G`, a morphism of `FinODAG`. -/
@[reducible] noncomputable def incl : cut G V ⟶ G where
  onV := id
  onA a := a.1
  s_onA _ := rfl
  t_onA _ := rfl
  monotone := monotone_id

variable {G V}

/-- "Its fibers are singletons." -/
theorem fiber_incl (y : Fin G.n) : fiber (incl G V) y = {y} := by
  ext x; simp [incl]

theorem preimS_incl (S : Finset (Fin G.n)) : preimS (incl G V) S = S := by
  ext x; simp [incl]

/-- "`i_v⁻¹(u) = u` for every atomic variable `u`", hence for every variable. -/
theorem preimW_incl (w : FreeMonoid (Fin G.n)) : preimW (incl G V) w = w := by
  have : preimW (incl G V) = MonoidHom.id _ := by
    refine FreeMonoid.hom_eq fun y => ?_
    rw [preimW_of, fiber_incl, finWord_singleton]; rfl
  rw [this]; rfl

/-- "The atomic variables in `v` have no parents in it." -/
theorem pa_cut_of_mem {u : Fin G.n} (hu : u ∈ V) : (cut G V).pa u = ∅ := by
  ext j
  simp only [Finset.notMem_empty, iff_false]
  intro h
  obtain ⟨hne, a, hs, ht⟩ := (cut G V).mem_pa.1 h
  rcases a.2 with h' | h'
  · exact hne (hs.symm.trans (h'.trans ht))
  · exact h' (ht ▸ hu)

/-- "If `u ∉ v` then `u` has the same parents in both graphs." -/
theorem pa_cut_of_not_mem {u : Fin G.n} (hu : u ∉ V) : (cut G V).pa u = G.pa u := by
  ext j
  rw [(cut G V).mem_pa, G.mem_pa]
  constructor
  · rintro ⟨hne, a, hs, ht⟩
    exact ⟨hne, a.1, hs, ht⟩
  · rintro ⟨hne, a, hs, ht⟩
    exact ⟨hne, ⟨a, Or.inr (ht ▸ hu)⟩, hs, ht⟩

/-- *Example 6.5.* The **`i_v`-intervention** `i_v^* : Cau(G) → Cau(G_{\bar v})`. -/
noncomputable abbrev intervention (JG : G.JS) (Jb : (cut G V).JS) :
    StrictMarkovFunctor JG.FsM Jb.FsM :=
  refine (incl G V) Jb JG

variable (JG : G.JS) (Jb : (cut G V).JS)

/-- `i_v^*` fixes the duplicates on the atomic variables. -/
theorem intervention_copy (u : Fin G.n) :
    Arrow.mk ((intervention JG Jb).map (δ_ (JG.wordM (FreeMonoid.of u)))) =
      Arrow.mk (δ_ (Jb.wordM (FreeMonoid.of u))) := by
  rw [(intervention JG Jb).map_copy, refine_obj, preimW_incl]

/-- `i_v^*` fixes the discards on the atomic variables. -/
theorem intervention_discard (u : Fin G.n) :
    Arrow.mk ((intervention JG Jb).map (ε_ (JG.wordM (FreeMonoid.of u)))) =
      Arrow.mk (ε_ (Jb.wordM (FreeMonoid.of u))) := by
  rw [(intervention JG Jb).map_discard, refine_obj, preimW_incl]

/-- "If `u ∉ v` then `u` has the same parents in both graphs, and `[u ‖ pa_G(u)]` in `Cau(G_{\bar v})`
is the causal mechanism on `u`": `i_v^*(κ_u) = \bar κ_u`. -/
theorem intervention_mech_of_not_mem {u : Fin G.n} (hu : u ∉ V) :
    Arrow.mk ((intervention JG Jb).map (JG.projM.map (EffSig.mechK JG u))) =
      Arrow.mk (Jb.projM.map (EffSig.mechK Jb u)) := by
  rw [refine_mechK, preimS_incl, fiber_incl]
  have h := EffSig.freeEffect_parents (J := Jb) u
  change EffSig.freeEffect Jb ((cut G V).pa u) {u} = _ at h
  rw [← pa_cut_of_not_mem hu]
  exact congrArg Arrow.mk h

/-- In `G_{\bar v}`, for `u ∈ v`, no directed path ends in `u` except the trivial one: the vertices of
`(G_{\bar v})_{S → {u}}` outside `S` are `u` alone (when `u ∉ S`). -/
theorem R_cut {u : Fin G.n} (hu : u ∈ V) (S : Finset (Fin G.n)) (k : Fin G.n) :
    (cut G V).K.R S {u} k ↔ k = u ∧ u ∉ S := by
  constructor
  · rintro ⟨hk, t, ht, h⟩
    rw [Finset.mem_singleton] at ht
    subst ht
    rcases h.cases_tail with rfl | ⟨c, _, hc⟩
    · exact ⟨rfl, hk⟩
    · have := hc.1
      change c ∈ (cut G V).pa t at this
      rw [pa_cut_of_mem hu] at this
      exact absurd this (Finset.notMem_empty c)
  · rintro ⟨rfl, hS⟩
    exact ⟨hS, k, Finset.mem_singleton_self k, ReflTransGen.refl⟩

theorem eInt₁ {u : Fin G.n} (hu : u ∈ V) :
    Fs.of Jb (finWord (G.pa u)) =
      Fs.of Jb (finWord ((cut G V).pa u)) * Fs.of Jb (FreeMonoid.ofList ((G.pa u).sort (· ≤ ·))) := by
  rw [pa_cut_of_mem hu, finWord_empty]
  exact (one_mul _).symm

theorem eInt₂ (u : Fin G.n) :
    Fs.of Jb (finWord ({u} : Finset (Fin G.n))) * Fs.of Jb 1 = Fs.of Jb (finWord {u}) := mul_one _

/-- The diagram of (6.2): `\bar κ_u` next to the discards on the parents of `u` in `G`. -/
noncomputable def interventionDiagram {u : Fin G.n} (hu : u ∈ V) :
    Fs.of Jb (finWord (G.pa u)) ⟶ Fs.of Jb (finWord {u}) :=
  eqToHom (eInt₁ Jb hu) ≫
    (EffSig.mechK Jb u ⊗ₛ EffSig.discW Jb ((G.pa u).sort (· ≤ ·))) ≫ eqToHom (eInt₂ Jb u)

theorem card_mechK {Q : FinODAG} (J : Q.JS) (k u : Fin Q.n) :
    J.card (.mech k) (EffSig.mechK J u) = if u = k then 1 else 0 := by
  simp only [EffSig.mechK, card_comp]
  repeat erw [EffSig.card_castF]
  rw [EffSig.card_mechF]
  simp

theorem interventionDiagram_isEffect {u : Fin G.n} (hu : u ∈ V) :
    EffSig.IsEffect Jb (interventionDiagram Jb hu) := by
  classical
  intro k
  unfold interventionDiagram
  rw [card_comp, card_comp, card_eqToHom, card_eqToHom, card_tensor, card_mechK, EffSig.card_discW]
  have hR := R_cut hu (G.pa u) k
  have hu' : u ∉ G.pa u := G.K.not_mem_pa u
  by_cases h : k = u
  · subst h; simp [hR.2 ⟨rfl, hu'⟩]
  · have : ¬ (cut G V).K.R (G.pa u) {u} k := fun h' => h (hR.1 h').1
    simp [Ne.symm h, this]

/-- **Equation (6.2)** (Example 6.5). For `u ∈ v`, `i_v^*(κ_u) = \bar κ_u ⊗ ε_{pa(u)}`, where `κ_u`,
`\bar κ_u` are the causal mechanisms on `u` in `Cau(G)`, `Cau(G_{\bar v})` and `pa(u)` are the parents
of `u` in `G`: "`[u ‖ pa_G(u)]` consists of `\bar κ_u` and the discards on the parents of `u` in
`G`". -/
theorem equation_6_2 {u : Fin G.n} (hu : u ∈ V) :
    Arrow.mk ((intervention JG Jb).map (JG.projM.map (EffSig.mechK JG u))) =
      Arrow.mk (Jb.projM.map (EffSig.mechK Jb u) ⊗ₛ ε_ (Jb.wordM (finWord (G.pa u)))) := by
  rw [refine_mechK, preimS_incl, fiber_incl,
    ← EffSig.projM_eq_freeEffect (interventionDiagram_isEffect Jb hu)]
  unfold interventionDiagram
  simp only [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]
  change Arrow.mk (Jb.projM.map (EffSig.mechK Jb u) ⊗ₛ
    Jb.projM.map (EffSig.discW Jb ((G.pa u).sort (· ≤ ·)))) = _
  exact mk_tensorHom_congr rfl (ProdSig.projM_discW Jb _)

end FinODAG

end FreeMarkov
