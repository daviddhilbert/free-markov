# Stage 6 status

Updated 2026-11-20. Plan: `formalization/PLAN.md`, Stage 6 (D7, ground rules 1–9, the row for
Proposition 6.6 in Section 6, risk 4). Source: Section 6 of `Free Markov - revised.tex`
(functoriality over ordered directed acyclic graphs).

**State: complete.** The "Done when" line of PLAN.md holds: Theorem 6.7 is proved in the form fixed by
D7 — a functor `FinODAGᵒᵖ ⥤ StrictMarkovCat` (`FinODAG.refinementStrict J`), `G ↦ Cau(G)`,
`φ ↦ φ^*`, followed by the inclusion `StrictMarkovCat.toMarCat` into Markov categories and Markov
functors (`FinODAG.refinement J`, `theorem_6_7`, `theorem_6_7_strict`). Every numbered statement of
Section 6 has a Lean declaration (table below). The strictification hypothesis C2 is not used.

## Verification

`python3 scripts/verify.py` (2026-11-20, after all changes): **RESULT: PASS**.

- `lake build FreeMarkovStage0 … FreeMarkovStage6`: exit code 0. Stage 6 builds with no warnings.
- `sorry` in sources: 0; `sorry` warnings in the build log: 0.
- Axioms: all 272 Stage 6 declarations (160 theorems) use only `propext`, `Classical.choice`,
  `Quot.sound`. No `axiom` declarations.
- Cited results in the types of Stage 6 theorems: C1 in 62 theorems, through `FreeMarkov.JoyalStreet`
  (7, the general lemmas of `Lift.lean`, `Coherence.lean`) or through the abbreviation
  `FreeMarkov.FinODAG.JS G := JoyalStreet G.W.toFreeGraphMonoid` (C1 for `W(G)`; 55, everything about
  `Cau(G)`, `φ^*`, Proposition 6.6, Theorem 6.7, Example 6.5). `FreeMarkov.Strictification` (C2): in
  none. The files `ODAG` and `Variables` (FinODAG, fibers, parents, `φ⁻¹(v)`) and the graph lemmas of
  `Prop66` use no cited result.
- Blueprint: 71 nodes, 156 edges, 69 formalized; labels unique, dependencies resolve, acyclic, every
  `\lean` name exists.

## Files (`stage 6/FreeMarkov/Stage6/`, 2 023 lines with the aggregator)

| File | Content |
|---|---|
| `ODAG.lean` | `FinODAG` (vertices `Fin n`, arrows with `s a ≤ t a`, identity loops), `Hom` (weakly monotone graph homomorphisms), the category, `toFinDAG`, `forget`; fibers `fiber`, `fiber_interval`, `lt_of_fiber_lt`, `fiber_disjoint`, `preimS`; parents `pa` (`S_i`), `K` (`K_G : EffSig n`), `W` (`W(G)`), `JS` (C1 for `W(G)`), `Hom.map_pa` |
| `Variables.lean` | Terminology 6.1: `Singular`, `SubVar`; `finWord_eq_of_sorted`; `preimW φ` (`φ⁻¹(v)`), `preimW_mul`, `mem_preimW`, `singular_preimW`, `preimW_of_of_empty` (the converse fails), `preimW_finWord` (`φ⁻¹(v_S) = u_{φ⁻¹(S)}`), `preimW_id`, `preimW_comp` |
| `Refinement.lean` | The note: `R_preimage_parents`, `inD_preimage_parents`; (6.1): `fPhi`, `fPhi_matches`, `fPhi_V`, `fPhi_dup`, `fPhi_disc`, `fPhi_mech`, `fPhi_dup_empty`, `fPhi_disc_empty`, `fPhi_mech_empty`; Definition 6.4: `refine` (`φ^*`), `refine_spec`, `eq_refine`, `refine_obj`, `refine_gen`, `refine_mechK` |
| `Lift.lean` | `ProdSig.projM_copyW`, `projM_discW`, `projM_dupF`; the substitution of the blocks `B_y` for the nodes `κ_y`: `substHom`, `subst` (Theorem 2.3), `subst_obj`, `subst_gen`, `card_subst` (node counts), `refine_projM` (`φ^* ∘ [−]_M = [−]_M ∘ subst`) |
| `Coherence.lean` | Label coherence comparing live producers: `ProdSig.LiveProd`, `sameSkeleton_of_live`, `projM_eq_of_live`; `arrow_projM_eq_of_card_zero` |
| `Causal.lean` | Definition 6.3: `causalEffectSets` (`[v_T ‖ v_S]`), `letterSet`, `singular_unique`, `twistIn` (`ρ_*⁻¹`), `twistOut` (`τ_*`), `causalEffect` (`[w ‖ v]`), `prior`, `causalEffect_finWord`; the twists as multipliers: `isMult_lift`, `multiplier_unique`, `twist_isMultiplier` |
| `Prop66.lean` | Graph part: `liveLab_iff`, `path_of_R`, `R_image` ("erasing the repetitions"), `R_preimS_of`, `liveSet_iff`; `substEffect`, `card_substEffect`; **`prop_6_6_sets`**, `refine_perm`, **`prop_6_6`** |
| `MarCat.lean` | `StrictMarkovCat` and its category; `MarCat`, `MarkovFunctor`, the category `MarCat`; `StrictMarkovFunctor.coreMonoidal`, `braided`, `toMarkovFunctor`; the inclusion `StrictMarkovCat.toMarCat` |
| `Theorem67.lean` | `hom_ext_W`, `refine_id`, `refine_comp`, **`refinementStrict`**, **`refinement`**, **`theorem_6_7`**, **`theorem_6_7_strict`** |
| `Example65.lean` | `cut` (`G_{\bar v}`), `incl` (`i_v`), `fiber_incl`, `preimW_incl`, `pa_cut_of_mem`, `pa_cut_of_not_mem`, `intervention` (`i_v^*`), `intervention_copy`, `intervention_discard`, `intervention_mech_of_not_mem`, `R_cut`, `interventionDiagram`, **`equation_6_2`** |

## Statements against the paper

| Paper | Lean |
|---|---|
| ordered DAG with identity loops, `σ : V → {1, …, n}`; `FinODAG`; morphisms "graph homomorphisms that preserve the total orderings in the weak sense" | `FinODAG`, `FinODAG.Hom`, `FinODAG.instCategory` (reading 1) |
| "the fiber `φ⁻¹(y)` is an interval ... if `y < y'` then every vertex in `φ⁻¹(y)` comes before every vertex in `φ⁻¹(y')`" | `fiber_interval`, `lt_of_fiber_lt` |
| **Terminology 6.1**: variables, atomic, singular, `v_S`, sub-variables, `∩`, `∖` | `FreeMonoid (Fin n)`, `FreeMonoid.of`, `Singular`, `finWord` (Stage 5), `SubVar`; `v_S ∩ v_{S'} = finWord (S ∩ S')` etc. directly |
| **Definition 6.2**: `S_i`, `pa(v_i) = v_{S_i}`, `W(G)`, causal mechanisms, exogenous ones | `pa`, `src_mech`, `W` (= Stage 5's `EffSig.sig` of `K_G`; an exogenous mechanism is `κ_i` with `pa i = ∅`) |
| `Cau(G)`, the free Markov category over `W(G)`; `κ_∅ = 1_∅` | `J.FsM` for `J : G.JS` (Theorem 4.1); `κ_∅ = 1_∅` is a convention of notation, not a declaration |
| **Definition 6.3**: `K_G` acyclic since `j ∈ S_i → j < i` | `K`, `lt_of_mem_pa` |
| causal effect of `v_S` on `v_T` | `causalEffectSets J S T` (= `EffSig.freeEffect`) |
| unique `S, T, ρ, τ` with `v = v_{ρ(S)}`, `w = v_{τ(T)}` | `singular_unique` (reading 3) |
| `[w ‖ v] = τ_* ∘ [v_T ‖ v_S] ∘ ρ_*⁻¹`; prior `[w]` | `causalEffect`, `prior`; for `v = v_S`, `w = v_T`: `causalEffect_finWord` |
| "`τ_*` and `ρ_*` are the multipliers `ι_{v_T → w}` and `ι_{v_S → v}` of Remark 5.3" | `twist_isMultiplier`, `multiplier_unique` (reading 4) |
| `φ⁻¹(v)`; `φ⁻¹(vw) = φ⁻¹(v)φ⁻¹(w)`; singular if `v` is; converse fails; `φ⁻¹(v_S) = u_{S'}` | `preimW`, `preimW_mul`, `singular_preimW`, `preimW_of_of_empty` with `not_singular_of_of`, `preimW_finWord` |
| **(6.1)** and "`f_φ` ... matches duplicates and discards"; the effect is defined and is a morphism `φ⁻¹(pa(v)) → φ⁻¹(v)` | `fPhi`, `fPhi_V`, `fPhi_dup`, `fPhi_disc`, `fPhi_mech`, `fPhi_matches` |
| "If `φ⁻¹(v) = ∅` then `f_φ(ε_v) = f_φ(δ_v) = 1_∅` and `f_φ(κ_v)` is the discard on `φ⁻¹(pa(v))`" | `fPhi_dup_empty`, `fPhi_disc_empty`, `fPhi_mech_empty` |
| the note on `H_{φ⁻¹(pa(v)) → φ⁻¹(v)}` (no other vertices; paths inside `φ⁻¹(v)` except the first vertex) | `R_preimage_parents`, `inD_preimage_parents` |
| **Definition 6.4**: `φ^*`, the unique strict Markov functor agreeing with `f_φ` | `refine φ JH JG`, `refine_spec`, `eq_refine` |
| **Example 6.5**: `G_{\bar v}`, `i_v`, fibers singletons, `i_v^*`, (6.2), the case `u ∉ v`, duplicates and discards fixed | `cut`, `incl`, `fiber_incl`, `intervention`, `equation_6_2`, `intervention_mech_of_not_mem`, `intervention_copy`, `intervention_discard` (reading 6) |
| Example 6.5, enlarged signature endofunctor | not formalized (optional in the plan) |
| **Proposition 6.6** `φ^*([w ‖ v]) = [φ^*(w) ‖ φ^*(v)]`, in the unabbreviated form (6.2) of the display | `prop_6_6` (general singular `v`, `w`), `prop_6_6_sets` (`v_S`, `v_T`) (reading 5) |
| **Theorem 6.7** | `refinementStrict`, `refinement`, `theorem_6_7`, `theorem_6_7_strict`; identities `refine_id`, composition `refine_comp` |
| `MarCat` (D7) | `MarCat`, `MarkovFunctor`, `StrictMarkovCat`, `StrictMarkovCat.toMarCat` (reading 7) |

## The statement of Theorem 6.7, for the author's review

**Hypothesis.** For every object `G` of `FinODAG`, an instance `J_G` of the cited result C1
(Joyal–Street, Theorem 2.3, in the comparison form of D4; `structure JoyalStreet`, reviewed and
accepted on 2026-11-20) for the free graph monoid underlying `W(G)`. In Lean this is one argument
`J : ∀ G : FinODAG, G.JS`. Nothing else is assumed: the strictification C2 is not used, and every step
the paper leaves to the reader (in particular the substitution of the blocks `B_y`, PLAN.md Section 6)
is proved.

**Objects of `FinODAG`.** A finite set of vertices `{0, …, n-1}` with its natural order, a finite set
of arrows with source and target maps, exactly one loop (the identity loop) at each vertex, and every
arrow going weakly up (`s(a) ≤ t(a)`), i.e. the order extends the order given by the directed paths.
Parallel arrows are allowed. **Morphisms** `φ : H → G`: graph homomorphisms (a map on vertices and a
map on arrows compatible with sources and targets) whose map on vertices is weakly order preserving.

**Construction.** For `G` with vertices `v_1 < … < v_n`, `S_i` is the set of `j ≠ i` with an arrow
`v_j → v_i`; `W(G)` is the free `DD`-graph monoid on the vertices with `δ_v`, `ε_v` and
`κ_{v_i} : v_{S_i} → v_i` (parents in increasing order). `Cau(G)` is `F_s(W(G))/S_M`, built from
`J_G`; by Theorem 4.1 (`JoyalStreet.theorem_4_1`) it is the free strict Markov category over `W(G)`.
For `φ : H → G`, `φ^* : Cau(G) → Cau(H)` is the unique strict Markov functor with
`φ^*(v) = φ⁻¹(v)` (fibres listed in the order of `H`), `φ^*(δ_v) = δ_{φ⁻¹(v)}`,
`φ^*(ε_v) = ε_{φ⁻¹(v)}`, `φ^*(κ_v) = [φ⁻¹(v) ‖ φ⁻¹(pa(v))]` (the causal effect in `Cau(H)`).

**Theorem 6.7 (as formalized).** Given `J` as above:

1. *(Strict form.)* There is a functor `R_J : FinODAGᵒᵖ → StrictMarkovCat` — the category whose
   objects are strict Markov categories and whose morphisms are strict Markov functors, composed as
   functors — with `R_J(G) = Cau(G)` and `R_J(φ) = φ^*` for every morphism `φ : H → G`. That is,
   `(1_G)^* = 1_{Cau(G)}` and `(φ ∘ ψ)^* = ψ^* ∘ φ^*` for `ψ : G'' → G'`, `φ : G' → G`, as equalities of
   strict Markov functors (on the nose, not up to isomorphism). (`refinementStrict J`,
   `theorem_6_7_strict`.)
2. *(D7.)* Composing with the inclusion `StrictMarkovCat → MarCat` gives a functor
   `FinODAGᵒᵖ → MarCat` sending `G` to `Cau(G)` with its structure of a Markov category in the sense of
   Mathlib (Stage 0 bridge: associators and unitors identities) and `φ` to `φ^*` regarded as a Markov
   functor, i.e. a strong symmetric monoidal functor matching duplicates and discards, whose structure
   isomorphisms are identities. Here `MarCat` has as objects the (Mathlib) Markov categories and as
   morphisms the Markov functors of the Introduction: a functor with a strong symmetric monoidal
   structure (`μ : F X ⊗ F Y ≅ F(X ⊗ Y)`, `ε : 1 ≅ F 1`, compatible with associators, unitors and
   symmetries) such that `μ⁻¹ ∘ F(δ_X) = δ_{F X}` and `ε⁻¹ ∘ F(ε_X) = ε_{F X}`; composition is
   composition of functors with the composite structure. (`refinement J`, `theorem_6_7`.)

Universes: the objects of `Cau(G)` and its hom-sets are in `Type`, so the functors land in
`StrictMarkovCat.{0,0}` and `MarCat.{0,0}`.

## Readings fixed in Stage 6 (within the plan; no statement of a numbered result departs from the paper)

1. **`FinODAG`** follows the plan's default: vertices `Fin n` in their natural order (the bijection
   `σ`), so "the total ordering extends the path ordering" is `s(a) ≤ t(a)` for every arrow (which
   also gives acyclicity, `toFinDAG`). The arrows form a finite type, as in Stage 5's `FinDAG`, so
   parallel arrows are allowed, and a morphism carries its map on arrows (a graph homomorphism, as the
   paper says); `φ^*` depends only on the map on vertices.
2. **One instance of C1 per graph.** `Cau(G)` is built from C1 for `W(G)`, so Theorem 6.7 takes a
   family `J : ∀ G, G.JS`, visible in its type (ground rule 2). The abbreviation `G.JS` is added to the
   cited structures of `scripts/verify.py` so that the report lists these theorems as using C1.
3. **Singular variables and twists.** A permutation `ρ` of `S` with `v = v_{ρ(S)}` is the list of the
   elements of `S` in the order `ρ(s_1), …` (as in Stage 5's twists), so "unique `S`, `ρ`" is
   `singular_unique` (`S` is the set of letters of `v`, the list is `v`). `ρ_*⁻¹` and `τ_*` are the
   node-free diagrams connecting equal atomic variables (Stage 5's `permFs`).
4. **"`τ_*`, `ρ_*` are the multipliers of Remark 5.3."** Remark 5.3 is stated in Stage 5 for a strict
   Markov category on `FreeMonoid X` itself; in `Cau(G)` the same fact is proved directly: the twist is
   a multiplier on the letters of its domain (`twist_isMultiplier`), and two multipliers on the letters
   of a singular word with the same codomain are equal (`multiplier_unique`, every multiplier being the
   image of a morphism of `F_s(W(G))` without causal mechanisms, then label coherence).
5. **Proposition 6.6** is an equation in `Arrow Cau(H)` between `φ^*([w ‖ v]) : φ^*(v) → φ^*(w)` and
   `[φ⁻¹(w) ‖ φ⁻¹(v)]`, whose objects agree by `refine_obj` (`φ^*(v) = φ⁻¹(v)`); `φ⁻¹(v)` is singular by
   `singular_preimW`. The unabbreviated form (6.2) of the paper is the same statement: the left-hand
   effect there is `φ^*([w ‖ v]_{(V_G, K_G)})` by Proposition 5.6, and the right-hand side is
   `[φ^*(w) ‖ φ^*(v)]_{(V_H, K_H)}`.
6. **Example 6.5.** The singular variable `v` enters through its set of atomic variables `V`
   (`letterSet v`). Equation (6.2) is an equation in `Arrow`: `\bar κ_u ⊗ ε_{pa(u)}` has domain
   `∅ ⊗ pa_G(u)` and codomain `u ⊗ ∅`, which are `pa_G(u)` and `u`.
7. **`MarCat`** (D7): Mathlib's `MarkovCategory` for the objects; Markov functors as a Mathlib
   `Functor.Braided` structure plus the two matching conditions, in the form already used for `eval`
   in Stage 5's `Strictification` (`map_copy`, `map_discard`). Mathlib has no bundled category of
   monoidal categories, so `MarCat`, `MarkovFunctor` and `StrictMarkovCat` are defined here. The laws of
   `StrictMarkovCat` hold by `rfl`; those of `MarCat` by comparing the structure morphisms `ε`, `μ`.

## Proof methods differing from the paper (statements unchanged)

1. **Proposition 6.6, the diagram `Γ_{φ^* G}`.** The paper builds `Γ_{φ^* G}` from `Γ_G` by replacing
   edges, duplicates, discards and the nodes `κ_y` by the blocks `B_y`. Here this substitution is the
   strict symmetric monoidal functor `subst : F_s(W(G)) → F_s(W(H))` given by Theorem 2.3 (C1) from the
   values on generators (PLAN.md, Section 6: "substitution of diagrams for nodes is the functor induced
   by C1"). "`Γ_{φ^* G}` represents `φ^*([w ‖ v])`" is `refine_projM`; "for each `x ∈ φ⁻¹(D ∖ S)` there
   is exactly one node `k_x` and the other nodes are duplicates and discards" is `card_subst` with the
   note `R_preimage_parents`.
2. **Proposition 6.6, live nodes and (∗).** The paper's claim (∗) (origins determined by values) is
   Stage 5's label coherence. `Γ_{φ^* G}` may have nodes `k_x` that are not live (those with
   `x ∈ φ⁻¹(D ∖ S) ∖ (D' ∖ S')`); the paper compares live nodes only, and so does the formal proof:
   `ProdSig.sameSkeleton_of_live` is Stage 5's `sameSkeleton_of_labels` with "the same producers occur"
   weakened to "the same producers occur and are connected to the codomain". The paper's two path
   arguments ("so `p_0, …, p_r` form a directed path in `H` ...", "erasing the repetitions ...") are
   `liveSet_iff` with `R_image`. Lemma 4.4 then gives the equality (`projM_eq_of_live`).
3. **Proposition 6.6, twists.** "`φ^*(τ_*)` is represented by the diagram without nodes ..." is
   `refine_perm`: `subst` of a node-free diagram has no node of a causal mechanism, and two such
   morphisms from a singular word to the same word are equal in `Cau(H)` (label coherence).
4. **Theorem 6.7** follows the paper: identities by `[v ‖ pa(v)] = κ_v` (Stage 5's
   `freeEffect_parents`) and uniqueness; composition by `ψ⁻¹(φ⁻¹(v)) = (φ ∘ ψ)⁻¹(v)`, matching of
   duplicates and discards, Proposition 6.6 for `ψ` (the `v_S`, `v_T` case suffices) and uniqueness.

Steps the paper leaves to the reader that are proved here (PLAN.md, Section 6): Proposition 6.6,
"substitution of the blocks `B_y`" (`subst`, `card_subst`, `refine_projM`).

## Items from earlier stages

- Stage 3, open item 2 (the diagram of `δ_a` as one glued diagram): not needed by Stage 6 (the
  duplicates on words enter through `ProdSig.projM_copyW`, a (1.2)-composite); stays open as decided.
- Stage 3, open item 1: not touched.

## Paper feedback

None. No step of Section 6 needed a change; `formalization/PAPER-FEEDBACK.md` was not created.

## Changes outside `stage 6/`

- `lakefile.toml`: library `FreeMarkovStage6` added and made a default target.
- `scripts/verify.py`: Stage 6 added to `STAGES`; `FreeMarkov.FinODAG.JS` added to `CITED` (point 2).
- `formalization/blueprint/src/content.tex`: section "Refinement (Stage 6)" rewritten: nodes
  `def:6.finodag`, `ter:6.1`, `def:6.2`, `def:6.3`, `def:6.preim`, `def:6.4`, `ex:6.5`, `lem:6.subst`,
  `prop:6.6`, `def:6.marcat`, `thm:6.7`, all formalized (`\lean`, `\leanok`).
- `formalization/PLAN.md`: Stage 6 record.
- No Stage 0–5 source and no manuscript file was changed. Nothing was installed and `lake update` was
  not run. Nothing committed.
