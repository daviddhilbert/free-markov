# Stage 5 status

Updated 2026-11-20. Plan: `formalization/PLAN.md`, Stage 5 (D6, C2, ground rules 1–9). Source:
Section 5 of `Free Markov - revised.tex` (effects in a Markov category).

**State: complete.** The "Done when" line of PLAN.md holds: Lemma 5.5 (`EffData.lemma_5_5`) and
Proposition 5.6 (`EffData.prop_5_6`) are proved in the generality fixed by D6 — every strict Markov
category, with the multipliers read as `m`-fold copies, no straightness — and the straight case of
the text is covered by Remark 5.2 (`remark_5_2`: in a straight category the `m`-fold copy is the only
multiplier on `(w, w^m)`, so the text's `ι_{w → w^m}` is the `m`-fold copy).

## Verification

`python3 scripts/verify.py` (2026-11-20, after all changes): **PASS**.

- `lake build FreeMarkovStage0 … FreeMarkovStage5`: exit code 0. Stage 5 builds with no warnings.
- `sorry` in sources: 0; `sorry` warnings in the build log: 0.
- Axioms: all 456 Stage 5 declarations (239 theorems) use only `propext`, `Classical.choice`,
  `Quot.sound`. No `axiom` declarations.
- Cited results in the types of Stage 5 theorems: `FreeMarkov.JoyalStreet` (C1) in 78 theorems, all
  about free Markov categories `F_s(G)/S_M` or their functors (files `Counts`, `Free`, `Remarks`,
  `EffectFree`, `Effect`, `Value`); `FreeMarkov.Strictification` (C2) in 19 theorems, all in
  `Strictification.lean` (the structure's own projections and the effects in an arbitrary Markov
  category); both in `Strictification.MData.effect_strict`. The files `Multipliers`, `Labels` and
  `Graph` (straightness, multipliers, `m`-fold copies, label coherence, `FinDAG`, the graph theory of
  Lemma 5.5) use no cited result.
- Blueprint: 67 nodes, 138 edges, 58 formalized; labels unique, dependencies resolve, acyclic,
  every `\lean` name exists.

## Files (`stage 5/FreeMarkov/Stage5/`, 2 970 lines with the aggregator)

| File | Content |
|---|---|
| `Multipliers.lean` | `Straight`, `straight_iff`; Definition 5.1 `IsMult`, `IsMultiplier`; the `m`-fold copy `copyN` (`copyN_zero/one/two/succ`), `isMult_copyN`; `StrictMarkovFunctor.map_copyN`; `IsMult.exists_preimage` (multipliers in the image of a functor injective on products) |
| `Labels.lean` | `ProdSig` (letters with at most one producer each) and its free `DD`-graph monoid `Q.G`; origins and live nodes determined by letters (`originAt_dom_iff`, `originAt_out_iff`, `live_iff_liveLab`); **label coherence** `sameSkeleton_of_labels` |
| `Counts.lean` | Number of nodes with a given value, for diagrams, classes and morphisms of `F_s(G)` (additive under `∘`, `⊗`; zero on identities and symmetries) |
| `Free.lean` | `JoyalStreet.lift` (the functor of Theorem 4.1, `lift_obj`, `lift_gen`, `eq_lift`, `functor_ext`); `ProdSig.toHom`; `ProdSig.projM_eq_of_card` (uniqueness in `F_s(Q.G)/S_M` from label coherence and Lemma 4.4); `ProdSig.free X` (only duplicates and discards) and `free_hom_eq` |
| `Remarks.lean` | `copyFunctor`; `remark_5_7_unique`, `remark_5_7_copy`, `copyN_comp_map` (Remark 5.7, first claim); **`remark_5_2`**; existence of multipliers `exists_multiplier`; `underlyingDD`; **`remark_5_3`**, **`remark_5_3_none`** |
| `Graph.lean` | `FinDAG`, its category, `FinDAG.isTerminal`; `EffSig` (the sets `S_i`), `toFinDAG`; `G_{S → T}` (`R`, `InD`, `DArr`); Lemma 5.5, graph part: `Anc` (`A`), `Ti` (`T_i`), `mem_Ti_self`, `not_inD_Ti_of_child`, `R_Ti_iff`, `R_Ti_T_iff`, `R_iff_R_Ti_or`, `not_R_Ti_and` |
| `EffectFree.lean` | `finWord` (`w_S`); `EffSig.sig` (the production signature `W(K)`); `IsEffectDiagram`, `IsEffect`; building blocks and `exists_effect`; `freeEffect`, `projM_eq_freeEffect`; `isEffect_comp`, `lemma_5_5_free`; `freeEffect_parents`; `effectDiagram_sameSkeleton`, `effectDiagram_live`, `effectDiagram_congruent` |
| `Effect.lean` | `EffData` (`W`, `K` in a strict Markov category), `functor` (`F_{(W,K)}`), **`effect`**, **`lemma_5_5`**, `map`, `functor_map`, **`prop_5_6`**; `freeData`, `effect_freeData`; node-free permutation diagrams `permFs`, `permStar`, `permStar_comp`, **`twist`** |
| `Strictification.lean` | **`Strictification`** (C2), `EvalStrict`; `straight_of_mulEquiv`, `straight_str`; `MData` and **`MData.effect`** (effects in an arbitrary Markov category); `effect_mk_congr`; **`MData.effect_strict`** |
| `Value.lean` | `ProdSig.relabelTo`; `ProdSig.value_relabel`; **`EffData.effect_eq_value`** (Definition 5.4 literally); `value_copy_diagram` (Remark 5.7 for diagrams of copies) |

## Statements against the paper

| Paper | Lean |
|---|---|
| straight; "`w^n ≠ w^m` for all `w ≠ 1`, `n ≠ m`" | `Straight C` (on the monoid of objects of a `StrictMarkov C`); `straight_iff` |
| **Definition 5.1**: multiplier on `(W, v)` | `IsMult W f` (generated arrows), `IsMultiplier W v f` for `f : W.prod ⟶ v` |
| `m`-fold copy, recursion of Remark 5.2 | `copyN w m`; `copyN_zero`, `copyN_one`, `copyN_two`, `copyN_succ` |
| **Remark 5.2**: exactly one multiplier on `(w, w^m)` in straight `M` | `isMultiplier_copyN` (existence), `remark_5_2` (every multiplier `w → w^m` is `copyN w m`) |
| Remark 5.2, proof: only one morphism `a → a^m` in `F_s(G_a)/S_M` | `remark_5_7_unique` (via `ProdSig.free_hom_eq`) |
| **Remark 5.3**, first paragraph: underlying free `DD`-graph monoid | `underlyingDD X` |
| Remark 5.3: exactly one multiplier on `(W, v)` for distinct letters, `v` a word in them; none otherwise | `remark_5_3` (`∃!`), `remark_5_3_none` |
| `FinDAG`, its terminal object | `FinDAG`, `FinDAG.isTerminal` |
| graph of `K`, acyclic after adding loops | `EffSig n` (with `acyclic`), `EffSig.toFinDAG` |
| `G_{S → T}`, its vertices, its arrows; children of `j` | `EffSig.InD S T`, `EffSig.R S T` (= `V(G_{S→T}) ∖ S`), `EffSig.DArr S T` |
| the two notes after `G_{S → T}` | `inD_of_mem_pa`, `not_dArr_of_mem` |
| **Definition 5.4**: components, fused diagram `Γ_{[w_T ‖ w_S]}` | `IsEffectDiagram S T Γ` (see reading 4); existence `exists_effect` |
| "the morphism that it represents is unique" (independence of the assignment) | `projM_eq_freeEffect`, `effectDiagram_sameSkeleton` |
| `[w_T ‖ w_S]_{(W,K)}` | `EffData.effect D J S T : D.wS S ⟶ D.wS T`; in the free category `EffSig.freeEffect J S T` |
| the morphism represented by `Γ_{[w_T ‖ w_S]}` in `M` | `EffData.effect_eq_value` |
| free case: Markov minimal, each `κ_i` once and live, same skeleton, Markov congruent | `IsEffectDiagram.card`, `effectDiagram_live`, `effectDiagram_sameSkeleton`, `effectDiagram_congruent` (reading 6) |
| **Lemma 5.5**, first item | `mem_Ti_self`, `not_inD_Ti_of_child` |
| **Lemma 5.5**, second item | `EffData.lemma_5_5` (in `M`), `EffSig.lemma_5_5_free`, "more precisely": `isEffect_comp` with `R_Ti_iff`, `R_Ti_T_iff`, `R_iff_R_Ti_or` (reading 7) |
| **Proposition 5.6** | `EffData.prop_5_6` (D6: strict `M`, `N`), with `EffData.map F` = `(F(W), F(K))` |
| twists, `τ_*`, `[τ(T) ‖ σ(S)]` | `EffData.permStar`, `permStar_comp` (`σ_*⁻¹`), `EffData.twist` |
| **Remark 5.7**: `m`-fold copy is the image of the unique `a → a^m`; diagrams of copies represent it, however ordered; functors preserve it; Def. 5.4, Lemma 5.5, Prop. 5.6 without straightness | `remark_5_7_copy`, `value_copy_diagram`, `copyN_comp_map`, `StrictMarkovFunctor.map_copyN`; D6 is the primary form throughout |
| `str(M)`, `eval`, C2 | `Strictification M Str`, `Strictification.EvalStrict` |
| "`str(M)` is straight" | `Strictification.straight_str` |
| effects in an arbitrary `M`: `eval([T ‖ S]_{(W,K)})` | `Strictification.MData.effect` |
| for strict `M` this is the effect formed in `M` | `Strictification.MData.effect_strict` |

## The statement of `Strictification` (C2), for the author's review

`Strictification M Str` is assumed (a structure passed to the theorems, never an axiom). In ordinary
mathematical language, for a Markov category `M` (Mathlib's `MarkovCategory`: symmetric monoidal,
every object a commutative comonoid compatible with `⊗`, discards natural) it states:

1. **The strict Markov category `str(M)`.** `Str` is a strict Markov category (the `StrictMarkov`
   structure of Stage 0: a category whose objects form a monoid under `⊗`, with symmetries,
   duplicates and discards satisfying (1.1)–(1.3) strictly), and its monoid of objects is
   isomorphic to the free monoid `W(M₀)` on the objects of `M` (field `words`). *Source:* Section 5
   ("The objects of `str(M)` are the words of the free monoid `W(M₀)`"), following Joyal–Street §1.1
   and Mac Lane–Paré §2.
2. **The evaluation functor.** A functor `eval : str(M) → M` (field `eval`). *Source:* Section 5.
3. **`eval` is a Markov functor.** It is strong symmetric monoidal (field `braided`: Mathlib's
   `Functor.Braided`, i.e. a strong monoidal functor whose structure isomorphisms
   `μ : eval(v) ⊗ eval(w) ≅ eval(v w)`, `ε : 1 ≅ eval(∅)` commute with the symmetries), and it matches
   the duplicates and the discards: `μ⁻¹ ∘ eval(δ_w) = δ_{eval(w)}` and `ε⁻¹ ∘ eval(ε_w) = ε_{eval(w)}`
   for every word `w` (fields `map_copy`, `map_discard`). *Source:* "it follows from the MacLane
   coherence theorem that `eval : str(M) → M` is indeed a Markov functor" (Mac Lane coherence).
4. **`eval` is full** (field `full`) **and faithful** (field `faithful`): every morphism
   `eval(w) → eval(w')` of `M` is `eval` of exactly one morphism `w → w'` of `str(M)`.
   *Source:* "Moreover, `eval` is full and faithful" (by construction in Mac Lane–Paré §2; used in
   Section 5 as "`κ_i : eval(w_{S_i}) → a_i` a morphism of `M`, that is, a morphism `w_{S_i} → w_i` of
   `str(M)`"; Fritz 2020, Proposition 10.16, is cited for the comonoid equivalence, which is not
   assumed here).
5. **`eval` on objects.** `eval(∅) = 1` (field `eval_one`), `eval(a) = a` for a word `a` of length one
   (field `eval_of`: "the identity on one-letter words"), and
   `eval(a_1 … a_{n+1}) = eval(a_1 … a_n) ⊗ a_{n+1}` for `n ≥ 1` (field `eval_snoc`). *Source:* the
   displayed definition of `eval` in Section 5.
6. **Strictness when `M` is strict** (separate structure `Strictification.EvalStrict T`, for a strict
   Markov category `C` with Mathlib's structure given by the Stage 0 bridge): there is a strict Markov
   functor `F : str(C) → C` (Stage 0: `F(v w) = F(v) F(w)`, `F(1) = 1`, preserving `⊗` of morphisms,
   symmetries, duplicates and discards on the nose) whose underlying functor is `eval`, and the
   structure isomorphisms `μ_{v,w}` and `ε` of `eval` are identities. *Source:* "If `M` is itself
   strict then `eval` is a strict Markov functor" (end of Section 5).

Not assumed (the paper mentions it but the effects do not use it): that `eval` is surjective on
isomorphism classes, that it is a comonoid equivalence, and the quasi-inverse `alp : M → str(M)`.
Proved rather than assumed: "`str(M)` is straight, since its objects form a free monoid"
(`straight_str`). Only clause 6 is used together with clauses 1–5 (in `MData.effect_strict`); the
definition of effects in `M` uses clauses 1–2, 4 (fullness, to lift `κ_i`) and 5 (`eval(a_i) = a_i`).

## Readings fixed in Stage 5 (within the plan; no statement of a numbered result departs from the paper)

1. **Straight.** "`M` is strict and the monoid has no idempotents or elements of finite order other
   than `1`": `Straight C` is the condition on the monoid of objects of a `StrictMarkov C`. "`n ≠ m > 0`"
   in the reformulation is read as `n ≠ m` with `n, m ≥ 0` (it includes `w^0 = 1`, as the text says).
2. **Multipliers.** "Generated from the duplicates, discards, symmetries, and identities on `w_i`" is
   the closure under composition and `⊗` of `δ_{w_i}`, `ε_{w_i}`, `σ_{w_i, w_j}`, `1_{w_i}` and the empty
   product `1_1` (`IsMult`); a multiplier on `(W, v)` has domain `w = ⊗_i w_i = W.prod`.
3. **D6.** Definition 5.4, Lemma 5.5 and Proposition 5.6 are stated in every strict Markov category
   with the multipliers read as `m`-fold copies; the effect is never formed through the multipliers
   `ι`, so no straightness hypothesis appears. In a straight category the two readings agree by
   Remark 5.2 (`remark_5_2`).
4. **The fused diagram.** Definition 5.4 builds `Γ_{[w_T ‖ w_S]}` by fusing the components `Γ_i` along
   an assignment of codomain edges to children. The formalization recognises it by the description
   the paper itself uses in the proofs of Lemma 5.5 and Proposition 6.6: `IsEffectDiagram S T Γ` — a
   diagram of the free `DD`-graph monoid `W(K)` (letters `1, …, n`, duplicates, discards, one arrow
   `κ_i : w_{S_i} → i` per `i`) with domain `w_S`, codomain `w_T`, exactly one node `κ_i` for each
   `i ∈ V(G_{S → T}) ∖ S` and no other node `κ_j` (its other nodes are duplicates and discards). Every
   fused diagram, for every assignment and every depiction of the multipliers in binary form, is
   such a diagram; the wiring is then forced by the indices (label coherence). The effect in `C` is
   the image of its class under the strict Markov functor `F_{(W,K)} : F_s(W(K))/S_M → C` with
   `F(i) = w_i`, `F(κ_i) = κ_i` (Theorem 4.1), and `effect_eq_value` proves that this is the value in
   `C` (Section 2) of the image of the diagram in `C`, i.e. "the morphism that it represents". The
   literal fusion along an assignment is not constructed as a separate operation on diagrams.
5. **`G_{S → T}`.** "All the directed paths that end in `T` but do not travel toward `S`": a vertex
   outside `S` lies on such a path iff a directed path from it through vertices outside `S` ends in
   `T` (`R S T`); `V(G_{S → T}) = S ∪ R S T` (it contains `T`, `mem_T_inD`); its arrows are those
   `j → k` with `k ∈ R S T` (all of them lie on such paths).
6. **Free case of Definition 5.4.** "Markov minimal ... any two such diagrams have the same skeleton,
   hence Markov congruent" is formalized for the free `DD`-graph monoid `W(K)`, where the letters are
   the indices (the case used in Section 6 and in the application): any two effect diagrams have the
   same skeleton, every node `κ_i` of an effect diagram is live (not quasi-terminal), and two Markov
   minimal effect diagrams are Markov congruent. The general case of an `M` whose objects form a free
   monoid with the `w_i` letters (possibly repeated) is its relabelling and is not stated separately.
7. **Lemma 5.5, "more precisely".** "If the multipliers are depicted suitably then there is a level `L`
   of `Γ_{[T‖S]}` whose layers are `Γ_{[T_i‖S]}` and `Γ_{[T‖T_i]}`" is read as: an effect diagram for
   `(S, T_i)` glued to an effect diagram for `(T_i, T)` is an effect diagram for `(S, T)`
   (`isEffect_comp` with the graph lemmas). That the nodes of the first factor form a level of the
   glued diagram, with the two factors as layers, is a property of gluing and is not restated.
8. **Proposition 5.6** is an equation in `Arrow N` between `F([T ‖ S]_{(W,K)}) : F(w_S) → F(w_T)` and
   `[T ‖ S]_{(F(W),F(K))} : F(W)_S → F(W)_T`, whose sources agree up to `F(⊗ w_i) = ⊗ F(w_i)`.
   `F(K)` has the morphisms `F(κ_i)` read through that identification (`EffData.map`).
9. **Twists.** A permutation `τ` of `T` is given by the list `lT` of the elements of `T` in the order
   `τ(t_1), …, τ(t_m)`; `τ_*` is the image under `F_{(W,K)}` of the node-free diagram that connects the
   factor `i` of `w_T` with the factor `i` of `w_{τ(T)}` (`permStar`); `σ_*⁻¹` is the node-free diagram
   in the other direction, inverse to `σ_*` (`permStar_comp`).
10. **Effects in an arbitrary `M`** take `κ_i : eval(w_{S_i}) → a_i` in `M` and lift them to `str(M)`
    by fullness (`MData.κStr`); the effect is `eval([T ‖ S]_{(W,K)}) : eval(w_S) → eval(w_T)`. For strict
    `M` (with `EvalStrict`) it equals, as an arrow, the effect formed in `M` from the `a_i` and the
    `κ_i` read through `eval(w_{S_i}) = a_{S_i}` (`MData.effect_strict`).

## Proof methods differing from the paper (statements unchanged)

1. **Uniqueness (Remarks 5.2, 5.3, Definition 5.4, Lemma 5.5)** all go through one lemma, label
   coherence (`ProdSig.sameSkeleton_of_labels`), then Lemma 4.4 (`projM_map_eq_iff`). It is the
   argument of Remarks 5.2, 5.3 ("no live nodes, the origin of an edge in the codomain is the edge in
   the domain with the same value") and of the proof of Proposition 6.6 (origins forced by values,
   live nodes determined through paths of producers), proved once for all free `DD`-graph monoids in
   which each letter has at most one producer.
2. **Remark 5.3, existence.** The paper takes the product of the `ι_{w_i → w_i^{m_i}}` followed by a
   symmetry; here a selection morphism (copy the whole word, keep one factor, recurse;
   `exists_multiplier`) is used, valid in every strict Markov category.
3. **Definition 5.4, existence of an effect diagram** (`exists_effect`): by induction on
   `|V(G_{S → T}) ∖ S|`, adding a minimal vertex `v` (its parents in `S`) and using
   `V(G_{S∪{v} → T}) ∖ (S ∪ {v}) = (V(G_{S → T}) ∖ S) ∖ {v}` (`R_insert`); the paper builds the diagram
   by fusion directly.
4. **Lemma 5.5.** The graph part follows the paper. The diagram part: instead of exhibiting the level
   inside a fused diagram, the glued diagram of two effect diagrams is shown to be an effect diagram,
   which needs only `V(D) ∖ S = (A ∖ S) ⊔ B` (`R_iff_R_Ti_or`, `not_R_Ti_and`); the composite of the two
   multipliers on `w_j` is absorbed by label coherence.
5. **Proposition 5.6** by the uniqueness in Theorem 4.1 (`F ∘ F_{(W,K)} = F_{(F(W),F(K))}`) instead of
   mapping the diagram node by node; the node-by-node statement is `ProdSig.value_relabel` with
   Stage 1's preservation of values.

Steps the paper leaves to the reader that are proved here (PLAN.md, Section 6): Definition 5.4
"changing an assignment amounts to composing a multiplier with a symmetry" (subsumed by
`projM_eq_freeEffect`: every effect diagram represents the effect).

## Items from earlier stages

- Stage 3, open item 2 (the diagram of `δ_a` as one glued diagram): not needed by Stage 5, not proved;
  stays open as decided.
- Stage 3, open item 1: not touched.

## Paper feedback

None. No step of Section 5 needed a change; `formalization/PAPER-FEEDBACK.md` was not created.

## Changes outside `stage 5/`

- `lakefile.toml`: library `FreeMarkovStage5` added and made a default target.
- `scripts/verify.py`: Stage 5 added to `STAGES`.
- `formalization/blueprint/src/content.tex`: Section "Effects (Stage 5)" rewritten: nodes
  `def:5.straight`, `def:5.1`, `lem:5.labels`, `rem:5.2`, `rem:5.3`, `def:5.findag`, `def:5.4`,
  `lem:5.5`, `prop:5.6`, `def:5.twists`, `cite:C2`, `rem:5.7`, all formalized (`\lean`, `\leanok`).
- `formalization/PLAN.md`: Stage 5 record.
- No Stage 0–4 source and no manuscript file was changed. One more Mathlib module is imported
  (`Mathlib.Data.Finset.Sort`, part of the pinned Mathlib already on disk); nothing was installed and
  `lake update` was not run. Nothing committed.
