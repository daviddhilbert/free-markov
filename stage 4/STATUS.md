# Stage 4 status

Updated 2026-11-20. Plan: `formalization/PLAN.md`, Stage 4 (Sections 4, 6, 7, ground
rules 1–9). Source: Section 4 of `Free Markov - revised.tex`, from after Remark 4.2 to the
end of the section.

**State: complete.** The "Done when" line of PLAN.md holds: Lemmas 4.3, 4.4 and 4.5 are
proved, in the form used by the application (section "Use in the application" below).
Lemmas 4.3 and 4.4 and the first two items of Lemma 4.5 use no cited result; the third item
of Lemma 4.5 and the form of Lemma 4.4 in `F_s(G)/S_M` use `JoyalStreet G` (C1), through
the quotient category.

## Verification

`python3 scripts/verify.py` (2026-11-20, after all changes): **PASS**.

- `lake build FreeMarkovStage0 … FreeMarkovStage4`: exit code 0. Stage 4 builds with no
  warnings.
- `sorry` in sources: 0; `sorry` warnings in the build log: 0.
- Axioms: all 880 Stage 4 declarations (633 theorems) use only `propext`,
  `Classical.choice`, `Quot.sound`. No `axiom` declarations.
- Cited results: `FreeMarkov.JoyalStreet` occurs in the type of 11 Stage 4 theorems, all
  about `F_s(G)/S_M`: `JoyalStreet.projM_map_eq_iff` (Lemma 4.4 in the quotient) and the
  third item of Lemma 4.5 (`lemma_4_5`, `lemma_4_5_unique`, `lemma_4_5_minimal`,
  `projM_lower`, `tau_comp_eq`, `cls_tau_comp`, `isFactor_congr`, `projM_surj`,
  `projM_dwF`, `cls_comp_eqToHom`). Everything else is about diagrams and their
  `S_M`-classes and uses no cited result.
- Blueprint: 63 nodes, 128 edges, 46 formalized; labels unique, dependencies resolve,
  acyclic, every `\lean` name exists.

## Files (`stage 4/FreeMarkov/Stage4/`, 9 064 lines with the aggregator)

| File | Content |
|---|---|
| `Basic.lean` | On a polarized graph with a predicate `D` ("is a duplicate"): `Step` (consecutive edges), `exists_isPath_iff` (equivalence with Stage 1's list paths), `ReachCod`, `DupStep`, `IsRoot`, **origin** `IsOrigin` with `isOrigin_unique`, `exists_isOrigin`, `origin`; **live** `Live`, **quasi-terminal** `QuasiTerminal`, **consumer** `Consumer`; `live_iff`, `exists_consumer_of_reachCod` |
| `Skeleton.lean` | `Valuation.IsDup`, `IsDisc` (a duplicate has one input and two outputs, a discard one input and none); `Port`, `OriginAt`, `OriginsMatch`; **`SkeletonIso Γ Υ π`**, **`SameSkeleton`**; ends `PEnd`; `HasPath`, `SameStart`, **`HasSplitter`**; their description through origins of consumers (`dPath_iff_sPath`, `hasSplitter_iff`) |
| `Items.lean` | Items 2 and 3 of Lemma 4.3 from a skeleton bijection (`hasPath_iff_of_skeletonIso`, `hasSplitter_iff_of_skeletonIso`); `SameSkeleton.symm` |
| `Count.lean`, `Item1.lean` | Item 1: counting the consumers at each origin; `exists_tilde_of_skeletonIso` (the extension of `π` to `Δ̃`) |
| `StepAnalysis.lean`, `StepSkeleton.lean`, `TemplateFacts.lean` | One surgery through Stage 2's canonical description: live nodes stay live, origins of consumers are carried along, under `StepCond`; `TStep.sameSkeleton`; the Markov templates satisfy `StepCond` (`markovTemplates_stepCond`) |
| `Lemma43.lean` | **Lemma 4.3**: `lemma_4_3`, `lemma_4_3_sameSkeleton`, `skeletonIso_items`; `SameSkeleton.trans`, `Iso.sameSkeleton` |
| `Embed.lean`, `EmbStep.lean` | Embeddings `PEmb` of diagrams assembled from one-node diagrams, identities, symmetries, `⊗`, gluing; a normality criterion; `Emb.tStep` (a template whose `Ω` embeds as a normal subgraph gives a surgery) |
| `Minimal.lean`, `ExistsMinimal.lean` | **`MarkovMinimal`**; `ndCount` (nodes that are not discards) decreases under the surgeries (4.2), (4.4) at a maximal non-minimal node; `lemma_4_4_exists_minimal` |
| `Rewire.lean`, `RewireStep.lean`, `MoveSteps.lean`, `MoveFacts.lean` | Swap (4.3) and rotation (4.1) as diagrams on the same nodes and edges, recognised as surgeries (`canonProj_of_rewire`, `tStep_swap`, `tStep_rotate`); **`congTemplates`** (`T_C`); `MoveRel`: moves keep live nodes, consumers, origins and minimality |
| `Normalize1.lean`, `Normalize2.lean`, `MoveSkeleton.lean` | Normalisation of the trees of duplicates of a minimal diagram to combs sorted by a rank (`normalize`); `SkeletonIso.of_moves` |
| `CodingA.lean` … `CodingF.lean` | Leaf sets, the correspondence of consumers `ConsCorr`, codes of nodes and edges; `iso_of_sorted` (two minimal sorted combs with the same skeleton are isomorphic) |
| `Lemma44.lean` | **`MarkovCongruent`**; **Lemma 4.4**: `lemma_4_4_congruent`, `lemma_4_4_iff`, `lemma_4_4_minimal_congruent`, `lemma_4_4`; `JoyalStreet.projM_map_eq_iff` |
| `Lemma45a.lean` | **`Dead`** (the set `J`); items 1, 2 of Lemma 4.5: `lemma_4_5_path`, `lemma_4_5_dead` |
| `Lemma45b.lean`, `Lemma45c.lean` | `subword`; `livePos`, `tauPos` (the permutation `τ`); `liveW` (`a''`), `deadW` (`a'`); `tauTarget` (the diagram of `1_{a''} ⊗ ε_{a'}`), `tauRe`, `tauRe_pos` |
| `Reanchor.lean` | `reanchor` (domain reordered); `SkeletonIso.of_reanchor`; `permNF` (node-free diagram of a permutation); **`glueNodeFreeIso`**: gluing `permNF` on the left reorders the domain |
| `TensorSkel.lean` | The notions of Section 4 in `Υ ⊗ Ω`; `SameSkeleton.of_tensor` (cancelling a disjoint union with discards) |
| `DeadLevel.lean` | For a minimal diagram: `deadL` (the discards at the dead inputs) is a level (`isLevel_deadL`) with cut `deadEnum`; `sameSkeleton_lower`, `not_dead_upper` |
| `Lemma45.lean` | `tauM` (`τ` in `F_s(G)/S_M`), `IsFactor`; `lemma_4_5_unique`, `lemma_4_5_minimal`; **Lemma 4.5**: `JoyalStreet.lemma_4_5` |

## Statements against the paper

| Paper | Lean |
|---|---|
| quasi-terminal, `Δ_Γ`, `Δ̃_Γ` | `PGraph.QuasiTerminal` (`Diagram.QuasiTerminal`); `Δ̃_Γ` as `{x // ¬ Γ.QuasiTerminal x}` |
| splitter path | `AGraph.HasSplitter` (with `SameStart`) |
| origin `e°` | `PGraph.IsOrigin q e`; it exists and is unique (`exists_isOrigin`, `isOrigin_unique`), `origin` is the function |
| live node, consumer | `PGraph.Live`, `PGraph.Consumer` (`Diagram.Live`, `Diagram.Consumer`); "in other words" is `live_iff` |
| have the same skeleton (via `π`) | `Diagram.SameSkeleton Γ Υ` = same domain, same codomain, `∃ π, SkeletonIso Γ Υ π` |
| **Lemma 4.3**: same class ⇒ same skeleton, and the three items | `Diagram.lemma_4_3` (hypothesis `SRel G.markovTemplates [Γ] [Υ]`) |
| Markov minimal | `Diagram.MarkovMinimal` |
| Markov congruent | `Diagram.MarkovCongruent` (`SRel G.congTemplates`) |
| **Lemma 4.4**, four claims | `Diagram.lemma_4_4` (`lemma_4_4_exists_minimal`, `lemma_4_4_congruent`, `lemma_4_4_iff`, `lemma_4_4_minimal_congruent`) |
| **Lemma 4.5**, `J`, `a'`, `a''`, `τ` | `Diagram.Dead`, `deadW`, `liveW`, `JoyalStreet.tauM` |
| Lemma 4.5, items 1, 2 | `Diagram.lemma_4_5_path`, `Diagram.lemma_4_5_dead` |
| Lemma 4.5, item 3 (unique `g`; "moreover") | `JoyalStreet.lemma_4_5` (third and fourth conjuncts) |

## Readings fixed in Stage 4 (within the plan; no formal statement departs from the paper)

1. **Quasi-terminal.** "Every maximal directed path `p` with `p(0) = x` ends at a terminal
   node" is read as "no directed path from `x` ends in `cod(Γ)`": a maximal directed path
   ends at a terminal node or at an outer node, and an outer node at the end of a path is
   in `cod(Γ)`. For a duplicate, "this is so for all such paths through one of the prongs"
   is "one output reaches no edge of `cod(Γ)`".
2. **Directed paths** are chains of consecutive edges (`Step`); "ends in `cod(Γ)`" is
   `ReachCod`. The ends of the paths in Lemma 4.3 are `PEnd`: a node, or the `i`-th edge of
   the domain (at the start) or of the codomain (at the end); paths are Stage 1's nonempty
   edge lists (`HasPath`), equivalent to the chains (`exists_isPath_iff`).
3. **Splitter paths**: two directed paths with the same start, i.e. the same source node,
   or the same first edge when it is an edge of the domain (`SameStart`); the paper's
   `p(0) = p'(0)` at an outer node means the same edge of the domain.
4. **Origin** as a relation `IsOrigin q e` (following `e` backward through duplicates ends
   at `q`, whose source is not a duplicate), with existence and uniqueness proved; the
   function `e ↦ e°` is `origin`.
5. **Same skeleton** includes "the same domain and the same codomain" as equality of the
   words `domWord`, `codWord`. The origins match at *ports*: `OriginAt e (.dom j)` ("`e°` is
   the `j`-th edge in `dom(Γ)`") and `OriginAt e (.out y j)` ("the `j`-th output of `y`").
6. **Lemma 4.3, item 1**: `π` extends to `π' : Δ̃_Γ ≃ Δ̃_Υ` compatible with the
   valuations, and `π'` agrees with `π` on live nodes. Items 2 and 3 are stated for all
   ends that are live nodes or positions of edges, with `π` applied to the node ends
   (`liftEnd`).
7. **Markov congruent**: "become isomorphic upon surgeries with the templates (4.1),
   (4.3)" is the congruence of Stage 2 for the set `T_C` of (4.1), (4.3), their reverses and
   the empty template (`SRel G.congTemplates`), the same construction as `S_M` for `T_M`.
8. **Lemma 4.4, first claim**: the minimal diagram is produced with `Fin` node and edge
   types (`DClass` representatives), and "contains" is `SRel G.markovTemplates c [Υ]`.
9. **Lemma 4.5.** `J` is `Γ.Dead : ℕ → Prop` (positions of the domain). `a''`, `a'` are the
   subwords at the positions outside and inside `J` (`liveW`, `deadW`). `τ` is the class of
   the node-free diagram of the permutation "positions outside `J`, then those in `J`, each
   in increasing order" (`tauPos`); in `F_s(G)` the symmetries are exactly the classes of
   node-free diagrams, and this is the one described. `[Γ]/S_M` is `J.projM.map f` for a
   morphism `f : a → b` of `F_s(G)` with `J.cls f = [Γ]`. The equation is written with the
   unit law `b ⊗ 1 = b` as `eqToHom (mul_one _)` (`IsFactor`). "In every diagram that
   represents `g`": every `Υ` with `J.cls h = [Υ]` and `J.projM.map h = g` for some
   `h : a'' → b` of `F_s(G)`. Item 2 is stated as: `SRel G.markovTemplates [Γ] [Υ]` implies
   `Γ.Dead j ↔ Υ.Dead j` for every `j`.

## Proof methods differing from the paper (statements unchanged)

1. **Lemma 4.3.** "`Γ` and `Υ` have the same live nodes" is proved as: the live nodes of
   `Γ` lie outside the image of `Ω` and stay live in `Υ` (an injection), and the reverse
   surgery gives an injection the other way; finiteness gives the bijection. The surgery is
   read through Stage 2's canonical description (`CanonProj`).
2. **Lemma 4.4, first claim**: as in the paper (a surgery at a maximal non-minimal node
   lowers the number of nodes that are not discards); the surgery is obtained by embedding
   the template diagram as a normal subgraph (`PEmb`, `Emb.tStep`).
3. **Lemma 4.4, second claim.** The paper moves a given leaf to the root and inducts on the
   number of leaves. Here the swaps (4.3) and rotations (4.1) are rewirings on the same nodes
   and edges; every tree is normalised to a comb sorted by a rank (two phases, each with a
   measure), and two minimal sorted combs with the same skeleton are isomorphic by coding
   their nodes and edges through live nodes, ports and consumers (`iso_of_sorted`).
4. **Lemma 4.5, third item, existence.** The paper says "`g = [Γ'']/S_M` is as required".
   Here: the dead inputs of a minimal `Γ` end at discards, which form a level `deadL`;
   Remark 2.4 gives `[Γ] = [Γ[deadL, Γ̇]] ∘ [Γ[∅, deadL]]`; the lower layer has the skeleton
   of `(1_{a''} ⊗ ε_{a'}) ∘ τ` (`sameSkeleton_lower`), hence the same class by Lemma 4.4;
   `Γ'' = Γ[deadL, Γ̇]` has no dead input (`not_dead_upper`). **Uniqueness** as in the paper:
   `Υ ⊗ (ε_{a'_1} ⊗ ⋯)` glued after `τ` is `Υ ⊗ ⋯` with its domain reordered
   (`glueNodeFreeIso`), skeletons are unchanged by the reordering (`SkeletonIso.of_reanchor`)
   and the discards can be cancelled (`SameSkeleton.of_tensor`).

Steps the paper leaves to the reader that are proved here (PLAN.md, Section 6): Lemma 4.3
"may be rerouted" (live nodes and origins before and after each template, `StepCond`);
Lemma 4.4 "determined, up to isomorphisms, by its skeleton and the shapes of these trees"
(`iso_of_sorted`) and the connection of trees by (4.1), (4.3) (`normalize`).

## Items from earlier stages

- Stage 3, open item 1 ((1.3) by induction on inner nodes): not added; Stage 4 did not need
  it. Stage 3's proof by generation stands (accepted by the coordinator).
- Stage 3, open item 2 (the diagram of `δ_a` as one glued diagram): not needed by Stage 4,
  not proved; stays open as decided.

## Paper feedback

None. No step of Section 4 after Remark 4.2 needed a change;
`formalization/PAPER-FEEDBACK.md` was not created.

## Changes outside `stage 4/`

- `lakefile.toml`: library `FreeMarkovStage4` added and made a default target.
- `scripts/verify.py`: Stage 4 added to `STAGES`.
- `formalization/blueprint/src/content.tex`: nodes `def:4.skeleton`, `lem:4.3`,
  `def:4.minimal`, `lem:4.4`, `lem:4.5` formalized (with `\lean`, `\leanok` and proof
  sketches; `lem:4.5` now also uses `rem:2.4` and `def:4.words`).
- `formalization/PLAN.md`: Stage 4 record.
- No Stage 0–3 source and no manuscript file was changed. Nothing was installed; `lake
  update` was not run. Nothing committed.
