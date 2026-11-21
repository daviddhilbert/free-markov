# Stage 1 status

Updated 2026-11-20. Plan: `formalization/PLAN.md`, Stage 1, with D1, D3, D4 and
ground rules 1–9. Source: Section 2 of `Free Markov - revised.tex`.

**State: complete.** The "Done when" line of PLAN.md holds: the layer
decomposition (Remark 2.4) is proved, and Theorem 2.3 is available under the
hypothesis `FreeMarkov.JoyalStreet G` together with its two derived principles
(generation, value of a diagram).

## Verification

`python3 scripts/verify.py` (2026-11-20): **PASS**.

- `lake build FreeMarkovStage0 FreeMarkovStage1`: exit code 0; each Stage 1 file
  compiled on its own with no warnings.
- `sorry` in sources: 0; `sorry` warnings in the build log: 0.
- Axioms: all 529 Stage 1 declarations (256 theorems) use only `propext`,
  `Classical.choice`, `Quot.sound`. No `axiom` declarations.
- Cited results: `FreeMarkov.JoyalStreet` occurs in the type of 43 theorems, all in
  `JoyalStreet.lean` and `Value.lean` (the laws of `F_s(G)`, Theorem 2.3,
  generation, values). It does not occur in the layer files or in Remark 2.4.
- Blueprint: 55 nodes, 104 edges, 24 formalized; labels unique, dependencies
  resolve, acyclic, every `\lean` name exists.

## Files (`stage 1/FreeMarkov/Stage1/`)

| File | Content |
|---|---|
| `Graph.lean` | `PGraph` (polarized progressive graphs as incidence data, D1), `AGraph` (anchored), `Enumeration` (a total ordering of a set of edges as a duplicate-free list) and position-by-position `matching`; pinned, half-loose, loose, `IsDom`, `IsCod`, initial, terminal; `PGraph.Iso`, `AGraph.Iso` (refl, symm, trans; `src_map`, `tgt_map` derived); transport along bijections |
| `Diagram.lean` | `Valuation` (in a free graph monoid), `Diagram`, `domWord`, `codWord`, `Diagram.Iso`; `toFin`, `FinDiag`, `DClass` (classes through `Fin` representatives, D3), `DClass.mk`, `mk_eq_mk_iff`, `DHom G a b`; `CValuation`, `CDiagram`, `domObj`, `codObj` (Definition 2.1 for a strict monoidal `C`); `graphOf C` (= `G_C`), `CDiagram.toFree` |
| `Operations.lean` | Disjoint union (`PGraph/AGraph/Diagram.tensor`); gluing along a bijection `cod(Γ) → dom(Ω)` (`PGraph.glue`, `glueIn`, `glueTgt`), anchored gluing (`AGraph.glue`, `Diagram.glue`), `Valuation.glue`; domain and codomain words |
| `Classes.lean` | Invariance of gluing and disjoint union under isomorphism; node-free diagrams (`nodeFree`, `idD`, `permD`, `braidD`), one-node diagrams (`oneNode`); `DClass.comp`, `DClass.tensor`, `DHom.comp/tensor/id/braid/gen` |
| `JoyalStreet.lean` | `JoyalStreet G` (cited result C1, D4); the laws of `F_s(G)`; `JoyalStreet.Fs` with `Category` and `StrictSMC` instances; strict isomorphisms `Syn_s(G) ⇄ F_s(G)`; `IsFreeSymmetric`; **Theorem 2.3** `JoyalStreet.isFreeSymmetric`; generation `JoyalStreet.induction` |
| `Value.lean` | Relabelling of diagrams and classes; naturality of C1 under relabelling (`val_synMap`, by generation); `evalHom`, `valueFree`, `CDiagram.value`; `valueFree_oneNode`; preservation by strict functors (`StrictFunctor.map_valueFree`, `CDiagram.map_value`) |
| `Layers.lean` | Directed paths, `Lt`/`Le`, `lt_iff_exists_path`, `nodeOrder` (a `PartialOrder`), `IsLevel` (= lower set), `Cut`, `sub` (subgraphs) and their pinned/loose edges and inherited orderings, `layer`, the layer facts; `Valuation.restrict`, `Diagram.layerD` (anchored layers) |
| `Decomposition.lean` | `glueLayersIso` (gluing `Γ[L,M]` and `Γ[M,K]` gives `Γ[L,K]`), `isoWholeLayer`, `mk_eq_comp_lower_upper`, **Remark 2.4** `remark_2_4`, `remark_2_4'` |

## Statements against the paper and the plan

Every item of PLAN.md, Stage 1, has a declaration:

| Paper | Lean |
|---|---|
| Graphs, nodes, edges, pinned/half-loose/loose, `inn`, `out`, initial, terminal, `dom`, `cod`, anchored | `PGraph`, `AGraph`, `PGraph.IsPinned`, `IsHalfLoose`, `IsLoose`, `ins`, `outs`, `IsInitial`, `IsTerminal`, `IsDom`, `IsCod`, `AGraph.dom/cod` |
| Definition 2.1 (valuations in `C` and in `G`, diagrams, isomorphisms, domain, codomain) | `CValuation`, `CDiagram`, `CDiagram.domObj/codObj`, `Valuation`, `Diagram`, `Diagram.domWord/codWord`, `Diagram.Iso` |
| Composition, product, identities, symmetries of `F_s(G)` | `Diagram.glue`, `Diagram.tensor`, `idD`, `braidD` (`permD` in general), `oneNode`; on classes `DHom.comp/tensor/id/braid/gen` |
| Theorem 2.3 and "freeness is understood as in the Introduction" | `JoyalStreet`, `JoyalStreet.Fs`, `JoyalStreet.isFreeSymmetric`, `JoyalStreet.induction` |
| Value of a diagram (PLAN.md, Section 2) | `CDiagram.value`, `valueFree`, `CDiagram.map_value` |
| Directed paths, `x < y`, `Γ̇`, levels, `cut(L)` | `IsPath`, `Lt`, `lt_iff_exists_path`, `nodeOrder`, `IsLevel`, `isLevel_iff_isLowerSet`, `Cut` |
| `cut(∅) = dom(Γ)`, `cut(Γ̇) = cod(Γ)`, loose edges cut by every level | `cut_empty_iff`, `cut_univ_iff`, `cut_of_isLoose` |
| Subgraphs; pinned iff both ends in `Γ'₀`, loose iff neither; inherited orderings | `sub`, `sub_isPinned_iff`, `sub_isLoose_iff`, `sub_ins_sublist`, `sub_outs_sublist` |
| Layers `Γ[L, M]`; `dom = cut(L)`, `cod = cut(M)`, loose = `cut(L) ∩ cut(M)`, `dom(Γ) = dom(Γ[∅, L])`, `cod(Γ) = cod(Γ[L, Γ̇])` | `layer`, `mem_layerEdge_iff`, `layer_isDom_iff`, `layer_isCod_iff`, `layer_isLoose_iff`, `layer_empty_isDom_iff`, `layer_univ_isCod_iff` |
| Remark 2.4 | `Diagram.remark_2_4`, `remark_2_4'` |
| Remark 2.2 | not formalized (comparison only; PLAN.md, Section 2) |

## Readings fixed in Stage 1 (within the plan; none departs from the paper)

1. **Graphs (D1).** An outer node is attached to exactly one edge end, so it is
   represented by `none` as the source or target of that edge. Pinned, half-loose
   and loose are defined from these (both ends inner, exactly one, none). A
   directed circuit passes through inner nodes only, so "no directed circuit" is
   the irreflexivity of the transitive closure of node adjacency.
2. **Orderings** of `inn(x)`, `out(x)`, `dom`, `cod`, `cut(L)` are duplicate-free
   lists enumerating the set (`Enumeration`).
3. **Gluing** is defined for polarized graphs along any bijection
   `cod(Γ) → dom(Ω)`; the composition of `F_s(G)` is the case where the bijection
   matches the orderings position by position. The glued graph keeps the edges of
   `Γ` and the edges of `Ω` with an inner source (a domain edge of `Ω` is identified
   with its matched codomain edge of `Γ`). Stage 2's three-piece surgery can use
   `PGraph.glue` directly.
4. **Classes (D3).** `DClass G` is the quotient of diagrams on `Fin n`, `Fin m` by
   isomorphism, in `Type (max w v)` like `Syn_s(G)`; `DClass.mk Γ` takes the class of
   a diagram on any finite types in any universe. `DHom G a b` is the subtype of
   classes with domain `a` and codomain `b` (rather than a quotient of a subtype), so
   no cast enters the data. `DClass.comp c d` is total; when `cod c ≠ dom d` its value
   is `c` by convention and is never used (`DHom.comp` requires the match).
5. **C1 (D4).** `JoyalStreet G` has exactly the fields listed in D4: for all words
   `a, b` an `Equiv` between `Syn.of G a ⟶ Syn.of G b` and `DHom G a b`, sending
   `Syn.gen x` to the one-node diagram, `𝟙` and `σ` to the node-free diagrams,
   `≫` to gluing and `⊗` to disjoint union. Everything else about `F_s(G)` is proved
   from it: the category and strict symmetric monoidal laws (transported along the
   bijection), freeness, generation, and the naturality used for values.
6. **Theorem 2.3** is `IsFreeSymmetric J.Fs G J.ι`, with the target universes as
   free parameters (as for `IsFreeMarkov` in Stage 0). `F_s(G)` is `JoyalStreet.Fs J`:
   objects the words, morphisms `DHom G a b`, operations those of Section 2.
7. **Values.** The value of a diagram in `C` is `Syn.lift` of the evaluation
   `G_C → C` applied to the morphism of `Syn_s(G_C)` that C1 assigns to its class.
   "A strict functor preserves values" is `CDiagram.map_value`, an equation in
   `Arrow D` because `F(⊗ᵢ aᵢ)` and `⊗ᵢ F(aᵢ)` are only propositionally equal; `F_*Γ`
   applies `F` to the labels, with the node labels retyped by `eqToHom`.
8. **Layers.** The edge set of `Γ[L, M]` is defined as "source outer or in `M`,
   target outer or outside `L`", and `mem_layerEdge_iff` proves it equal to the
   paper's description (pinned edges inside `M ∖ L`, and `cut(L) ∪ cut(M)`) when
   `L ⊆ M`. The facts `dom Γ[L, M] = cut(L)`, `cod Γ[L, M] = cut(M)` hold for any
   `L ⊆ M`; that `L` and `M` are levels is used only to restrict the valuation
   (every edge at a node of the layer lies in the layer).
9. **Remark 2.4** is proved in the strong form of PLAN.md: for levels `L ⊆ M` and
   *every* pair of total orderings of `cut(L)` and `cut(M)` (with `dom(Γ)`, `cod(Γ)`
   at the two ends), as an equation of classes, in both bracketings, and without C1.
   The paper's convention ("the partial orderings may be extended to compatible
   total orderings so as to make the equality hold") follows.

Steps the paper leaves to the reader that are proved here: `cut(∅) = dom`,
`cut(Γ̇) = cod`, the layer facts, the inherited polarization of subgraphs, the
partial order on nodes, "this is a strict partial ordering", invariance of gluing
and disjoint union under isomorphism, and Remark 2.4.

## Paper feedback

None. No step of Section 2 needed a change.

## Changes outside `stage 1/`

- `lakefile.toml`: library `FreeMarkovStage1` added and made a default target.
- `scripts/verify.py`: Stage 1 added to `STAGES`.
- `formalization/blueprint/src/content.tex`: Section 2 nodes rewritten (graphs,
  Definition 2.1, operations, C1, Theorem 2.3, value, preservation of values, layers,
  facts about layers, Remark 2.4).
- `formalization/REUSE-SURVEY.md`: the focused search before Stage 1 proofs.
- `formalization/PLAN.md`: Stage 1 record.
- No Stage 0 source and no manuscript file was changed. Nothing was installed;
  `lake update` was not run. Nothing committed.

## Item for the author: review of the statement of `JoyalStreet` (closed)

Closed 2026-11-20. The coordinating session compared the statement with
Joyal–Street, Chapter 2 (§2, Theorem 2.3; Chapter 1, Definition 1.5 and the proof of
Theorem 1.2), and compared the Lean definitions of diagrams, isomorphisms, classes,
gluing, disjoint union, the node-free diagrams and the one-node diagrams line by line
with Section 2 of the paper; no mismatch. The author read the statement in
mathematical form and accepted it. Two points are part of what is assumed: the
strict unique factorization comes from Joyal–Street's proof (their Definition 2.1 of
freeness is an equivalence of categories), and their graphs are topological while
ours are combinatorial.

Original record:

PLAN.md risk 5 and the Stage 0 hand-over ask that the author review the statement of
`JoyalStreet` before proofs build on it. Following ground rule 9 the stage went
ahead; the statement is item 5 above and the structure at the top of
`JoyalStreet.lean`. If the author changes it, only `JoyalStreet.lean` and
`Value.lean` depend on it.
