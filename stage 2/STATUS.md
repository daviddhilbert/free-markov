# Stage 2 status

Updated 2026-11-20. Plan: `formalization/PLAN.md`, Stage 2 (Sections 4, 6, 7, ground
rules 1–9). Source: Section 3 of `Free Markov - revised.tex` (surgeries on diagrams).

**State: complete.** The "Done when" line of PLAN.md holds: Corollary 3.5 is proved
(`FreeMarkov.cor_3_5`) and the quotient category `F_s(G)/S_T` is constructed
(`JoyalStreet.Quot` with `Category` and `StrictSMC` instances, projection
`JoyalStreet.quotProjStrict`).

## Verification

`python3 scripts/verify.py` (2026-11-20): **PASS**.

- `lake build FreeMarkovStage0 FreeMarkovStage1 FreeMarkovStage2`: exit code 0; Stage 2
  builds with no warnings.
- `sorry` in sources: 0; `sorry` warnings in the build log: 0.
- Axioms: all 634 Stage 2 declarations (382 theorems) use only `propext`,
  `Classical.choice`, `Quot.sound`. No `axiom` declarations.
- Cited results: `FreeMarkov.JoyalStreet` occurs in the type of 23 Stage 2 theorems, all
  about `S_T` as a congruence, the quotient and Corollary 3.5 (`Congruence.lean`,
  `Quotient.lean`, `Cor35.lean`). Definition 3.1, Lemma 3.2, the surgery, its
  properties, and Lemma 3.3 use no cited result.
- Blueprint: 59 nodes, 111 edges, 34 formalized; labels unique, dependencies resolve,
  acyclic, every `\lean` name exists.

## Files (`stage 2/FreeMarkov/Stage2/`, 5 277 lines)

| File | Content |
|---|---|
| `Paths.lean` | Order on nodes; `Reach e e'` (`e(1) ≤ e'(0)`); two distinct edges lie on a directed path in this order iff `Reach` (`reach_of_mem_path`, `exists_path_of_reach`); paths through a node; ends of the edges of a path |
| `Normal.lean` | `Subgraph`; `LooseIn`, `flat` (`Γ'^♭`), `EdgeAt`; **Definition 3.1** `IsNormal`; the two observations; **Lemma 3.2** `isNormal_iff`; `sharpL`, `sharpM`, `sharp` (`Γ'^♯`); `ValidLayer` (a layer as in Lemma 3.2) and the facts `cut(L) = dom(Γ') ⊎ R`, `cut(M) = cod(Γ') ⊎ R` |
| `Gluing.lean` | `PDiagram` (diagrams that are not anchored) and their isomorphisms; enumerations transported along bijections (`mapEquiv`), images, `ofFinite`; `addLoose` (`Λ ⊎ R`), `liftDom`/`liftCod` (`α ⊎ id`); `glueCodEquiv`; the three-piece gluing `three m₁ m₂` with the edge maps `rA`, `rK`, `rC`, its anchored and valued versions `threeA`, `Diagram.three`; order and ends of edges in glued graphs; the comparison principle `PGraph/AGraph/Diagram/PDiagram.Iso.ofProj` |
| `Surgery.lean` | `R`, `edgeOf`, `domMatch`, `codMatch` (`φ` and the identity on `R`), the gluing bijections `m₁`, `m₂` (`φ ∘ α`, `φ ∘ β`); **the surgery** `AGraph.surgeryAt`/`surgery` and `Diagram.surgeryAt`/`surgery` (fused valuation `v_w`); `alphaSharp`, `betaSharp` and the natural anchoring; `v_w = v ∘ α^♯`, equal domain and codomain words |
| `Canonical.lean` | `isoMid` (isomorphic middle pieces); `decompAt`, `isoDecomp` (`Γ ≅ Γ[∅,L] ∘ (Ω ⊎ R) ∘ Γ[M,Γ̇]`); `CanonProj`, `canonProj`: the canonical description of the result of a surgery for any three-piece decomposition |
| `Recognition.lean` | **independence of the layer** `surgeryAt_iso`; `surgeryAt_iso_self` (an isomorphism `Λ → Ω` inducing `α`, `β`); `recognition` ("if" half of Lemma 3.3 for diagrams); **reversibility** `surgeryAt_reverse`; `surgeryAt_of_iso` |
| `Lemma33.lean` | Enumeration calculus; `threeIsoGlue`, `mk_three` (three-piece gluing along matchings of orderings = composite of classes); `mk_eq_decomp`, `mk_surgeryAt_eq_decomp` ("only if", class form); `classRecognition` ("if", class form); `layerIso` (`Γ'^♯ ≅ Ω ⊎ R`); **Lemma 3.3** `lemma_3_3` |
| `Templates.lean` | **Definition 3.4**: `Template`, `Template.symm`, `Template.empty`, `Template.IsSymmetric`, `TStep` (`T`-surgery), `TEquiv` (`T`-equivalence); the empty surgery; invariance and symmetry of steps; `SRel` (`S_T`) and its equivalence |
| `GraphLevel.lean` | The statements for graphs without valuations (shape valuation): `AGraph.surgeryAt_iso_self`, `AGraph.surgery_iso_self`, `AGraph.surgery_empty_iso` |
| `Congruence.lean` | Orderings of `K ⊎ (R ⊕ R')`; `tensorIdIso`, `idTensorIso` (`Ω^♯ ⊗ 1 = Ω ⊎ (R ⊕ b)`); C1 laws on classes (`cls_assoc`, `cls_interchange`, `cls_comp_id`, `cls_id_comp`); `TDecomp` (class form of a `T`-step) and its stability under `⊗`, `∘` |
| `Quotient.lean` | **`S_T` is a monoidal congruence** (`SRel.tensor`, `SRel.comp`); **the quotient** `JoyalStreet.Quot` with `quotCategory`, `quotStrictSMC`, `quotProj`, `quotProjStrict`, `quotProj_map_eq_iff` |
| `Cor35.lean` | `plusIso` (`[Ω ⊎ R] = [Ω] ⊗ [R]`), `addLooseEmptyIso`; **`E_T`** `ERel`; **Corollary 3.5** `cor_3_5` |

## Statements against the paper and the plan

| Paper | Lean |
|---|---|
| Definition 3.1 (normal subgraph), `Γ'^♭` | `PGraph.IsNormal`, `Subgraph`, `PGraph.flat` |
| Observations after Definition 3.1 | `PGraph.flat_eq_of_edgeAt`, `IsNormal.isInitial`, `IsNormal.isTerminal` |
| Lemma 3.2 | `PGraph.isNormal_iff` (`isNormal_of_layer`, `isNormal_iff_nonempty_validLayer`) |
| `Γ'^♯` | `PGraph.sharp`, `IsNormal.sharpLayer` |
| `R`, `cut(L) = dom(Γ') ⊎ R`, `cut(M) = cod(Γ') ⊎ R` | `ValidLayer.R`, `ValidLayer.domMatch`, `codMatch` (bijections), `cut_L_of_dom`, `cut_M_of_cut_L`, … |
| `Λ^♯ = Λ ⊎ R` | `PGraph.addLoose`, `PDiagram.addLoose` |
| The surgery `Γ^Ω_Λ(φ, α, β)`, "more precisely" paragraph | `AGraph.surgery` (`surgeryAt` for any layer as in Lemma 3.2), built with `PGraph.three` |
| No directed circuit | built in (`PGraph.glue` is a `PGraph`) |
| `α^♯`, `β^♯`, naturally anchored | `AGraph.alphaSharp`, `betaSharp`, `surgeryAt_dom`, `surgeryAt_cod` |
| Isomorphism `Λ → Ω` inducing `α`, `β` gives `Γ` | `AGraph.surgery_iso_self` (graphs), `Diagram.surgeryAt_iso_self` (diagrams) |
| Empty template gives `Γ` | `AGraph.surgery_empty_iso`, `Diagram.surgery_empty_iso` |
| The surgery on diagrams, `v_w`, `dom`, `cod` | `Diagram.surgery`, `surgeryAt_v₀_dom`, `surgeryAt_v₀_cod`, `surgeryAt_domWord`, `surgeryAt_codWord` |
| A surgery can be reversed | `Diagram.surgeryAt_reverse` |
| Lemma 3.3 | `Diagram.lemma_3_3` |
| Independence of the layer (proof of Lemma 3.3) | `Diagram.surgeryAt_iso`, `surgery_iso_surgeryAt` |
| Definition 3.4: templates, symmetric set, `T`-surgery, `T`-equivalence | `Template`, `Template.IsSymmetric`, `Diagram.TStep`, `TEquiv` |
| "`[Γ] = [Υ]`, … then clearly `Υ ⇝_T Υ'`" | `SRel.mk_iff`, `TStep.iso_left`, `TStep.iso_right`, `TEquiv.iso_left`, `TEquiv.iso_right` |
| `S_T` monoidal congruence | `SRel.equivalence`, `SRel.tensor`, `SRel.comp` |
| `F_s(G)/S_T` symmetric strict monoidal | `JoyalStreet.Quot`, `quotCategory`, `quotStrictSMC`, `quotProjStrict` |
| `E_T` | `ERel` |
| Corollary 3.5 | `cor_3_5` |

## Readings fixed in Stage 2 (within the plan; none departs from the paper)

1. **Subgraphs** are pairs of predicates (`Subgraph`); their graph is Stage 1's
   `Γ.sub`. "Loose in `Γ'`" for an edge of `Γ'` is `LooseIn` (neither end in `Γ'₀`),
   equal to `(Γ.sub P Q).IsLoose` (`sub_isLoose_iff_looseIn`). "A directed path belongs
   to `Γ'`": its edges and the nodes it passes through are in `Γ'`.
2. **Lemma 3.2.** The layer is required to be between levels `L ⊆ M` (layers are only
   defined so). In the "if" half, "deleting loose edges from a normal subgraph leaves it
   normal" is read as deleting *any set* of loose edges, which covers every `Γ'` between
   `Γ[L, M]^♭` and `Γ[L, M]` (same nodes); `isNormal_of_layer` proves the three
   conditions directly.
3. **The surgery** is constructed for every layer `Γ[L, M]` as in Lemma 3.2
   (`surgeryAt`); the paper's surgery uses `Γ'^♯` (`surgery`). This is the construction
   of the "more precisely" paragraph read literally, with the generality that the proof
   of Lemma 3.3 needs. `R` is the set of edges cut by `L` and `M` not in `Γ'`, which is
   the set of loose edges of `Γ[L, M]` not in `Γ'`.
4. **Templates** have `Ω`, `Λ` as diagrams that are not anchored (`PDiagram`), with
   finite node and edge types in a universe `u` (`Template.{u} G`); `α : dom(Λ) → dom(Ω)`,
   `β : cod(Λ) → cod(Ω)` with the labels agreeing along them. The isomorphism
   `φ : (Ω, u) → (Γ', v')` is an isomorphism of `PDiagram`s onto `Γ.subD A _` (the
   restriction `v'`). "Symmetric set that contains the empty one" is
   `Template.IsSymmetric` (`Template.empty ∈ T` and closure under `Template.symm`).
5. **`T`-equivalence** is defined, as in Definition 3.4, by chains of `T`-surgeries,
   with the diagrams of the chain represented on `Fin` types (`FinDiag`, D3);
   `SRel T` (`S_T`) is the relation on classes. Iso-invariance of a step on both sides
   (`TStep.iso_left`, `iso_right`) and the empty template make the choice of
   representatives irrelevant (`SRel.mk_iff`).
6. **Morphisms of `F_s(G)` in Lemma 3.3** are classes with the matching domain and
   codomain words, and composites are taken in the bracketing `h ∘ (X ∘ g)`
   (`(g.comp X).comp h`), which needs no associativity, so Lemma 3.3 holds without C1.
   Order preservation is stated as "`φ ∘ α ⊎ id` carries the ordering of `dom(Λ^♯)` to
   that of `cut(L)`", and similarly for codomains.
7. **`E_T`** is the inductive relation generated by the template pairs, closed under
   reflexivity, symmetry, transitivity, `⊗` and `∘` of related pairs; "compatible with
   `α`, `β`" means `α` carries the ordering of `dom(Λ)` to that of `dom(Ω)` (`β` likewise).
   It relates parallel morphisms only (`ERel.dom_eq_cod_eq`).
8. **Use of C1.** `S_T` being a congruence uses associativity and the interchange law of
   `F_s(G)` (via `JoyalStreet`), as the paper's "easy to see" does; so do the quotient
   category and Corollary 3.5. The quotient is built as in Stage 0's `Syn_s(G)`: hom-sets
   are plain quotients, the laws are transported along the projection functor.
9. **Graph-level statements** (isomorphism `Λ → Ω` inducing `α, β`; empty template) are
   deduced from the diagram-level ones through the shape valuation in a fixed free
   graph monoid (`GraphLevel.lean`); the surgery on the valued diagram has the surgery on
   the graph as its anchored graph by definition (`surgeryAt_shape`, `rfl`).

Steps the paper leaves to the reader that are proved here (PLAN.md, Section 6): the
observations after Definition 3.1; "clearly there are induced bijections" `α^♯`, `β^♯`
and the absence of directed circuits; reversibility; independence of the layer (the
longest part, via the canonical description `CanonProj`); "clearly" iso-invariance of
`T`-equivalence and "easy to see" compatibility with `⊗` and `∘`; both inclusions of
Corollary 3.5.

## Paper feedback

None. No step of Section 3 needed a change; `formalization/PAPER-FEEDBACK.md` was not
created.

## Changes outside `stage 2/`

- `lakefile.toml`: library `FreeMarkovStage2` added and made a default target.
- `scripts/verify.py`: Stage 2 added to `STAGES`.
- `formalization/blueprint/src/content.tex`: Section 3 nodes rewritten (Definition 3.1,
  observations, Lemma 3.2 with `Γ'^♯`, the surgery, structure of a surgery, Lemma 3.3,
  Definition 3.4, `S_T` congruence and quotient, `E_T`, Corollary 3.5).
- `formalization/PLAN.md`: Stage 2 record.
- No Stage 0 or Stage 1 source and no manuscript file was changed. Nothing was installed;
  `lake update` was not run. Nothing committed.

## Open items (recorded, not blocking)

- The author's review of the statement of `JoyalStreet` (Stage 1, PLAN risk 5) is still
  open; in Stage 2 only the congruence, the quotient and Corollary 3.5 depend on it.
