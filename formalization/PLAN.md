# Formalization plan: A graphical construction of free Markov categories

Drawn up 2026-11-20. Source text: `Free Markov - revised.tex` (24 pages, the clean
version of the revised manuscript). Statement numbers below are those of that file.

This is a plan only. No Lean code exists yet. The work is to be done one section
at a time, in separate sessions.

**Approved by the author on 2026-11-20:** the recommended defaults for D1
(combinatorial diagrams), D6 (strict version of Section 5 as primary), D7
(target of Theorem 6.7), the package pins of D5, and the advertised results.
Each stage has its own folder in the project folder, `stage 0` to `stage 7`,
and is carried out in the session named after it.

## 1. Ground rules

1. **One section per stage.** A stage is finished only when every numbered
   statement of that section has a Lean declaration, the library builds, and
   there is no `sorry`.
2. **Cited results are given.** Results the paper cites are not proved. They enter
   as explicit hypotheses (fields of a structure passed to the theorems), never
   as `axiom` declarations, so that the axiom report stays at `propext`,
   `Classical.choice`, `Quot.sound` and every use of a cited result is visible
   in the type of the theorem that uses it. Section 2 lists them.
3. **Everything the paper proves is proved**, including the steps it calls
   clear, easy or routine. Section 6 lists those steps.
4. **Statements before proofs.** Each stage starts with an independent reading
   of the section, then a file of Lean definitions and theorem statements with
   docstrings quoting the paper number. Proofs follow; a statement that departs
   from the paper or this plan is put to the author as a decision first.
8. **Existing work.** `formalization/REUSE-SURVEY.md` records the search of
   Mathlib, its pull requests, Tau Ceti, Lean Pool, Reservoir, Palomar and
   GitHub made on 2026-11-20. Nothing covering the paper was found; what was
   found is used as stated in D2, D4 and D5 below. A focused search is repeated
   before Stage 1 proofs and before Stage 7.

9. **Reporting.** A stage session does not put questions to the author and
   does not stop at routine checkpoints; it records them in
   `stage N/STATUS.md` and carries on. It ends its turn with a report only
   when the author has to decide something (installing software, a choice that
   changes a formal statement or departs from this plan, a gap in the paper, a
   real blocker) and when the stage is complete. The report goes to the
   coordinating session, which reviews it and resolves it itself when it can
   (from the paper, this plan and the author's earlier decisions), and
   escalates to the author only what it cannot resolve; the decisions are sent
   back from there. (Author, 2026-11-20.)

## 2. Cited results taken as given

| Id | Source | What is assumed | Where it is used |
|---|---|---|---|
| C1 | Joyal–Street, Ch. 2 §2, Theorem 2.3, and the remark after Theorem 1.2 | For a free graph monoid `G`: a symmetric strict monoidal category `F_s(G)` whose objects are the words, whose morphisms `a → b` are the isomorphism classes of anchored diagrams in `G` from `a` to `b`, with composition given by gluing, monoidal product by disjoint union, identities and symmetries by node-free diagrams; and every graph monoid homomorphism from `G` to a symmetric strict monoidal category factors through `i_s : G → F_s(G)` by exactly one strict symmetric monoidal functor | Theorem 2.3; everything after it |
| C2 | Mac Lane coherence; Joyal–Street §1.1; Mac Lane–Paré §2; Fritz 2020, Prop. 10.16 | Strictification: for a Markov category `M`, the strict Markov category `str(M)` on the words over the objects of `M`, the Markov functor `eval : str(M) → M`, full, faithful, the identity on one-letter words, and strict when `M` is strict | End of Section 5 only |

Not assumed, because Mathlib already has it:

- Fritz 2020, Remark 2.3 (the unit is terminal, `ε_I = 1`, `δ_I = 1` in the strict
  case): `MarkovCategory.isTerminalUnit`, `discard_unit`, `copy_unit`.
- Mac Lane coherence for monoidal categories:
  `Mathlib.CategoryTheory.Monoidal.Free.Coherence`.

Not formalized, because the paper uses them only for comparison or motivation:
Fritz 2020, Theorem 10.17; Fritz–Liang, Definition 6.2, Theorem 6.6,
Corollary 6.7; Fong; Jacobs–Kissinger–Zanasi; Selinger; Remark 1.1; Remark 2.2
(isotopy in R⁴).

Two consequences of C1 are needed repeatedly and are to be *proved*, not added
to it (see D4 for how):

- **Generation.** Every morphism of `F_s(G)` is built from the generators,
  identities and symmetries by composition and monoidal product. This is the
  induction principle behind "`F_s` takes the same value", Proposition 5.6 and
  Proposition 6.6.
- **Value of a diagram in a strict symmetric monoidal category `C`**
  (Definition 2.1, first half). A diagram in `C` is a diagram in the free graph
  monoid `G_C` with alphabet the objects of `C` and arrows `a_1…a_n → b_1…b_m`
  the morphisms `⊗a_i → ⊗b_j`; its value is its image under the functor
  `F_s(G_C) → C` given by C1. A strict symmetric monoidal functor preserves
  values.

## 3. Design decisions

Each has a default. Those marked **(author)** change what the formal statements
say; the author approved their defaults on 2026-11-20.

### D1. Diagrams are combinatorial **(author, Stage 1)**

The paper defines a graph as a Hausdorff space with a finite set of nodes whose
complement is a finite union of open intervals. Sections 3–6 use only the
incidence data: nodes, edges, which end of an edge is attached to which node or
is free, the orders on inputs and outputs, the orders on domain and codomain.
A graph without circles is determined up to isomorphism by this data.

Default: formalize the incidence data and treat the topological wording of
Section 2 as part of the cited background (it is recorded in the blueprint, not
in Lean).

Author's decision, 2026-11-20: the passage between topological graphs and
incidence data (same isomorphism classes for finite graphs without circles) is
not to be formalized, also not in Stage 7; a reference is enough. The reference
is still to be chosen and recorded here.

Sketch, not compiled:

```lean
structure PGraph where
  Node : Type
  Edge : Type
  [finNode : Fintype Node] [finEdge : Fintype Edge]
  ins  : Node → List Edge      -- ordered inputs
  outs : Node → List Edge      -- ordered outputs
  dom  : List Edge             -- ordered; edges with no source node
  cod  : List Edge             -- ordered; edges with no target node
  -- every edge occurs exactly once among dom and the outs lists,
  -- exactly once among cod and the ins lists; no directed circuit
```

A loose edge is in both `dom` and `cod`; half-loose and pinned are derived.
Ordered ports as lists make a valuation of a node an arrow from
`(ins x).map v₀` to `(outs x).map v₀` directly.

Alternative: formalize topological graphs and prove the reduction to incidence
data. This is a separate project about one-dimensional spaces and adds nothing
to the paper's own arguments.

### D2. Strictness

Mathlib has `MonoidalCategory`, `SymmetricCategory`, `CopyDiscardCategory`,
`MarkovCategory`, but no notion of a strict monoidal category and no free
symmetric monoidal category. The paper needs strict categories whose objects
form a monoid, strict functors, and equality of functors.

Default: own definitions in `FreeMarkov/Strict/`:

- `GraphMonoid` (a monoid `V`, a type `A`, `s t : A → V`) and homomorphisms,
  exactly as in the Introduction; `FreeGraphMonoid` with `V = FreeMonoid S`
  (the paper allows this identification); `FreeDDGraphMonoid` with the two
  families of distinguished arrows.
- `StrictSMC`, `StrictMarkov`: a category on a monoid of objects with
  `f ⊗ g : a * c ⟶ b * d`. Laws that compare morphisms whose types differ by
  `mul_assoc` or `one_mul` are stated in the one-sorted type of arrows
  `Σ a b, a ⟶ b` (the paper's "underlying graph monoid"), which avoids casts
  in statements.
- Strict functors with an extensionality lemma; bundled categories of strict
  Markov categories.
- A bridge: every `StrictMarkov` is a Mathlib `MarkovCategory` whose associator
  and unitors are `eqToIso`. The final theorems are restated through the bridge,
  so that "Markov category" means Mathlib's definition.

Stage 0 includes a small trial of this encoding before anything is built on it.
Two existing developments are the references for it (REUSE-SURVEY.md):
`apellis/string-diagrams-lean` (`StringDiagrams.Monoidal`, `.Transport`: a
strict presented category as a Mathlib `MonoidalCategory`, retyping along
equalities of objects) and Tau Ceti's `Monoidal/EqToHom.lean`.

**Trial outcome (Stage 0, 2026-11-20): the default is kept.** As built:

- The one-sorted type of arrows is Mathlib's `Arrow C`; a law is
  `Arrow.mk lhs = Arrow.mk rhs`. Where a composite itself passes through an
  identification of objects (the hexagon, (1.2)), the identification is an
  `eqToHom` inside the composite. `StrictSMC C` and `StrictMarkov C` are
  classes over `[Monoid C] [Category C]` (`stage 0/FreeMarkov/Stage0/Strict/Basic.lean`).
- A small calculus suffices: `Arrow.mk_eq_mk_iff` and the two `simp` lemmas
  that drop outer `eqToHom`s (Mathlib), plus congruence of `Arrow.mk`-equality
  for `≫`, `⊗` and functors, and `eqToHom ⊗ eqToHom = eqToHom` (local,
  `Arrow.lean`, `Strict/Lemmas.lean`). The uniform proof method is: turn a
  goal into an equation in `Arrow`, strip outer casts, apply the axiom.
- Tested on the places where casts are worst: the derivation of the second
  hexagon from the first (25 lines); the Mathlib `MonoidalCategory` and
  `SymmetricCategory` instances, pentagon and both hexagons included (proved,
  `Strict/Bridge.lean`); the strict symmetric monoidal structure of `Syn_s(G)`
  (proved); and the interpretation of terms along a graph monoid
  homomorphism, where the casts come from `map_mul`, with soundness for
  associativity of `⊗` and for the hexagon (`stage 0/trial/D2Interp.lean`).
  All of these check with only `propext` and `Quot.sound`.
- For `Syn_s(G)` the relation on terms is heterogeneous (it relates terms
  whose source and target words are only propositionally equal), so the
  hom-sets are plain quotients and no cast enters the data; casts appear only
  on the target side of interpretations. Stage 1 can use the same device for
  diagrams.
- The type synonym `Syn G := FreeMonoid S` forces statements about words of
  `Syn G` to be made through `Syn.of G` (one lemma, `hexagon_aux`, had to be
  stated that way). Later quotient categories should follow the same pattern.
- `string-diagrams-lean` and Tau Ceti were not needed beyond the idea; nothing
  was ported.

### D3. Morphisms as classes of diagrams, and universes

Isomorphism classes of diagrams with arbitrary finite node and edge types live
one universe up. Default: constructions (gluing, disjoint union, sub-graphs,
surgery) are done on arbitrary finite types; the hom-sets use representatives
with `Fin n` nodes and `Fin m` edges, with a transport lemma between the two.

**Trial outcome (Stage 0, 2026-11-20): the default is kept.** Toy case
`stage 0/trial/D3Toy.lean`: finite sets labelled by `S` on an arbitrary
`Type u`, label-preserving bijections across universes, `Fin`-representatives
(read in any universe through `ULift`), the transport lemma
`X ≅ X.toFin.toLabelled`, an equivalence between the classes in
`Type (u+1)` and the classes of representatives in `Type` for every `u`, and
disjoint union computed on representatives agreeing with disjoint union on
arbitrary types. About 120 lines, no difficulty; the only friction was
`Fin (m + n) ≃ Fin m ⊕ Fin n` bookkeeping (`finSumFinEquiv`), which gluing
in Stage 1 will meet in the same form.

### D4. Form of the cited hypotheses

C1 is assumed in **comparison form**, in two steps.

1. The *syntactic* free symmetric strict monoidal category `Syn_s(G)` is built
   in Lean: objects the words, morphisms the formal composites and products of
   generators, identities and symmetries, modulo the axioms of a symmetric
   strict monoidal category. Its universal property for strict functors and
   the generation principle are proved by induction on terms. This is the
   pattern of Mathlib's `FreeMonoidalCategory`, Tau Ceti's
   `TensorSignature.FreeMonoidal` (which has coupons, `lift`, `inductionOn`
   and substitution) and Carlier's `FreeSymmetricMonoidalCategory`; none of
   them is strict on unparenthesized words with coupons and a symmetry, so it
   is written here, with credit.
2. `structure JoyalStreet (G)` is then one statement about two concrete things:
   for all words `a, b` a bijection between `Syn_s(G)(a, b)` and the
   isomorphism classes of anchored diagrams from `a` to `b`, sending a
   generator to its one-node diagram, composition to gluing, product to
   disjoint union, identities and symmetries to the node-free diagrams.

This is equivalent to Theorem 2.3 (two free objects are isomorphic by a unique
strict isomorphism). It has three advantages over assuming the universal
property itself: the hypothesis mentions no target category, so there is no
universe restriction; freeness and generation are theorems; and Remark 4.2
becomes a theorem (Stage 3). `F_s(G)` is `Syn_s(G)` with its morphisms read as
classes of diagrams through the bijection.

`structure Strictification (M)` holds C2.

Gluing, disjoint union and isomorphism of diagrams are defined concretely in
Stage 1 (the hypothesis and Sections 2–3 need them); their laws on classes
follow from the bijection.

### D5. Package


No external development is imported (REUSE-SURVEY.md): Tau Ceti is on Lean
4.37.0-rc1 and is a very large dependency, `string-diagrams-lean` is on 4.34.1,
`SymmMonCoherence` on 4.29.0-rc6, and none has the paper's objects. All three
are Apache-2.0; a ported lemma keeps its notice. Mathlib's `MarkovCategory` is
used as it is at the pin.


**Layout as built (Stage 0, 2026-11-20).** Library `FreeMarkovStage0` with
`srcDir = "stage 0"`, `roots = ["FreeMarkov.Stage0"]`,
`globs = ["FreeMarkov.Stage0", "FreeMarkov.Stage0.+"]`. Each stage's modules
carry the stage (`FreeMarkov.Stage1.*` for `FreeMarkovStage1`, …) so that the
libraries never claim each other's modules; declarations live in namespace
`FreeMarkov` regardless of stage. Files use Lean's module system (`module`,
`public import`, `@[expose] public section`) as Mathlib does; without it
every file warns. Trial files that are not part of the library sit in
`stage N/trial/`; scratch work in `.scratch/`. `python3 scripts/verify.py`
builds, scans for `sorry`, reports the axioms of every declaration and the
cited-result structures (`JoyalStreet`, `Strictification`) in the type of
every theorem, compiles the trial files and checks the blueprint.


### D6. Generality in Section 5 **(author, Stage 5)**

Remark 5.7 shows that Definition 5.4, Lemma 5.5 and Proposition 5.6 hold in every
strict Markov category once the multipliers `ι_{w → w^m}` are read as the
`m`-fold copies. Default: formalize this strict version as the primary one (it
has no straightness hypothesis and is what Section 6 uses in `Cau(G)`), and
obtain the straight case of the text as a corollary together with the
uniqueness statements of Remarks 5.2 and 5.3.

### D7. Target of Theorem 6.7 **(author, Stage 6)**

Default: a functor `FinODAGᵒᵖ ⥤ StrictMarkovCat` (strict Markov categories and
strict Markov functors), followed by the inclusion into `MarCat` (Markov
categories and Markov functors in the sense of the Introduction).

## 4. Stages

Sizes are my estimates of relative effort: S, M, L.

### Stage 0 — Scaffolding and the definitions of the Introduction (M)

- Package, pins, `.scratch/`, verification script (build, `sorry` scan, axiom
  report, list of cited hypotheses per public theorem), blueprint with one node
  per numbered statement and the dependency graph.
- `GraphMonoid`, homomorphisms, `FreeGraphMonoid`, `FreeDDGraphMonoid`.
- `StrictSMC`, `StrictMarkov`, strict functors, "matches duplicates and
  discards", the underlying graph monoid of a strict Markov category,
  `IsFreeMarkov C G i` (the definition of freeness in the Introduction).
- Bridge to Mathlib's `MarkovCategory`; `ε_I = 1`, `δ_I = 1`.
- `Syn_s(G)` (D4): terms, the congruence, the strict symmetric monoidal
  structure, the universal property for strict functors, generation.
- Trial of D2 and D3 on a toy case.

Done when: the definitions compile, the bridge and the universal property of
`Syn_s(G)` are proved, the trial is recorded.

**Record (2026-11-20): done.** `python3 scripts/verify.py` passes:
`lake build` exit code 0, no `sorry`, 341 declarations using only `propext`,
`Classical.choice`, `Quot.sound`, no cited result used. Status in
`stage 0/STATUS.md`, hand-over in `stage 0/HANDOFF.md`. Decided in Stage 0,
within this plan:

- Readings of the Introduction: "isomorphic to `W(S)` over `g`" means the
  extension `W(S) → V(G)` of `g` is bijective (`GraphMonoid.IsFreeOn`), and
  `V(G) = W(S)` is justified by `IsFreeOn.exists_iso`; `StrictSMC` has one
  hexagon (the other is `hexagon_reverse`); `ε_1 = 1`, `δ_1 = 1` are theorems
  (`StrictMarkov.discard_one`, `copy_one`), not axioms; a strict Markov functor
  has both matching conditions as fields, and `ofMapCopy` is the remark that
  discards match automatically; `IsFreeMarkov` has the target universes as
  free parameters.
- The bridge instances (`StrictSMC.monoidalCategory`, `symmetricCategory`,
  `StrictMarkov.markovCategory`) are global instances on any type carrying
  `StrictSMC`/`StrictMarkov`.
- The verification script is `scripts/verify.py` (the root `.gitignore`
  admits `scripts/` since 2026-11-20). The blueprint is
  `formalization/blueprint/` (a `leanblueprint` source tree, one node per
  numbered statement plus the Introduction and `Syn_s(G)`: 50 nodes, 14
  formalized), because the root `.gitignore` publishes `formalization/` and
  not a root `blueprint/`. The blueprint has not been rendered (`leanblueprint` is not installed).

### Stage 1 — Section 2: diagrams and `F_s(G)` (L)

- `PGraph`: nodes, edges, pinned, half-loose, loose, `inn`, `out`, initial,
  terminal, `dom`, `cod`, anchoring.
- Definition 2.1: valuations in a free graph monoid, diagrams, isomorphisms,
  domain and codomain words; diagrams in a strict symmetric monoidal category.
- Gluing, disjoint union, node-free diagrams of a permutation, one-node
  diagrams.
- `JoyalStreet G` (C1) in comparison form (D4); Theorem 2.3 as a theorem under
  it; the value of a diagram (Section 2 above).
- Directed paths, the partial order `Γ̇`, levels (lower sets), `cut(L)`,
  subgraphs, layers `Γ[L, M]`, with `cut(∅) = dom`, `cut(Γ̇) = cod`,
  `dom Γ[L, M] = cut(L)`, `cod Γ[L, M] = cut(M)`, loose edges of a layer.
- Remark 2.4 as a theorem: for levels `L ⊆ M` and any orderings of `cut(L)`,
  `cut(M)`, `[Γ] = [Γ[M, Γ̇]] ∘ [Γ[L, M]] ∘ [Γ[∅, L]]`.

Done when: the layer decomposition is proved and Theorem 2.3 is available as a
hypothesis with its two derived principles.

**Record (2026-11-20): done.** `python3 scripts/verify.py` passes: build exit
code 0 with no warnings, no `sorry`, 529 Stage 1 declarations using only
`propext`, `Classical.choice`, `Quot.sound`; `FreeMarkov.JoyalStreet` occurs in 43
theorems (`JoyalStreet.lean`, `Value.lean`), not in the layer files or Remark 2.4.
Status in `stage 1/STATUS.md`, hand-over in `stage 1/HANDOFF.md`. Decided in
Stage 1, within this plan:

- Graphs as in D1, with an outer node represented by `none` as the source or
  target of its edge; orderings as duplicate-free lists (`Enumeration`).
- Gluing is defined along any bijection `cod(Γ) → dom(Ω)` (for the surgeries);
  composition is the position-by-position case. Classes through `Fin`
  representatives (D3) in `Type (max w v)`; `DHom G a b` is a subtype of classes.
- `JoyalStreet G` has exactly the fields of D4. Theorem 2.3 is
  `JoyalStreet.isFreeSymmetric : IsFreeSymmetric J.Fs G J.ι` (target universes
  free); generation is `JoyalStreet.induction`; values are `CDiagram.value`, with
  preservation by strict functors `CDiagram.map_value` (proved via naturality of
  C1 under relabelling).
- Remark 2.4 holds for every choice of orderings of the cuts, in both
  bracketings, as an equation of classes, without C1 (`Diagram.remark_2_4`,
  `remark_2_4'`).
- The author's review of the statement of `JoyalStreet` (risk 5) was done on
  2026-11-20 and the statement accepted; the record is in `stage 1/STATUS.md`.

### Stage 2 — Section 3: surgeries (L, the heaviest combinatorics)

- Definition 3.1 (normal subgraph), `Γ'^♭`, the two observations after it.
- Lemma 3.2 (normal iff between `Γ[L, M]^♭` and `Γ[L, M]`), and `Γ'^♯`.
- The surgery `Γ^Ω_Λ(φ, α, β)` by the three-piece gluing of the "more
  precisely" paragraph; `α^♯`, `β^♯`; the fused valuation `v_w`; equal domain
  and codomain; an isomorphism `Λ → Ω` inducing `α, β` gives back `Γ`; the
  empty template; reversibility.
- Lemma 3.3, including the independence of the choice of layer.
- Definition 3.4: templates, symmetric sets, `T`-surgery, `T`-equivalence;
  `S_T` is a monoidal congruence; the quotient `F_s(G)/S_T` is a `StrictSMC`;
  `E_T`; Corollary 3.5 `S_T = E_T`.

Done when: Corollary 3.5 is proved and the quotient category is constructed.

**Record (2026-11-20): done.** `python3 scripts/verify.py` passes: build exit code 0
with no warnings, no `sorry`, 634 Stage 2 declarations using only `propext`,
`Classical.choice`, `Quot.sound`; `FreeMarkov.JoyalStreet` occurs in 23 theorems, all
about `S_T` as a congruence, the quotient and Corollary 3.5 (Lemma 3.3 needs no cited
result). Status in `stage 2/STATUS.md`, hand-over in `stage 2/HANDOFF.md`. Decided in
Stage 2, within this plan:

- Subgraphs are pairs of node and edge predicates; Definition 3.1 is stated with
  directed paths, and its conditions are proved equivalent to statements about the
  order of nodes (`Reach`).
- The surgery is built, as in the "more precisely" paragraph, by the three-piece gluing
  of `Γ[∅, L]`, `Λ ⊎ R`, `Γ[M, Γ̇]`, for every layer as in Lemma 3.2 (`surgeryAt`); the
  paper's surgery uses `Γ'^♯`. Independence of the layer, reversibility and the
  recognition of surgeries come from one canonical description of the result
  (`CanonProj`) and a comparison principle for isomorphisms.
- Templates have their diagrams not anchored (`PDiagram`) and finite types in a universe
  `u`; `T`-equivalence uses chains of diagrams on `Fin` types (D3), harmless by the
  iso-invariance of a `T`-surgery step; `S_T` is the relation on classes.
- Lemma 3.3 is stated with classes and the bracketing `h ∘ (X ∘ g)`, without C1;
  `S_T` being a congruence, the quotient `F_s(G)/S_T` (a `StrictSMC`, quotient of the
  hom-sets as for `Syn_s(G)`) and Corollary 3.5 use C1 (associativity and interchange).
- No paper feedback; no Stage 0 or Stage 1 source changed.

### Stage 3 — Section 4, first part: Theorem 4.1 (M–L)

- The Markov templates (4.1)–(4.4): coassociativity, left and right
  counitality, cocommutativity, naturality of discard for every arrow `f`
  including empty source or target; the reversed ones and the empty one; `S_M`.
- `δ_a`, `ε_a` for words; independence of the order of the prongs; equations
  (1.2), (1.1), (1.3) in `F_s(G)/S_M`, the last by induction on inner nodes.
- `i_s`, `i_m`; existence, Markov property and uniqueness of `F_m`.
- **Theorem 4.1**: `IsFreeMarkov (F_s(G)/S_M) G i_m`, and the instance of
  Mathlib's `MarkovCategory`.
- Remark 4.2 as a theorem: the quotient of `Syn_s(G)` by the congruence
  generated by the Markov axioms is isomorphic to `F_s(G)/S_M`; that is, an
  equation between terms follows from the axioms of Markov categories if and
  only if the diagrams are related by Markov surgeries.

Done when: Theorem 4.1 is proved under `JoyalStreet G` alone.

**Record (2026-11-20): done.** `python3 scripts/verify.py` passes: build exit code 0
with no warnings, no `sorry`, 234 Stage 3 declarations using only `propext`,
`Classical.choice`, `Quot.sound`; `FreeMarkov.JoyalStreet` occurs in 66 theorems, all
about the quotient `F_s(G)/S_M`, Theorem 4.1 and Remark 4.2 (the templates, the criterion
for `S_M` and the soundness of the Markov congruence use no cited result). Theorem 4.1 is
`JoyalStreet.theorem_4_1 : IsFreeMarkov J.FsM G J.iM`, with the Mathlib instance
`JoyalStreet.markovCategoryM`; Remark 4.2 is `JoyalStreet.remark_4_2` (with
`remark_4_2_surjective`) and `remark_4_2_semantic`. Status in `stage 3/STATUS.md`,
hand-over in `stage 3/HANDOFF.md`. Decided in Stage 3, within this plan:

- The Markov templates are built from concrete Stage 1 diagrams (gluings of one-node
  diagrams, identities, the symmetry), `α`, `β` matching positions; (4.2) as drawn
  discards the second prong, right counitality the first; templates in universe 0.
- `S_M ⊆ K` holds as soon as `K` contains each template pair for one ordering
  (`SRelClosed.of_sRel`, the proof of `S_T ⊆ E_T` with the ordering chosen freely); this
  is the form of Corollary 3.5 that the paper's argument for `F_m` uses.
- `δ_a`, `ε_a` on words are the monoidal products of the comonoids on the letters
  (Mathlib's comonoid theory through the bridge), i.e. defined through (1.2); the paper's
  diagram `Γ` with a choice of prong order is read through (1.2) (`prongCopy`) and its
  independence of the order is `prongCopy_eq`.
- Proof methods: (1.1) for words via Mathlib's comonoids, (1.3) via the generation
  principle instead of the induction on inner nodes asked for above (statement
  unchanged; recorded as an open item in `stage 3/STATUS.md`).
- Remark 4.2: duplicates and discards on words of `Syn_s(G)` through (1.2); the
  congruence generated by (1.1), (1.2) for all words and (1.3) for all morphisms, on
  `Arrow Syn_s(G)`; "isomorphic quotients" as kernel equality plus surjectivity.
- No paper feedback; no Stage 0–2 source changed.

### Stage 4 — Section 4, second part: skeletons (L)

- Quasi-terminal nodes, `Δ_Γ`, splitter paths, origin, live nodes, consumers,
  "same skeleton".
- **Lemma 4.3** (same class ⇒ same skeleton; the three items).
- Markov minimal, Markov congruent.
- **Lemma 4.4** (a minimal diagram in every class; minimal diagrams with the
  same skeleton are Markov congruent; the skeleton is a complete invariant).
- **Lemma 4.5** (dead inputs; the three items).

Done when: the three lemmas are proved in the form used by the application.

**Record (2026-11-20): done.** `python3 scripts/verify.py` passes: build exit code 0
with no warnings, no `sorry`, 880 Stage 4 declarations using only `propext`,
`Classical.choice`, `Quot.sound`; `FreeMarkov.JoyalStreet` occurs in 11 theorems, all
about `F_s(G)/S_M` (`JoyalStreet.projM_map_eq_iff` and the third item of Lemma 4.5).
Lemma 4.3 is `Diagram.lemma_4_3`, Lemma 4.4 `Diagram.lemma_4_4` (with `lemma_4_4_iff`),
Lemma 4.5 `JoyalStreet.lemma_4_5` (items 1, 2 also as `Diagram.lemma_4_5_path`,
`lemma_4_5_dead`, without `J`). Status in `stage 4/STATUS.md`, hand-over in
`stage 4/HANDOFF.md`. Decided in Stage 4, within this plan:

- Quasi-terminal is read as "no directed path from the node ends in `cod(Γ)`"; directed
  paths are chains of consecutive edges, equivalent to Stage 1's lists; the origin is a
  relation with existence and uniqueness; "same skeleton" includes equal domain and
  codomain words.
- Markov congruent is `S_T` for `T` = (4.1), (4.3), their reverses and the empty template.
- Lemma 4.5: `J` as positions (`Diagram.Dead`); `τ` is the class of the node-free diagram
  of the permutation "positions outside `J`, then those in `J`"; the equation is
  `projM f = τ ≫ (g ⊗ ε_{a'}) ≫ eqToHom (mul_one _)`; "every diagram that represents `g`"
  is every `Υ` with `J.cls h = [Υ]`, `projM h = g`.
- Proof methods: Lemma 4.3 by one surgery at a time through the canonical description,
  the bijection of live nodes onto by the reverse surgery; Lemma 4.4's congruence by
  normalising the trees of duplicates to sorted combs (swaps, rotations on the same
  nodes and edges) and an isomorphism of sorted minimal combs by coding; Lemma 4.5's
  existence through the layer decomposition at the discards of the dead inputs.
- No paper feedback; no Stage 0–3 source changed. Stage 3's open item 2 (the diagram of
  `δ_a`) was not needed and stays open.

### Stage 5 — Section 5: effects (L)

- Straight categories; Definition 5.1 (multipliers, as an inductive
  predicate); the `m`-fold copy; Remark 5.2 (uniqueness on `(w, w^m)`);
  Remark 5.3 (the underlying free DD-graph monoid when the objects form a free
  monoid; uniqueness for distinct letters; no multiplier if another letter
  occurs).
- Finite directed acyclic graphs with identity loops, `FinDAG`, its terminal
  object; `G_{S→T}`.
- Definition 5.4: the components, the fused diagram, independence of the
  assignment, `[w_T ‖ w_S]_{(W,K)}`; Markov minimality and equal skeletons in
  the free case.
- Lemma 5.5, Proposition 5.6, twists, Remark 5.7.
- `Strictification M` (C2); effects in an arbitrary Markov category; agreement
  with Definition 5.4 for strict `M`.

Done when: Lemma 5.5 and Proposition 5.6 are proved in the generality fixed by D6.

**Record (2026-11-20): done.** `python3 scripts/verify.py` passes: build exit code 0
with no warnings, no `sorry`, 456 Stage 5 declarations using only `propext`,
`Classical.choice`, `Quot.sound`; `FreeMarkov.JoyalStreet` occurs in 78 theorems (all about
free Markov categories and their functors), `FreeMarkov.Strictification` in 19 (all in
`Strictification.lean`). Lemma 5.5 is `EffData.lemma_5_5`, Proposition 5.6
`EffData.prop_5_6`, both in every strict Markov category (D6); Remark 5.2 `remark_5_2`,
Remark 5.3 `remark_5_3`, `remark_5_3_none`; the effect `EffData.effect`, in `Cau`-like free
categories `EffSig.freeEffect`. Status in `stage 5/STATUS.md` (including the statement of
`Strictification` in mathematical language, clause by clause, for the author), hand-over in
`stage 5/HANDOFF.md`. Decided in Stage 5, within this plan:

- One lemma, label coherence (`ProdSig.sameSkeleton_of_labels`: in a free `DD`-graph monoid
  where each letter has at most one producer, origins and live nodes are determined by
  letters), gives with Lemma 4.4 the uniqueness in Remarks 5.2, 5.3, Definition 5.4 and
  Lemma 5.5; it is also the core of the proof of Proposition 6.6.
- Definition 5.4: the fused diagram is recognised by the description used in the paper's
  proofs (`IsEffectDiagram`: domain `w_S`, codomain `w_T`, one node `κ_i` for each
  `i ∈ V(G_{S → T}) ∖ S`, no other producer node); the effect in `C` is the image under
  `F_{(W,K)}` (Theorem 4.1) of its class, and `EffData.effect_eq_value` shows it is the value
  in `C` of the image of the diagram. Put to the coordinator as a reading (STATUS, point 1).
- `G_{S → T}` through `R S T` (vertices outside `S` reaching `T` through vertices outside `S`).
- C2 is `structure Strictification M Str` (str(M), eval strong symmetric monoidal matching
  duplicates and discards, full, faithful, values on words) plus `Strictification.EvalStrict`
  for "strict when `M` is strict"; effects in an arbitrary `M` are `MData.effect`, and
  `MData.effect_strict` is the agreement for strict `M`.
- No paper feedback; no Stage 0–4 source changed. Stage 3's open item 2 stays open.

### Stage 6 — Section 6: refinement (M–L)

- `FinODAG` (default: vertices `Fin n`, arrows increasing), morphisms, fibers
  are intervals ordered as their images, the category.
- Terminology 6.1; Definition 6.2 (`W(G)`, causal mechanisms); `Cau(G)`;
  Definition 6.3 (causal effect, prior, twists, uniqueness of `S, T, ρ, τ`).
- `φ⁻¹` on variables; `f_φ` and (6.1); the note on `H_{φ⁻¹(pa v) → φ⁻¹(v)}`;
  Definition 6.4 (`φ^*`).
- Example 6.5: `G_{\bar v}`, `i_v^*`, equation (6.2). The enlarged-signature
  endofunctor is optional.
- **Proposition 6.6** and **Theorem 6.7**.

Done when: Theorem 6.7 is proved in the form fixed by D7.

**Record (2026-11-20): done.** `python3 scripts/verify.py` passes: build exit code 0
with no warnings, no `sorry`, 272 Stage 6 declarations using only `propext`,
`Classical.choice`, `Quot.sound`; C1 occurs in 62 theorems (through `JoyalStreet` or the
abbreviation `FinODAG.JS G := JoyalStreet G.W.toFreeGraphMonoid`, now listed in `CITED` of
`verify.py`), C2 in none. Theorem 6.7 is `FinODAG.refinementStrict J : FinODAGᵒᵖ ⥤
StrictMarkovCat` followed by `StrictMarkovCat.toMarCat` (`FinODAG.refinement J`,
`theorem_6_7`, `theorem_6_7_strict`), for a family `J : ∀ G, G.JS` of instances of C1;
Proposition 6.6 is `FinODAG.prop_6_6` (general singular variables) with `prop_6_6_sets`;
Definition 6.4 `FinODAG.refine`; Example 6.5 `equation_6_2`. Status in `stage 6/STATUS.md`
(including the statement of Theorem 6.7 in mathematical language for the author), hand-over and
a summary of the whole development in `stage 6/HANDOFF.md`. Decided in Stage 6, within this plan:

- `FinODAG` as the default: vertices `Fin n`, arrows a finite type with `s a ≤ t a` and identity
  loops (parallel arrows allowed), morphisms weakly monotone graph homomorphisms.
- Singular variables and twists as in Stage 5 (orderings as lists, `τ_*` node-free diagrams);
  "`τ_*`, `ρ_*` are the multipliers of Remark 5.3" proved directly in `Cau(G)`
  (`twist_isMultiplier`, `multiplier_unique`).
- Proposition 6.6: the substitution of the blocks `B_y` is the strict functor
  `F_s(W(G)) → F_s(W(H))` given by Theorem 2.3 (`FinODAG.subst`, node counts `card_subst`,
  `refine_projM`); label coherence is extended to compare live producers only
  (`ProdSig.sameSkeleton_of_live`), as the paper compares live nodes; the path arguments are
  `liveSet_iff`, `R_image`.
- `MarCat`: Mathlib's `MarkovCategory`, Markov functors as `Functor.Braided` plus matching of
  duplicates and discards (the form of Stage 5's `Strictification`); `StrictMarkovCat`,
  `MarCat` and the inclusion defined here (Mathlib has no bundled category of monoidal
  categories).
- The enlarged-signature endofunctor of Example 6.5 is not formalized (optional).
- No paper feedback; no Stage 0–5 source changed. Stage 3's open item 2 stays open.

### Stage 7 — optional, after the paper is covered

Author's decisions, 2026-11-20: `Strictification M` (C2) stays assumed and is
not to be discharged. Whether to construct an inhabitant of `JoyalStreet G`
(C1) is decided after Stage 6; if it is done, the combinatorial model only.

- Construct an inhabitant of `JoyalStreet G` for the combinatorial model, and of
  `Strictification M`, removing the cited hypotheses. No formalization of
  Theorem 2.3 was found; Tau Ceti's `DiagrammaticCoherence` roadmap plans the
  monoidal and braided cases geometrically and had no diagram category on
  2026-11-09. Recheck it first.
- The universal property for non-strict targets, by comparison with Tau Ceti's
  presented braided categories; comparison with Fritz–Liang.

## 5. Order and dependencies

Stages run in the order 0 to 6; each uses all earlier ones. Inside the paper:

- Theorem 4.1 needs C1, Lemma 3.2, the surgery, Corollary 3.5.
- Lemma 4.3 needs the surgery and the templates, not Theorem 4.1.
- Lemma 4.4 needs Lemma 4.3; Lemma 4.5 needs both.
- Remarks 5.2, 5.3 need Theorem 4.1 and Lemma 4.4.
- Proposition 6.6 needs Lemma 4.4, Definition 5.4, the value of a diagram;
  Theorem 6.7 needs Proposition 6.6 and the uniqueness in Theorem 4.1.

Advertised results (default, following the standing rule of a small selection):
Theorem 4.1 and Theorem 6.7, with Lemma 4.4 as the supporting result the
application relies on.

## 6. Steps the paper leaves to the reader

Each is a proof obligation and a possible source of feedback to the paper.

| Place | Wording | Obligation |
|---|---|---|
| Remark 2.4 | convention | Layer decomposition of `[Γ]` for every compatible ordering |
| After Def. 3.1 | "Observe" | Equal `♭` for subgraphs with the same nodes; initial and terminal nodes of a normal subgraph |
| Surgery | "Clearly there are induced bijections" | `α^♯`, `β^♯`; no directed circuit in the result |
| After the surgery | "Observe that a surgery can be reversed" | The reverse surgery and the isomorphism |
| After Def. 3.4 | "clearly", "easy to see" | `T`-equivalence respects isomorphism classes, `⊗` and `∘` |
| Corollary 3.5 | "easy consequence", "routine induction" | Both inclusions |
| Theorem 4.1 | "this is how `δ_a`, `ε_a` have been defined"; "`n` Markov surgeries" | (1.2) and (1.1) for words |
| Lemma 4.3 | "may be rerouted" | Live nodes and origins before and after each template |
| Lemma 4.4 | "determined, up to isomorphisms, by its skeleton and the shapes of these trees"; trees of duplicates | Construction of the isomorphism; the induction on leaves |
| Definition 5.4 | "changing an assignment amounts to…" | Independence of the assignment |
| Proposition 6.6 | substitution of the blocks `B_y` | Substitution of diagrams for nodes is the functor induced by C1 |

## 7. Risks, in order of weight

1. **Surgery and Lemma 3.3.** The construction glues three anchored pieces along
   bijections; the bookkeeping of loose edges (`R`, `Λ^♯`) and the independence
   of the layer are where a formal proof is longest.
2. **Lemma 4.4.** Rebuilding a Markov minimal diagram from its skeleton and tree
   shapes, and connecting binary trees of duplicates by (4.1) and (4.3).
3. **Strictness (D2).** Equalities between objects produce casts in proofs even
   if statements avoid them. The trial in Stage 0 decides the encoding before
   Stage 1 depends on it.
4. **Proposition 6.6.** Needs substitution of diagrams for nodes and its
   compatibility with gluing and disjoint union.
5. **Strength of C1.** The hypothesis must state the diagram operations
   precisely enough to give the layer decomposition and substitution, without
   assuming more than Joyal–Street prove. Its statement is reviewed by the
   author before Stage 1 proofs begin. (Reviewed and accepted 2026-11-20, after
   Stage 3; see `stage 1/STATUS.md`.)
6. **Universes (D3).** The comparison form of C1 removes the universe question
   from the hypothesis; it remains for classes of diagrams.

## 8. Decisions for the author

All were approved as recommended on 2026-11-20. The package layout was then
changed to the stage folders (D5); the first step of Stage 0 confirms it.

1. D1: combinatorial diagrams, with the topological definitions as cited
   background. (Stage 1)
2. Package `free_markov` rooted in the project folder with the stage folders
   as source directories; shared infrastructure stays local at first. (Stage 0)
3. D6: strict version of Section 5 as primary. (Stage 5)
4. D7: target category of Theorem 6.7. (Stage 6)
5. The advertised results: Theorem 4.1 and Theorem 6.7. (any time)
