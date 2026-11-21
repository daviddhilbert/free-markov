# Stage 7 status: C1 for the combinatorial diagrams

Written 2026-11-20. Task: the first item of Stage 7 of `formalization/PLAN.md` — construct an
inhabitant of `JoyalStreet G` for every free graph monoid `G`, for the combinatorial diagrams of
Stage 1, and derive the unconditional forms of the main theorems.

## Result

**Done.** `python3 scripts/verify.py` ends with `RESULT: PASS` (all eight libraries; 2026-11-20).
Stage 7: 352 declarations (280 theorems), no `sorry`, no `axiom`, every declaration uses only
`propext`, `Classical.choice`, `Quot.sound`; the build of `FreeMarkovStage7` has no warnings.
The cited-hypothesis report lists one Stage 7 theorem, `FreeMarkov.joyalStreet`, whose type is
`Nonempty (JoyalStreet G)`: the statement of C1 itself, as a conclusion. No unconditional
corollary has `JoyalStreet` in its type.

| What | Lean | File |
|---|---|---|
| C1 holds (an inhabitant, exactly Stage 1's structure, unchanged) | `JoyalStreet.ofCombinatorial G : JoyalStreet G` | `JoyalStreet.lean` |
| C1 holds (as a proposition) | `joyalStreet G : Nonempty (JoyalStreet G)` | `JoyalStreet.lean` |
| Theorem 2.3, unconditional | `Combinatorial.theorem_2_3 : IsFreeSymmetric (FsC G) G (FsC.ι G)`; generation `Combinatorial.induction` | `JoyalStreet.lean` |
| Theorem 4.1, unconditional | `Combinatorial.theorem_4_1 : IsFreeMarkov (Combinatorial.FsM G) G _` | `JoyalStreet.lean` |
| Lemma 4.4, quotient form | `Combinatorial.lemma_4_4` | `JoyalStreet.lean` |
| Lemma 4.5 | `Combinatorial.lemma_4_5` | `JoyalStreet.lean` |
| Proposition 6.6 | `Combinatorial.prop_6_6`, `Combinatorial.prop_6_6_sets` | `JoyalStreet.lean` |
| Theorem 6.7, both forms | `Combinatorial.theorem_6_7`, `Combinatorial.theorem_6_7_strict` (functors `Combinatorial.refinementStrict`, `Combinatorial.refinement`) | `JoyalStreet.lean` |

Each unconditional corollary is the Stage 1–6 result applied to `JoyalStreet.ofCombinatorial`
(`Combinatorial.js G` for `W(G)` in Section 6); the statements are the earlier ones with the
instance substituted. Lemma 4.4 in its diagram form (`Diagram.lemma_4_4`) and items 1, 2 of
Lemma 4.5 never used C1. C2 (`Strictification`) is untouched and remains a hypothesis where
Section 5 uses it.

## What was proved, without C1

1. **The laws of `F_s(G)` on classes** (`Embedding.lean`, `Laws.lean`, `Laws2.lean`,
   `FsCat.lean`). Gluing is associative (`DClass.comp_assoc`) and unital with the node-free
   identities (`idD_comp`, `comp_idD`); disjoint union is associative and unital
   (`tensor_assoc`, `idD_one_tensor`, `tensor_idD_one`, `idD_tensor_idD`); interchange
   (`interchange`); the node-free symmetries are natural (`braid_natural`), involutive
   (`braid_braid`) and satisfy the hexagon (`hexagon`). Hence `FsC G`, the words with
   `DHom G a b` as morphisms, is a `StrictSMC` (Stage 0's class). Method: each law is one
   embedding (`PEmb`, Stage 4) of one diagram into the other, and `PEmb.mk_eq` (an embedding
   between diagrams with as many nodes and edges, preserving the anchoring, is an isomorphism)
   with the edge count `card_glue_edges`.
2. **The comparison map.** `FsC.fromSyn G := Syn.lift (FsC.ι G) : Syn_s(G) → F_s(G)` (Stage 0's
   universal property); on hom-sets `FsC.toDHom`, compatible with generators, identities,
   symmetries, composition and products (`toDHom_gen`, …, `toDHom_tensor`).
3. **Injectivity** (route (a) of the task, specialised to the target `Syn_s(G)`). The *value*
   of a diagram in `Syn_s(G)` (`Diagram.value`, `DClass.value`) is computed node by node along a
   processing order (a chain of levels with one node per step); it is independent of the order
   (`Wires.VData.val_indep`), invariant under isomorphism (`Diagram.value_eq_of_iso`), and sends
   one-node diagrams, node-free identities and symmetries, disjoint unions and gluings to
   generators, identities, symmetries, products and composites (`value_oneNode`, `value_idD`,
   `value_braidD`, `value_tensor`, `value_glue`). By induction on terms of `Syn_s(G)`, the value
   of the class of a formal composite is that composite (`FsC.value_toDHom`), so `toDHom` is
   injective (`FsC.toDHom_injective`).
4. **Surjectivity** (generation; `Generation.lean`). Node-free diagrams are composites of
   identities and symmetries (`DClass.inIm_nodeFree`: bring the wires into the codomain order one
   at a time, each step an embedding); a diagram with a node is `[P] ∘ ([x] ⊗ 1) ∘ [Γ']` for a
   minimal node `x`, a node-free `P` on the domain edges and the upper layer `Γ' = Γ[{x}, Γ̇]` of
   Stage 1 (one embedding of the three-piece gluing into `Γ`); induction on the number of nodes
   (`DClass.inIm_of_card`, `FsC.toDHom_surjective`).

Underneath item 3:

- **Coherence for symmetries** (`ArrowAlg.lean`, `Perm.lean`, `Perm2.lean`). For labelled wires
  in any `StrictSMC`, `Wires.perm d c` (bring the first wire of `c` to the front and recurse)
  satisfies `perm_self`, `perm_comp` (`perm d c ∘ perm c c' = perm d c'`), `perm_append`
  (monoidal), `perm_swap` (a block swap is the symmetry) and `perm_map` (renaming). The only
  braid identity beyond the axioms is `AArr.dm_obj` (two ways of bringing two wires to the
  front), proved from the hexagons, naturality and `σ ∘ σ = 1`. The computations use a
  one-sorted calculus of arrows (`AArr`: composition of arrows when they meet, `⊗`, identities,
  symmetries as arrows), in the spirit of D2: equations in `Arrow C`, never casts.
- **Processing nodes** (`Steps.lean`, `Steps2.lean`, `Passive.lean`) on abstract incidence data
  `Wires.VData`: reordering the initial wires (`val_perm`), renaming (`IsMap.val`), two
  independent nodes in either order (`two_step`, `val_swap`), moving a node to the front and full
  independence (`val_move`, `val_indep`), and untouched wires beside the processed ones
  (`IsMap.steps_append_right`, `step_passive_left`, `IsMap.val_append_left`).
- **Existence of a processing order** (`Diagram.exists_order`): repeatedly take a node minimal for
  the order `Γ̇` (well-founded on a finite type); the wires present at each step are the cut of the
  processed level.

## Route chosen, and why

Task item 2 offered (a) the value in an arbitrary symmetric strict monoidal category or (b) the
comparison `Syn_s(G) → F_s(G)` with surjectivity by layer decomposition and injectivity by a
normal form or by (a). Taken: (b), with injectivity by (a) for the single target `Syn_s(G)`.
Reasons: the universal property of `F_s(G)` then follows from Stage 0's universal property of
`Syn_s(G)` through the bijection, exactly as Stage 1 already does under C1; only one target is
needed; surjectivity uses Stage 1's layers (`upperD`) and Stage 4's embeddings, which needed no
change. The value machinery itself is written for any `StrictSMC` (`Wires.VData` takes the
target as a parameter); only `Diagram.vdata` specialises to `Syn_s(G)`.

## Relation to Joyal–Street, Chapter 2

- Proposition 2.1 (the value does not depend on the choice of levels): `Wires.VData.val_indep`
  with `val_perm`; their chains of levels are our processing orders (one node per level), and
  their "progressive plane diagram" decompositions are the steps `VData.step`.
- Theorem 2.2 (the value is invariant under isomorphism and is a strict monoidal functor on
  diagrams): `Diagram.value_eq_of_iso`, `value_tensor`, `value_glue`, `value_oneNode`,
  `value_idD`, `value_braidD`.
- Theorem 2.3 (`F_s(G)` is free): `Combinatorial.theorem_2_3`, via the bijection with `Syn_s(G)`.
  The laws of `F_s(G)` that Joyal–Street take from the topology of graphs are proved here on the
  incidence data (item 1).
- Joyal–Street's proof of Proposition 2.1 rests on Mac Lane's coherence for symmetric monoidal
  categories (their Theorem 1.2 / remark after it). Here the needed form of coherence is proved
  directly (`Wires.perm_comp` and its companions), not cited.
- Their objects are topological graphs (Hausdorff spaces with a finite set of nodes). As decided
  by the author (D1), the passage to incidence data is not formalized; the reference chosen by
  the author and recorded in PLAN.md (D1) is Bonchi–Gadducci–Kissinger–Sobociński–Zanasi, *String
  Diagram Rewrite Theory II*, Section 3 (Corollary 3.20), with Part I, Corollary 3.11; their
  hypergraph encoding is the dual of ours and the dictionary is not formalized.

## What remains assumed

- **C2** (`Strictification M`), where Section 5 uses it (author's decision: never to be proved).
- **The informal passage** between Joyal–Street's topological graphs and the combinatorial graphs
  of Stage 1 (D1; a reference, not formalized).

Nothing else: Theorem 2.3 and everything after it in the advertised list hold for the
combinatorial model without hypotheses.

## Changes outside `stage 7/`

- `lakefile.toml`: library `FreeMarkovStage7` (`srcDir = "stage 7"`), added to `defaultTargets`.
- `scripts/verify.py`: `7: ("FreeMarkovStage7", "FreeMarkov.Stage7", "stage 7")` in `STAGES`.
- `formalization/REUSE-SURVEY.md`: the focused search before Stage 7.
- `formalization/blueprint/src/content.tex`: section "C1 for the combinatorial diagrams
  (Stage 7)", nodes `s7:laws`, `s7:perm`, `s7:value`, `s7:bij`, `s7:C1`, `s7:uncond`; the Scope
  paragraph mentions Stage 7.
- `formalization/PLAN.md`: the Stage 7 record (appended after the coordinator's uncommitted
  paragraphs of the Stage 7 entry, which were left as they were).
- No Stage 0–6 source was changed; `structure JoyalStreet` is untouched. No defect was found in
  an earlier stage's definitions: every law holds for the operations of Stage 1 as defined.
- No paper feedback (`PAPER-FEEDBACK.md` unchanged): the paper cites Joyal–Street, and nothing in
  its use of Theorem 2.3 is contradicted.

# Follow-up (2026-11-20): the diagram of `δ_a`, and uniqueness of the free Markov category

Task: the two items recorded in the Stage 7 entry of `formalization/PLAN.md` (coordinator's
decision on Stage 3's open item 2; author's decision on the comparison of free Markov categories).

**Done.** `python3 scripts/verify.py` ends with `RESULT: PASS` (all eight libraries; build exit
code 0, no warnings). Stage 7 now has 383 declarations (303 theorems), no `sorry`, no `axiom`,
only `propext`, `Classical.choice`, `Quot.sound`. The cited-hypothesis report lists, besides
`joyalStreet` (C1 as a conclusion), the four theorems `JoyalStreet.projM_copyD`,
`projM_copyWordD`, `projM_discardD`, `projM_discardWordD`: they are stated for an arbitrary
`J : JoyalStreet G`, as the earlier stages do; their unconditional forms are
`Combinatorial.copy_diagram` and `Combinatorial.discard_diagram`. Blueprint: 79 nodes, 77
formalized (new nodes `s7:copy-diagram`, `s7:unique`).

New files (imported by the aggregator `stage 7/FreeMarkov/Stage7.lean`): `CopyDiagram.lean`,
`Uniqueness.lean`. No other source was changed (no Stage 0–6 file, no existing Stage 7 module).

## Item A: the single diagram of `δ_a` (Stage 3's open item 2) — closed

| Paper (Section 4, before the proof of Theorem 4.1) | Lean |
|---|---|
| `Γ`: joins `⊗_i δ_{a_i}` and `(⊗_i 1_{a_i}) ⊗ (⊗_i 1_{a_i})`, the two outputs of `δ_{a_i}` to the `i`th and `(n+i)`th edges, in either order | `Diagram.copyD G a c` (letters `a : Fin n → S`, prong order `c : Fin n → Bool`); `Diagram.copyWordD G w c` for a word `w` |
| "all such `Γ` represent the same morphism ... denoted by `δ_a`" | `JoyalStreet.projM_copyD` (any `c`: the class is `copyM a`, as arrows), `projM_copyWordD` (paper's form: `w → w w`, equality in `F_s(G)/S_M`) |
| "`ε_a = ⊗_i ε_{a_i}`" | `Diagram.discardD`, `discardWordD`; `projM_discardD`, `projM_discardWordD` |
| unconditional | `Combinatorial.copy_diagram`, `Combinatorial.discard_diagram` |

The diagram is literal: nodes `Fin n` (the duplicate on `a_i`), edges `Fin n ⊕ (Fin n ⊕ Fin n)`
(the inputs; the outputs going to the `i`th codomain edge; those going to the `(n+i)`th), domain
the inputs in order, codomain the first-kind outputs then the second-kind ones, so the codomain
word is `a a`; `c i` says which prong of the `i`th duplicate goes to the `i`th edge. `copyM a` is
Stage 3's duplicate on words (the instance `strictMarkovM` used in Theorem 4.1), so the statement
is exactly "for every choice of prong order, `[Γ] = δ_a`". The paper's diagram represents
`copyM a` for every prong order; no stop condition arose.

Stage 5's `value_copy_diagram` and `remark_5_7_copy` do not give this directly: they are about the
one-letter monoid `G_a`, where a word `a^m` has only one letter, whereas a word of `G` may repeat
letters at different positions and the diagram must connect positions, not letters (the paper's
parenthesis "it is not enough to match the values in `S`"). They do give the method.

Proof (differs from the paper's "in light of (4.3)", same statement): over the free `DD`-graph
monoid with the distinct letters `0, …, n-1` and only duplicates and discards
(`ProdSig.free (Fin n)`), there is at most one morphism from `0 ⋯ (n-1)` to any word in
`F_s/S_M` (Stage 5's `ProdSig.free_hom_eq`, from label coherence and Lemma 4.4), so the class of
`copyD _ id c` there is the duplicate. Relabelling `i ↦ a_i` (`CopyDiagram.relab`) carries that
diagram to `copyD G a c` (`relabelCopyIso`, the identity on nodes and edges) and, by the
naturality of C1 under relabelling (Stage 1's `val_synMap`) and the uniqueness in the universal
property of `Syn_s`, is the strict Markov functor of Theorem 4.1 on classes; it preserves
duplicates. For the auxiliary monoid C1 is Stage 7's theorem (`ofCombinatorial`), so the form for
`J : JoyalStreet G` assumes nothing beyond `J`. For `ε_a`: the unit of a strict Markov category is
terminal (`eq_discard`).

## Item B: uniqueness of the free Markov category — closed

| Statement | Lean |
|---|---|
| `C`, `C'` free over `G` via `i`, `i'` ⇒ exactly one strict Markov functor `F : C → C'` with `i' = F ∘ i`, and every such `F` has a strict Markov inverse `F'` (`i = F' ∘ i'`, `F' ∘ F = 1`, `F ∘ F' = 1`) | `IsFreeMarkov.unique_iso`; same-universe form `IsFreeMarkov.unique_iso'` |
| the same for free symmetric strict monoidal categories (Theorem 2.3's notion) | `IsFreeSymmetric.unique_iso`, `unique_iso'` |
| any strict Markov category with the universal property of Theorem 4.1 is isomorphic to `F_s(G)/S_M` by a unique compatible strict Markov functor | `Combinatorial.fsM_unique_iso` (docstring: with Fritz–Liang, Corollary 6.7, cited, not formalized, this compares the two constructions) |
| the same for `F_s(G)` and Theorem 2.3 | `Combinatorial.fsC_unique_iso` |

Universes: `IsFreeMarkov C G i` quantifies over targets in one pair of universes (its last two
universe parameters). The proof uses the property of `C` with targets `C'` and `C`, and that of
`C'` with targets `C` and `C'`; so `unique_iso` takes these four instances, and `unique_iso'` (both
categories in the same universes) two. In the corollaries Theorem 4.1 (resp. 2.3) supplies the two
instances for `F_s(G)/S_M` (resp. `F_s(G)`), at every universe; the other category's property is
needed at the universes of `F_s(G)/S_M` (`Type w`, morphisms in `max w w₂`) and at its own.

Form of the conclusion: `(∃! F, i' = F ∘ i) ∧ ∀ F, i' = F ∘ i → ∃ F', i = F' ∘ i' ∧ F' ∘ F = 1 ∧
F ∘ F' = 1`, which says that the compatible functor is unique and that it is an isomorphism (in
the category of strict Markov categories and strict Markov functors), with equalities of functors
(no natural isomorphisms are needed in the strict setting).
