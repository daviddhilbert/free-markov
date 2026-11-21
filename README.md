# A graphical construction of free Markov categories — Lean formalization

A Lean 4 formalization of Yimu Yin, *A graphical construction of free Markov categories*.
The paper is in [`paper/`](paper/) (`free-markov.pdf`, and its source `free-markov.tex` with
commented-out draft passages removed); statement numbers below are those of that version.

Every numbered theorem, lemma, proposition and corollary of Sections 2–6 is proved, including
the steps the paper leaves to the reader, and so are the numbered definitions and remarks, with
these exceptions: Remark 2.2 (a comment on isotopy) and the last paragraph of Example 6.5 (the
endofunctor on an enlarged signature) are not formalized.

About 32 000 lines of Lean. No `sorry`, no `axiom` declarations; every declaration depends only
on `propext`, `Classical.choice` and `Quot.sound`.

## Main results

All names are in the namespace `FreeMarkov`. The forms listed here take no cited result as a
hypothesis, except where the last table says so.

| Paper | Statement | Lean |
|---|---|---|
| Theorem 2.3 | Isomorphism classes of anchored diagrams form the free symmetric strict monoidal category `F_s(G)` | `Combinatorial.theorem_2_3` |
| Remark 2.4 | Decomposition of a diagram into layers | `Diagram.remark_2_4` |
| Lemma 3.2 | Characterisation of normal subgraphs by layers | `PGraph.isNormal_iff` |
| Lemma 3.3 | A surgery is the replacement `h ∘ [Ω ⊎ R] ∘ g ↦ h ∘ [Λ ⊎ R] ∘ g` | `Diagram.lemma_3_3` |
| Corollary 3.5 | `S_T = E_T` | `Combinatorial.cor_3_5` |
| **Theorem 4.1** | `F_s(G)/S_M` is the free Markov category over `G` | `Combinatorial.theorem_4_1` |
| Remark 4.2 | An equation follows from the Markov axioms iff it holds up to Markov surgeries | `Combinatorial.remark_4_2` |
| Lemma 4.3 | Diagrams in the same class have the same skeleton; the three items | `Diagram.lemma_4_3` |
| Lemma 4.4 | Markov minimal diagrams; the skeleton is a complete invariant | `Diagram.lemma_4_4`; in the quotient, `Combinatorial.lemma_4_4` |
| Lemma 4.5 | Dead inputs | `Combinatorial.lemma_4_5` |
| Remarks 5.2, 5.3 | Uniqueness of multipliers | `Combinatorial.remark_5_2`, `Combinatorial.remark_5_3` |
| Definition 5.4 | The effect `[w_T ‖ w_S]` | `Combinatorial.effect` |
| Lemma 5.5 | Effects compose | `Combinatorial.lemma_5_5` |
| Proposition 5.6 | Strict Markov functors preserve effects | `Combinatorial.prop_5_6` |
| Proposition 6.6 | `φ^*([w ‖ v]) = [φ^*(w) ‖ φ^*(v)]` | `Combinatorial.prop_6_6` |
| **Theorem 6.7** | Refinement is a functor `FinODAG^op → MarCat` | the functors `Combinatorial.refinementStrict`, `Combinatorial.refinement`; the functor laws are stated in `Combinatorial.theorem_6_7_strict` |

Beyond the paper:

| Statement | Lean |
|---|---|
| The paper's single diagram for `δ_a` on a word represents the duplicate, for every order of the prongs | `Combinatorial.copy_diagram` |
| Free Markov categories over `G` are isomorphic by a unique compatible strict Markov functor | `Combinatorial.fsM_unique_iso` |
| A morphism between the restrictions to generators of two Markov functors `F_s(G)/S_M → M` lifts to exactly one monoidal natural transformation | `Combinatorial.extension_existsUnique` |
| Restriction to generators is an equivalence between Markov functors into an arbitrary Markov category `M` and interpretations of `G` in `M` — **assumes a strictification of `M`** | `Combinatorial.restrict_isEquivalence` |
| Proposition 5.6 for Markov functors into an arbitrary Markov category — **assumes a strictification of `M`** | `Combinatorial.prop_5_6_markov` |

## How the Lean text relates to the paper

- **Diagrams are combinatorial.** A graph is incidence data: nodes, edges, the source and target
  of each edge (a node or "outer"), ordered inputs and outputs at each node, ordered domain and
  codomain. The topological definitions of Section 2 are not formalized. Theorem 2.3 is therefore
  proved here for these combinatorial diagrams (Stage 7), following Joyal–Street, Chapter 2; the
  identification with their topological diagrams is not formalized. For a combinatorial account in
  the literature see Bonchi, Gadducci, Kissinger, Sobociński, Zanasi, *String Diagram Rewrite
  Theory II* (arXiv:2104.14686), Section 3.
- **Free graph monoids** have `W(S)` itself as their monoid of vertices.
- **Section 5 is stated for every strict Markov category**, with the multipliers `ι_{w → w^m}`
  read as `m`-fold copies (Remark 5.7); the straight case of the text follows by Remark 5.2.
- **Definition 5.4.** The effect is defined as the morphism represented by any diagram with
  domain `w_S`, codomain `w_T`, exactly one node `κ_i` for each `i ∈ V(G_{S→T}) ∖ S` and otherwise
  only duplicates and discards; all such diagrams are proved to represent the same morphism. The
  fusion of components along an assignment is not constructed as an operation.
- **`FinODAG`** has vertex sets `{0, …, n-1}` in their natural order.
- **Template (4.1)**: `coassT` has `Ω` and `Λ` in the order opposite to the paper's picture. The
  set of Markov templates contains every template with its reverse, so `S_M` is the paper's.

Each `stage N/STATUS.md` gives the full correspondence for its part, with every such reading.

## What is assumed

Cited results are never axioms. They enter as explicit hypotheses in the types of the theorems
that use them, and the verification script reports every such use.

- **Joyal–Street, Theorem 2.3** is *proved* for the combinatorial diagrams
  (`JoyalStreet.ofCombinatorial`). Stages 1–6 state their results for an arbitrary instance
  `J : JoyalStreet G`; the forms in `Combinatorial` substitute the proved instance.
- **Strictification** (`Strictification M Str`): for a Markov category `M`, a strict Markov
  category on the words over the objects of `M` with a full and faithful Markov functor `eval`
  to `M`. It is assumed where used, and no instance is constructed in this repository. It is
  used only for effects in a non-strict Markov category (end of Section 5) and for the two
  results marked above. Nothing else depends on it.

## Layout

One Lean library per stage, in the folder of that stage, each with a `STATUS.md`.

| Folder | Content |
|---|---|
| `paper` | The paper |
| `stage 0` | Strict symmetric monoidal and strict Markov categories, the bridge to Mathlib's `MarkovCategory`, the syntactic free category `Syn_s(G)` |
| `stage 1` | Section 2: graphs, diagrams, gluing, levels and layers, Remark 2.4 |
| `stage 2` | Section 3: normal subgraphs, surgeries, Lemma 3.3, Corollary 3.5 |
| `stage 3` | Section 4, first part: Markov templates, Theorem 4.1, Remark 4.2 |
| `stage 4` | Section 4, second part: skeletons, Lemmas 4.3–4.5 |
| `stage 5` | Section 5: multipliers, effects, Lemma 5.5, Proposition 5.6 |
| `stage 6` | Section 6: ordered DAGs, causal effects, refinement, Proposition 6.6, Theorem 6.7 |
| `stage 7` | Joyal–Street's Theorem 2.3 for combinatorial diagrams; the forms without hypotheses |
| `stage 8` | The universal property for arbitrary Markov categories |
| `formalization` | The plan (`PLAN.md`), the survey of existing formalizations, the blueprint |
| `scripts` | `verify.py` |

## Building and checking

Lean `v4.35.0` and Mathlib at revision `56a005855ea17e0b0958f73ec801ae140b0a1679` (see
`lean-toolchain` and `lake-manifest.json`).

```bash
lake exe cache get
```

```bash
lake build
```

```bash
python3 scripts/verify.py
```

The script builds all libraries, scans for `sorry`, reports the axioms of every declaration,
lists the theorems whose types mention a cited hypothesis, and checks the blueprint. It must
end with `RESULT: PASS`.

## Licence

The Lean development, the scripts and the accompanying notes are under the Apache License 2.0;
see `LICENSE`. The paper in `paper/` is © its author, all rights reserved, and is not covered
by that licence.
