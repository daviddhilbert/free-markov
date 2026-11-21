# A graphical construction of free Markov categories — Lean formalization

A Lean 4 formalization of Yimu Yin, *A graphical construction of free Markov categories*
(arXiv:2204.04920, revised version). Every numbered statement of Sections 2–6 of the paper is
proved, including the steps the paper leaves to the reader.

About 32 000 lines of Lean, no `sorry`, no `axiom` declarations; every declaration depends only
on `propext`, `Classical.choice` and `Quot.sound`.

## Main results

Unconditional forms are in the namespace `FreeMarkov.Combinatorial` (and
`FreeMarkov.Diagram` where noted).

| Paper | Statement | Lean |
|---|---|---|
| Theorem 2.3 | Isomorphism classes of anchored diagrams form the free symmetric strict monoidal category `F_s(G)` | `Combinatorial.theorem_2_3` |
| Lemma 3.2 | Characterisation of normal subgraphs by layers | `PGraph.isNormal_iff` |
| Lemma 3.3 | A surgery is the replacement `h ∘ [Ω ⊎ R] ∘ g ↦ h ∘ [Λ ⊎ R] ∘ g` | `Diagram.lemma_3_3` |
| Corollary 3.5 | `S_T = E_T` | `cor_3_5` |
| **Theorem 4.1** | `F_s(G)/S_M` is the free Markov category over `G` | `Combinatorial.theorem_4_1` |
| Remark 4.2 | Equations follow from the Markov axioms iff they hold up to Markov surgeries | `JoyalStreet.remark_4_2` |
| Lemma 4.3 | Diagrams in the same class have the same skeleton; the three items | `Diagram.lemma_4_3` |
| Lemma 4.4 | Markov minimal diagrams; the skeleton is a complete invariant | `Diagram.lemma_4_4`, `Combinatorial.lemma_4_4` |
| Lemma 4.5 | Dead inputs | `Combinatorial.lemma_4_5` |
| Remarks 5.2, 5.3 | Uniqueness of multipliers | `remark_5_2`, `remark_5_3` |
| Lemma 5.5 | Effects compose | `EffData.lemma_5_5` |
| Proposition 5.6 | Strict Markov functors preserve effects | `EffData.prop_5_6` |
| Proposition 6.6 | `φ^*([w ‖ v]) = [φ^*(w) ‖ φ^*(v)]` | `Combinatorial.prop_6_6` |
| **Theorem 6.7** | Refinement is a functor `FinODAG^op → MarCat` | `Combinatorial.theorem_6_7`, `Combinatorial.theorem_6_7_strict` |

Beyond the paper:

| Statement | Lean |
|---|---|
| The paper's single diagram for `δ_a` on a word represents the duplicate, for every order of the prongs | `Combinatorial.copy_diagram` |
| Free Markov categories over `G` are isomorphic by a unique compatible strict Markov functor | `Combinatorial.fsM_unique_iso` |
| A morphism between the restrictions of two Markov functors `F_s(G)/S_M → M` lifts to exactly one monoidal natural transformation | `Combinatorial.extension_existsUnique` |
| Restriction to generators is an equivalence between Markov functors into an arbitrary Markov category `M` and interpretations of `G` in `M` (assumes strictification) | `Combinatorial.restrict_isEquivalence` |
| Proposition 5.6 for Markov functors into an arbitrary Markov category (assumes strictification) | `Combinatorial.prop_5_6_markov` |

## What is assumed

Cited results are never axioms. They enter as explicit hypotheses in the types of the theorems
that use them, and the verification script reports every such use.

- **Joyal–Street, Theorem 2.3** — *proved* here for the combinatorial diagrams
  (`JoyalStreet.ofCombinatorial`, Stage 7). Stages 1–6 state their results for an arbitrary
  `J : JoyalStreet G`; the unconditional forms substitute the proved instance.
- **Strictification** (`Strictification M Str`): for a Markov category `M`, a strict Markov
  category on the words over the objects of `M` with a full and faithful Markov functor
  `eval` to `M`. It is assumed, and is used only for effects in a non-strict Markov category
  (end of Section 5) and for the two results marked above. Theorems 2.3, 4.1 and 6.7 do not
  use it.

Diagrams are combinatorial (incidence data: nodes, edges, ordered inputs and outputs, ordered
domain and codomain). The passage from the topological graphs of Joyal–Street to this data is
not formalized; for a combinatorial account of free symmetric monoidal categories in the
literature see Bonchi, Gadducci, Kissinger, Sobociński, Zanasi, *String Diagram Rewrite
Theory II* (arXiv:2104.14686), Section 3.

## Layout

One Lean library per stage, in the folder of that stage. Each folder has a `STATUS.md`
(statements against the paper, readings fixed, proof methods) and a `HANDOFF.md`.

| Folder | Content |
|---|---|
| `stage 0` | Strict symmetric monoidal and strict Markov categories, the bridge to Mathlib's `MarkovCategory`, the syntactic free category `Syn_s(G)` |
| `stage 1` | Section 2: graphs, diagrams, gluing, levels and layers, Remark 2.4 |
| `stage 2` | Section 3: normal subgraphs, surgeries, Lemma 3.3, Corollary 3.5 |
| `stage 3` | Section 4, first part: Markov templates, Theorem 4.1, Remark 4.2 |
| `stage 4` | Section 4, second part: skeletons, Lemmas 4.3–4.5 |
| `stage 5` | Section 5: multipliers, effects, Lemma 5.5, Proposition 5.6 |
| `stage 6` | Section 6: ordered DAGs, causal effects, refinement, Proposition 6.6, Theorem 6.7 |
| `stage 7` | Joyal–Street's Theorem 2.3 for combinatorial diagrams; unconditional forms |
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

Apache License 2.0; see `LICENSE`.
