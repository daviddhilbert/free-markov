# Reuse survey: free Markov categories

Surveyed 2026-11-20, before any Lean code, following
`special-transformations/FORMALIZATION-REUSE-GUIDELINES.md`.

Targets searched for: Markov and copy-discard categories; the free symmetric
monoidal category on a tensor scheme; Joyal–Street diagrams and Theorem 2.3;
strict monoidal categories and strictification; free Markov categories;
directed acyclic graphs; causal models and the do-calculus.


## Result in one paragraph

No formalization of the paper's results, of free Markov categories, or of
Joyal–Street's Theorem 2.3 (symmetric case) was found. Mathlib supplies the
definition of a Markov category. Three external developments supply patterns
worth following for the algebraic side and for strictness, none importable as
it stands for the paper's objects (strict categories on unparenthesized words,
symmetric, with graph-shaped diagrams). The search changed one design decision
of the plan: the form of the Joyal–Street hypothesis (PLAN.md, D4).

## Candidates

| Candidate | What it has | Decision |
|---|---|---|
| **Mathlib**, pinned `56a005855ea17e0b0958f73ec801ae140b0a1679` (Apache-2.0), Lean 4.35.0. `CategoryTheory/CopyDiscardCategory/{Basic,Cartesian,Deterministic,Widesubcategory}.lean`, `CategoryTheory/MarkovCategory/{Basic,Positive}.lean` | `CopyDiscardCategory`, `MarkovCategory` (`discard_natural`, `eq_discard`, `isTerminalUnit`, `copy_unit`, `discard_unit`), deterministic morphisms | **Import directly.** The paper's "Markov category" is this class; the strict notion is bridged to it (PLAN.md, D2). Covers Fritz 2020, Remark 2.3 |
| Mathlib `CategoryTheory/Monoidal/Free/{Basic,Coherence}.lean` | `FreeMonoidalCategory` on a type of objects, Mac Lane coherence; no morphism generators, no symmetry | Import for C2 work if strictification is ever discharged; pattern for the syntactic category |
| Mathlib `Combinatorics/Digraph/{Basic,Orientation}.lean` | `Digraph`; no acyclicity | Too thin; define the small `FinDAG`/`FinODAG` locally |
| Mathlib `Tactic/Widget/StringDiagram.lean`, `Tactic/CategoryTheory/Monoidal/*` | Display of string diagrams, coherence normalization tactics | Proof aid only; no diagram objects |
| Mathlib PRs: #40482 "define directed acyclic graphs" (closed 2026-06-29, unmerged); #29926 FinStoch (closed, unmerged); #35684 "Kleisli PMF is a Markov category" (open) | — | Not available at the pin. Upstream `master` `3eae40f5eb25c5934211edf662d3b24c5afbe47a` has the same files in these directories as the pin |
| **Tau Ceti**, `TauCetiProject/TauCeti` `main` `911e17d69371df48f7bfddb0d0d2ebf3923b0c26` (Apache-2.0), Lean 4.37.0-rc1, Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. `TauCeti/CategoryTheory/Monoidal/Free/TensorSignature/{Basic,Interpretation,Substitution,Braided}.lean`, `Monoidal/Presentation.lean`, `Monoidal/EqToHom.lean` | `TensorSignature` (Joyal–Street tensor scheme: generating objects, coupons with source and target words; words are parenthesized `FreeMonoidalCategory` objects); `TensorSignature.FreeMonoidal` with `Hom.inductionOn`, `lift` into non-strict targets, uniqueness up to monoidal natural isomorphism; `Presented S R` (generators and relations) with its universal property; `FreeBraided`, `BraidedPresented`; `Substitution` (coupons replaced by expressions, shown to be the universal lift); `eqToHom` tensor lemmas. No `sorry` in the three files read (Basic 817 lines, Braided 468, Interpretation 356) | **Pattern and proof reference; attributed port of small pieces if needed.** Not imported: different toolchain (a release candidate), a very large dependency, parenthesized words and strong functors where the paper needs lists and strict functors, no symmetric quotient, no copy/discard. It shows that the algebraic free category on a signature, its universal property, generation by induction, and substitution are routine to formalize. PLAN.md D4 now takes this route for the strict symmetric case |
| Tau Ceti roadmap `DiagrammaticCoherence` (status at `7ca783d`, 2026-11-09) | Plan to prove diagrammatic coherence for the monoidal, braided, rigid, pivotal, braided-pivotal and ribbon rows, with geometric diagrams up to isotopy. Only the algebraic Layer 0 has begun; "no diagram categories" exist yet. The symmetric row (Joyal–Street I, Theorem 2.3) is not in its table | Nothing to reuse for C1 now. Worth rechecking before the optional Stage 7 |
| Tau Ceti `Combinatorics/Digraph/{Basic,DirectedCycle,…}.lean`, `Combinatorics/Hypergraph`, `Combinatorics/RibbonGraph` | Directed graphs with directed cycles; not inspected beyond file names | Possible reference for acyclicity lemmas; not needed at the planned size |
| **`robin-carlier/SymmMonCoherence`** `0cb94d5bcbddf2637423504af658a2f6e3319ef2` (Apache-2.0), Lean 4.29.0-rc6, Mathlib `891789085e407fba1a922860af840d00227aae69`; paper arXiv:2603.00896. `SymmMonCoherence/FreeSMC.lean` (643 lines, no `sorry`), `SList/*` | `FreeSymmetricMonoidalCategory` on a type of objects (terms modulo the axioms, `SymmetricCategory` instance, `Hom.inductionOn`), symmetric lists, coherence for symmetric monoidal categories | **Proof reference.** Object-generated only (no coupons), non-strict, old toolchain. The term-quotient pattern with a symmetry constructor is the one to follow; its coherence theorem is the input a later proof of C1 or C2 would want |
| **`apellis/string-diagrams-lean`** `8ae261b120e748db9f79fa3179028fa5617c996f` (Apache-2.0), Lean 4.34.1 | Diagrams as well-typed lists of layers `id ⊗ g ⊗ id`, presentations, interpretations, a strict monoidal category as a Mathlib `MonoidalCategory` with `eqToIso` associators (`StringDiagrams.Monoidal`), retyping along equalities of objects (`StringDiagrams.Transport`, `castHom`), induction over layers. Planar and linear; no symmetry | **Proof reference for strictness (D2)**: how to state and use laws across equalities of objects, and how a strict presented category is made a Mathlib monoidal category. Its layer-list diagrams do not carry the graph notions (levels, normal subgraphs, origins) the paper uses |
| `damast93/markovlib` `0788ceda609d76aaf03c79ee98e19bae052f806d` (no license), Lean 4.12.0-rc1 | Its own `MarkovCategory` class, deterministic morphisms, almost-sure equality | Unsuitable: superseded by Mathlib, unlicensed, old toolchain |

## Catalogues

| Source | Queries | Outcome |
|---|---|---|
| Pinned Mathlib (local source) | `string diagram`, `Stoch`, `Acyclic`, `strict`, free symmetric, directory listings | As in the table |
| Mathlib pull requests (`gh pr list --search`, all states) | free symmetric monoidal category; Markov category; copy discard category; strict monoidal category; symmetric monoidal coherence; PROP symmetric monoidal; string diagram category; directed acyclic graph | The PRs listed above; nothing on free symmetric monoidal categories or strict monoidal categories |
| GitHub repositories (`gh search repos`, language Lean) | markov category; string diagrams; symmetric monoidal; do-calculus; causal inference lean4; free markov category; PROP lean4 category; hypergraph category; categorical probability | The five repositories above; the last five queries returned nothing |
| GitHub code (`gh search code`) | `FreeSymmetricMonoidal`, `CopyDiscardCategory`, `FreeMarkov`, `Joyal Street progressive`, `MarkovCategory causal` (language Lean) | Carlier's repository; Mathlib and a copy of its files; nothing for the last three |
| Tau Ceti (`TauCeti`, `TauCetiRoadmap`) | `MarkovCategory`, `CopyDiscardCategory`, `string diagram`, `TensorSignature`, `causal`, `monoidal`; directory listings; two roadmap status files | As in the table; no Markov or copy-discard material |
| Lean Pool (`LeanPool/lean-pool`) | `MarkovCategory`, `monoidal` | No Markov categories; monoidal hits are in an unrelated project on Deligne and skein categories |
| Reservoir | markov, monoidal, string diagram, causal, category theory | One unrelated package (Markov semigroups); otherwise none. The search matches package names and descriptions only |
| Palomar | monoidal, Markov categor, string diagram, causal | None for the first three; three unrelated results for the last |
| Lean community projects page | page text filtered for markov, monoidal, diagram, causal, categor | No relevant entry |
| Formalpedia | Markov category; symmetric monoidal | 2 unrelated results; 135 results, first page unrelated (later pages not read) |
| Web search | Lean free symmetric monoidal string diagrams Joyal–Street; Lean Markov category; other proof assistants | Carlier's paper; reports of an Isabelle/HOL development on rewriting in PROPs (arXiv:2602.11035) and a Coq student project on symmetric string-diagram rewriting, neither read; no mechanization of Joyal–Street's theorem reported |

## Coverage limits

- TheoremSearch was not queried (it indexes theorems of papers, and its search
  did not run from a URL).
- One GitHub code query (`Symmetric` in files named `Free` in Tau Ceti) hit the
  rate limit and was not repeated; the directory listing of
  `Monoidal/Free/TensorSignature` shows no symmetric file.
- The Isabelle and Coq developments were seen only in search summaries.
- Tau Ceti and Lean Pool change daily; the commits above fix what was seen.

## Consequences for the plan

1. Use Mathlib's `MarkovCategory`; do not define a competing class.
2. Build the strict syntactic free symmetric monoidal category on a signature
   locally, following the term-quotient pattern of Mathlib, Tau Ceti and
   Carlier, and prove its universal property. Joyal–Street's theorem is then
   assumed in comparison form (PLAN.md, D4).
3. Keep the pins of the earlier projects; import none of the external
   developments. Credit any ported lemma to its source and license.
4. Repeat a focused search before Stage 1 proofs (diagram categories) and
   before the optional Stage 7.
