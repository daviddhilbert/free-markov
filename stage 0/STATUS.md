# Stage 0 status

Updated 2026-11-20. Plan: `formalization/PLAN.md`, Stage 0 and D2–D5.

**State: complete.** The "Done when" line of PLAN.md holds: the definitions
compile, the bridge and the universal property of `Syn_s(G)` are proved, the
trial is recorded (PLAN.md, D2 and D3).

## Verification

`python3 formalization/verify.py` (2026-11-20): **PASS**.

- `lake build FreeMarkovStage0`: exit code 0, 747 jobs, no warnings.
- `sorry` in sources: 0; `sorry` warnings in the build log: 0.
- Axioms: every one of the 341 declarations (133 theorems) uses only
  `propext`, `Classical.choice`, `Quot.sound`. Most use only `propext` and
  `Quot.sound`; `IsFreeOn.exists_iso` also uses `Classical.choice`.
- Cited results used: none (C1 and C2 enter in Stages 1 and 5).
- Trials `stage 0/trial/D2Interp.lean`, `D3Toy.lean`: exit 0, no `sorry`.
- Blueprint `formalization/blueprint/src/content.tex`: 50 nodes, 96 edges,
  14 formalized; labels unique, dependencies resolve, acyclic, every `\lean`
  name exists. Its PDF wrapper compiles with the cached tectonic (title font
  aside); the web version was not rendered (`leanblueprint` is not installed).


## Files (`stage 0/FreeMarkov/Stage0/`)

| File | Content |
|---|---|
| `Arrow.lean` | Equations in `Arrow C`: congruence for `≫`, identities, `eqToHom` |
| `GraphMonoid.lean` | `GraphMonoid`, `GraphMonoid.Hom` (id, comp), `words S`, `IsFreeOn`, `FreeGraphMonoid` (`isFreeOn`, `IsFreeOn.exists_iso`), `FreeDDGraphMonoid` |
| `Strict/Basic.lean` | `StrictSMC`, `StrictMarkov`; notation `⊗ₛ`, `σ_`, `δ_`, `ε_` |
| `Strict/Lemmas.lean` | `⊗` congruence, `eqToHom ⊗ eqToHom`, `hexagon_reverse`; `discard_one` (`ε_1 = 1`), `copy_one` (`δ_1 = 1`), `eq_discard` |
| `Strict/Bridge.lean` | Mathlib `MonoidalCategory`, `SymmetricCategory` instances (associators and unitors `eqToIso`, braiding `σ`) |
| `Strict/Markov.lean` | Mathlib `ComonObj`, `IsCommComonObj`, `MarkovCategory` instances (`Δ[a] = δ_a`, `ε[a] = ε_a`) |
| `Strict/Functor.lean` | `graphMonoid D`, `StrictFunctor`, `StrictMarkovFunctor` (ext, id, comp, induced graph monoid homomorphism), `ofMapCopy` |
| `Strict/Free.lean` | `FreeDDGraphMonoid.MatchesDupDisc`, `IsFreeMarkov` |
| `Syntactic/Basic.lean` | `Syn_s(G)`: `Term`, heterogeneous `Rel`, category, `StrictSMC` instance, inclusion `ι`, `gen` |
| `Syntactic/Universal.lean` | `Syn.induction` (generation), `interp`, `interp_sound`, `lift`, `lift_comp_ι`, `eq_lift`, `existsUnique_lift`, `strictFunctor_ext` |

## Readings of the paper fixed in Stage 0

None departs from the paper or from PLAN.md; recorded in PLAN.md (Stage 0
record) so that later stages keep them.

1. "`V(G)` is isomorphic to `W(S)` over `g`": `g` injective and the monoid
   homomorphism `W(S) → V(G)` extending `g` bijective (`IsFreeOn`). The library
   works with `V(G) = W(S)`; `IsFreeOn.exists_iso` justifies this.
2. `StrictSMC` has one hexagon and `σ_{b,a} σ_{a,b} = 1`; the other hexagon is
   a theorem; `σ_{a,1} = 1` is not assumed.
3. `StrictMarkov` has (1.1)–(1.3), with `1_A ⊗ σ_{AB} ⊗ 1_B` bracketed as
   `(1_a ⊗ σ_{a,b}) ⊗ 1_b`; `ε_1 = 1`, `δ_1 = 1` are theorems.
4. A strict Markov functor has both matching conditions as fields;
   `ofMapCopy` is the paper's "discards are matched automatically".
5. "Matches duplicates and discards" and "`f = F ∘ i`" are equations of graph
   monoid homomorphisms into the underlying graph monoid (arrows `Arrow D`).
6. `IsFreeMarkov` quantifies over targets in fixed universes `u'`, `v'` that
   are free parameters of it, so a freeness theorem holds for all of them.

## Layout decisions taken in Stage 0 (within PLAN.md)

- The verification script is `formalization/verify.py` (not `scripts/`),
  because the root `.gitignore` publishes `formalization/` and not `scripts/`.
- The blueprint is `formalization/blueprint/` for the same reason; it is a
  standard `leanblueprint` source tree.
