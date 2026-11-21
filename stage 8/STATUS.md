# Stage 8 status: the universal property for arbitrary Markov categories

Written 2026-11-21. Task: Stage 8 as recorded in the Stage 7 entry of `formalization/PLAN.md`
("Author's decision, 2026-11-20 (revising the same day's 'skip')"): the universal property of the
free Markov category for arbitrary (non-strict) Markov categories, with the strictification C2
(`Strictification M Str`) as a hypothesis. This goes beyond the paper, which only cites the result
(Introduction: Fritz 2020, Theorem 10.17; Fritz–Liang, Theorem 6.6).

## Result

**Done: items (a)–(e) are proved.** `python3 scripts/verify.py` ends with `RESULT: PASS` (all nine
libraries, 2026-11-21). Stage 8: 250 declarations (168 theorems), no `sorry`, no `axiom`, every
declaration uses only `propext`, `Classical.choice`, `Quot.sound`; `lake build FreeMarkovStage8` has
no warnings. Blueprint: 87 nodes, 206 edges, 85 formalized (8 new Stage 8 nodes).

Cited-hypothesis report for the unconditional forms (namespace `FreeMarkov.Combinatorial`, C1
discharged by Stage 7's `JoyalStreet.ofCombinatorial`): `exists_realize`, `restrict_isEquivalence`
and `prop_5_6_markov` have `FreeMarkov.Strictification` (C2) and nothing else in their types;
`extension_existsUnique`, `iso_existsUnique` have no cited hypothesis at all. The general forms (for
any `J : JoyalStreet …`, as in Stages 1–6) carry `JoyalStreet` and, for (b), (d), (e), `Strictification`.

| Item | Lean (general form) | Unconditional form | File |
|---|---|---|---|
| (a) interpretations, morphisms, category | `Interp G M`, `Interp.Hom`, `Interp.category` | — | `Interp.lean` |
| (a) restriction of Markov functors | `JoyalStreet.restrictObj`, `JoyalStreet.restrict` | `Combinatorial.restrict` | `Interp.lean`, `Uniqueness.lean` |
| (b) existence | `JoyalStreet.realize T I`, `realize_letter`, `realize_ar`, `restrict_realize`, `exists_realize` | `Combinatorial.exists_realize` | `Existence.lean` |
| (c) uniqueness | `JoyalStreet.extend`, `restrict_existsUnique`, `restrict_full`, `restrict_faithful`, `iso_existsUnique` | `Combinatorial.extension_existsUnique`, `Combinatorial.iso_existsUnique` | `Uniqueness.lean` |
| (d) equivalence (Fritz–Liang 6.6) | `JoyalStreet.restrict_essSurj`, `restrict_isEquivalence`, `restrictEquiv` | `Combinatorial.restrict_isEquivalence`, `Combinatorial.restrictEquiv` | `Equivalence.lean` |
| (e) Proposition 5.6, non-strict targets | `EffSig.markovData`, `EffSig.prop_5_6_markov` | `Combinatorial.prop_5_6_markov` (for `Cau(G)`, `G : FinODAG`) | `Effects.lean`, `Combinatorial.lean` |

Supporting files: `Products.lean` (left-bracketed products, comparison isomorphisms, monoidality
from single letters), `Functors.lean` (Markov functors in arbitrary universes and monoidal natural
transformations). 1 621 lines in all.

## The statements, in ordinary mathematical language (for the author's review)

Throughout: `G` is a free `DD`-graph monoid over an alphabet `S` (arrows `x : s(x) → t(x)` between
words, with the duplicates `δ_a : a → aa` and discards `ε_a : a → ∅`); `F_m(G)` is its free Markov
category `F_s(G)/S_M` (Stage 3, Theorem 4.1), built from the combinatorial diagrams in the
unconditional forms; `M` is a Markov category in Mathlib's sense (symmetric monoidal, not
necessarily strict, in any universe). For a function `ob` from letters to objects of `M` and a word
`w = a_1 … a_n`, `lp(ob, w) = (…((ob a_1 ⊗ ob a_2) ⊗ ob a_3) …) ⊗ ob a_n`, with `lp(ob, ∅) = 1` and
`lp(ob, a) = ob a`: the left-bracketed product, i.e. the object `eval(ob a_1 … ob a_n)` that C2
fixes (Section 5, displayed definition of `eval`).

**Markov functors and their transformations** (`MarkovFun`, `MarkovFun.Hom`). A Markov functor is
as in the Introduction and Stage 6 (a strong symmetric monoidal functor with
`μ⁻¹ ∘ F(δ_X) = δ_{FX}` and `ε⁻¹ ∘ F(ε_X) = ε_{FX}`); the fields are those of Stage 6's
`MarkovFunctor`, but source and target may live in different universes (needed because `F_m(G)` and
targets such as `FinStoch` need not share universes; for equal universes the two notions coincide,
`MarkovFunctor.equivMarkovFun`). A morphism of Markov functors is a **monoidal natural
transformation** `θ : F → F'`: natural, with `θ_1 ∘ ε_F = ε_{F'}` and
`θ_{X⊗Y} ∘ μ_F = μ_{F'} ∘ (θ_X ⊗ θ_Y)` (Mathlib's `NatTrans.IsMonoidal`). Hypotheses: none.

**(a) Interpretations.** An *interpretation* `I` of `G` in `M` consists of an object `ob(a)` of `M`
for every letter `a` and a morphism `I(x) : lp(ob, s(x)) → lp(ob, t(x))` for every arrow `x` of `G`,
such that `I(δ_a) = δ_{ob(a)}` and `I(ε_a) = ε_{ob(a)}` (as morphisms of `M`; `s(δ_a) = a`,
`t(δ_a) = aa` hold only up to the identification `V(G) = W(S)`, so the equations are stated as
equalities of arrows). A *morphism of interpretations* `α : I → I'` is a family of morphisms
`α_a : ob(a) → ob'(a)` with `I'(x) ∘ (α_{a_1} ⊗ … ⊗ α_{a_n}) = (α_{b_1} ⊗ … ⊗ α_{b_m}) ∘ I(x)` for
every arrow `x : a_1 … a_n → b_1 … b_m` (left-bracketed products of the `α`; in particular for the
duplicates and discards, so the `α_a` commute with them). Interpretations and their morphisms form a
category. The *restriction* of a Markov functor `F : F_m(G) → M` is the interpretation
`F|_G = (F(a), φ_{t(x)}⁻¹ ∘ F(x) ∘ φ_{s(x)})`, where
`φ_w : lp(F, w) = (…(F a_1 ⊗ F a_2) …) ⊗ F a_n ≅ F(a_1 … a_n)` is the comparison isomorphism built
from the structure isomorphisms `ε`, `μ` of `F`; the restriction of a monoidal natural
transformation is its family of components on the letters. This is a functor
`restrict : MarkovFun(F_m(G), M) → Interp(G, M)`. Hypotheses: C1 (`J`) in the general form, none in
the unconditional form.

**(b) Existence.** For every interpretation `I` there is a Markov functor `F_I^M : F_m(G) → M` whose
restriction is isomorphic to `I`; indeed `F_I^M(a) = ob(a)` for every letter (`realize_letter`),
`F_I^M|_G(x)` equals `I(x)` as a morphism of `M` (`realize_ar`), and the isomorphism of
interpretations has identity components (`restrict_realize`). Construction: the homomorphism
`G → str(M)` sending `a` to the one-letter word `ob(a)` and `x` to the unique morphism of `str(M)`
that `eval` sends to `ψ_{t(x)} ∘ I(x) ∘ ψ_{s(x)}⁻¹` (`ψ_w : lp(ob, w) ≅ eval(ob a_1 … ob a_n)` the
comparison isomorphism of `eval`; fullness and faithfulness of `eval`); it matches duplicates and
discards (`toStrHom_matches`, because `eval` is a Markov functor); Theorem 4.1 gives a strict
Markov functor `F_I : F_m(G) → str(M)`, and `F_I^M = eval ∘ F_I`. Hypotheses: C1 (`J`) and C2
(`T`) in the general form, C2 only in the unconditional form.

**(c) Uniqueness.** Let `F, F' : F_m(G) → M` be Markov functors and `α : F|_G → F'|_G` a morphism
of interpretations. Then there is exactly one monoidal natural transformation `θ : F → F'` whose
components on the letters are the `α_a` (`restrict_existsUnique`); it is
`θ_w = φ'_w ∘ (α_{a_1} ⊗ … ⊗ α_{a_n}) ∘ φ_w⁻¹`. Consequently the restriction functor is full and
faithful, and every isomorphism `F|_G ≅ F'|_G` lifts to exactly one monoidal natural isomorphism
`F ≅ F'` (`iso_existsUnique`). Hypotheses: C1 (`J`) in the general form, **none** in the
unconditional form; C2 is not used.

**(d) The equivalence.** Restriction to the generators is an equivalence of categories between
Markov functors `F_m(G) → M` with monoidal natural transformations and interpretations of `G` in
`M` with their morphisms (`restrict_isEquivalence`: full, faithful, essentially surjective;
`restrictEquiv` is the `Equivalence`). Hypotheses: C1 (`J`) and C2 (`T`) in the general form, C2
only in the unconditional form.

**(e) Proposition 5.6 for non-strict targets.** Let `K = (S_1, …, S_n)` be sets with acyclic
associated graph (Stage 5's `EffSig`; for an ordered DAG `G`, `S_i` the parents of `v_i`, and then
`F_m(W(K)) = Cau(G)`), let `F : F_m(W(K)) → M` be a Markov functor, and let
`[T ‖ S]^M` be the effect in `M` (end of Section 5, Stage 5's `MData.effect`) formed from the objects
`a_i = F(v_i)` and the morphisms
`κ_i^M = ψ_{S_i}⁻¹ ∘ φ_{S_i} ∘ F(κ_i) : eval(w_{S_i}) → F(v_i)` (`markovData`; this is `F(κ_i)` read
through the structure isomorphisms of `F` and of `eval`). Then
`F([v_T ‖ v_S]) = φ_T ∘ ψ_T⁻¹ ∘ [T ‖ S]^M ∘ ψ_S ∘ φ_S⁻¹` (`EffSig.prop_5_6_markov`), where
`φ_S : F(v_{s_1}) ⊗ … ⊗ F(v_{s_k}) ≅ F(v_S)` (left-bracketed) comes from `μ` of `F` and
`ψ_S : F(v_{s_1}) ⊗ … ⊗ F(v_{s_k}) ≅ eval(w_S)` from `μ` of `eval`. So `F([v_T ‖ v_S])` is the
effect formed from the `F(κ_i)`, up to the comparison isomorphisms. This is the general statement
(for every Markov functor, not only for those produced by (b)). Hypotheses: C1 (`J`) and C2 (`T`)
in the general form, C2 only in `Combinatorial.prop_5_6_markov` (stated for `Cau(G)` and the causal
effects `causalEffectSets` of Section 6).

## Relation to Fritz–Liang, Theorem 6.6, and to the Introduction of the paper

- **Fritz–Liang, Theorem 6.6** (as cited in the task: `gsCat(FreeMarkov_Σ, C) ≃ CatHyp(Σ, hyp(C))`):
  (d) is the same form — an equivalence, given by restriction to the generators, between the
  category of (strong, Markov) functors out of the free Markov category with monoidal natural
  transformations and a category of interpretations of the signature in the target. The signatures
  here are free `DD`-graph monoids (arrows between words of letters) rather than Fritz–Liang's
  hypergraph signatures, and the interpretations here use left-bracketed products in `M`. The
  Fritz–Liang paper is not in the project folder and was not consulted, so the comparison is with
  the statement as cited, not with their definitions line by line. Their strict version,
  Corollary 6.7, corresponds to Theorem 4.1 (Stage 3) and to Stage 7's `fsM_unique_iso`.
- **The Introduction's other sentence** ("the restriction to strict Markov categories is harmless,
  since every Markov category is comonoid equivalent to a strict one", Fritz, Theorem 10.17): C2 is
  the form of this used here; only clauses 1–5 of C2 (no essential surjectivity, no quasi-inverse,
  no `EvalStrict`) are needed.

## C2 clauses used

`words` (through `Strictification.letter`), `eval`, `braided`, `map_copy`, `map_discard`, `full`,
`faithful`, `eval_of`. Not used: `eval_one`, `eval_snoc` (the comparison `lp(ob, w) ≅ eval(w)` is
built from `μ` of `eval`, not from the object equations), and `EvalStrict`. No clause beyond C2 was
needed: essential surjectivity of `eval` and an inverse on objects are not used, because
interpretations are given directly by objects of `M` and lifted along one-letter words.

## Readings fixed (within the plan; no accepted statement or hypothesis changed)

1. **Typing of interpretations.** "A morphism `eval(s(x)) → eval(t(x))` between the left-bracketed
   products fixed by C2" is read with the left-bracketed product `lp` defined directly in `M`, so
   that the category of interpretations does not depend on `T`. C2 makes `eval(ob a_1 … ob a_n)`
   equal to `lp` on objects (`eval_one`, `eval_of`, `eval_snoc`), but the comparison used in (b) is
   the isomorphism `ψ` built from `μ` of `eval`, because C2 does not say that `μ_{v, a}` is an
   identity; with `ψ` the restriction of the extension is `I` itself (up to the identities on
   letters), with the bare object equations it would only be isomorphic to a conjugate of `I`.
2. **Matching duplicates and discards** in an interpretation is stated as equality of arrows of `M`
   (`Arrow.mk (I(δ_a)) = Arrow.mk δ_{ob a}`), because `s(δ_a) = a`, `t(δ_a) = aa` hold only
   propositionally in a `FreeDDGraphMonoid` (the convention of Stages 0–7).
3. **Morphisms of interpretations** commute with every arrow of `G`, the duplicates and discards
   included (so their components are comonoid morphisms); this is what makes (c) and (d) true —
   a monoidal natural transformation between Markov functors is natural at `δ_a`, `ε_a`.
4. **Restriction** uses the comparison isomorphisms `φ` of `F`; for a strict functor (structure
   isomorphisms identities) it is the plain restriction to generators.
5. **(e)** is stated with the comparison isomorphisms written out (`φ`, `ψ`) rather than "up to `μ`";
   `κ_i^M` is `ψ⁻¹ ∘ φ ∘ F(κ_i)`. Both sides are morphisms `F(v_S) → F(v_T)`; the equation is an
   equation of morphisms, not only of arrows.

## Proof methods

- (c) by the generation principle in the quotient (`JoyalStreet.inductionM`, from Stage 1's
  `JoyalStreet.induction`): naturality on generators is the hypothesis on `α`; on symmetries and
  monoidal products it follows from monoidality of `θ`, which is proved from the letters by the
  coherence of `μ` (`tensor_of_snoc`: compatibility with `ε` and with `μ_{X, a}` for letters `a`
  implies compatibility with all `μ_{X, Y}`, by induction on `Y` with the associativity and unit
  axioms of strong monoidal functors). Uniqueness: monoidal natural transformations commute with
  the comparison isomorphisms (`cmpR_naturality`).
- (b) through Stage 5's `JoyalStreet.lift` (Theorem 4.1), with the comparison isomorphisms of the
  composite `eval ∘ F_I` identified with those of `eval` (`cmpR_comp_strict`).
- (e) from (b) and (c): `F ≅ eval ∘ F_{F|_G}` by the unique monoidal natural isomorphism lifting the
  identity components of `restrict_realize`; its components on words are computed from the
  comparison isomorphisms (`app_of_eqToHom`); the strict functor `F_{F|_G}` is the functor
  `F_{(W,K)}` of Stage 5 for the data `markovData` (both lift the same homomorphism `W(K) → str(M)`,
  `toHom_eq`), so the effect in `M` is `eval` of `F_{F|_G}` of the free effect.

## Changes outside `stage 8/`

- `lakefile.toml`: library `FreeMarkovStage8` (`srcDir = "stage 8"`) added and made a default target.
- `scripts/verify.py`: Stage 8 added to `STAGES`.
- `formalization/blueprint/src/content.tex`: new section "The universal property for arbitrary
  Markov categories (Stage 8)", nodes `s8:markovfun`, `s8:products`, `s8:interp`, `s8:unique`,
  `s8:exist`, `s8:equiv`, `s8:prop56`, `s8:uncond`, all formalized.
- `formalization/REUSE-SURVEY.md`: section "Focused search before Stage 8" (Mathlib at the pin:
  `NatTrans.IsMonoidal` used; no strictification, no Markov functors in Mathlib).
- `formalization/PLAN.md`: Stage 8 record.
- No Stage 0–7 source was changed; no defect found; no paper feedback; nothing installed or
  imported beyond the pinned Mathlib already on disk (`Mathlib.CategoryTheory.Monoidal.NaturalTransformation`).
