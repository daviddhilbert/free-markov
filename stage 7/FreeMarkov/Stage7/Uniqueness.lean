/-
Free Markov categories, Stage 7 (follow-up): uniqueness of the free (symmetric strict monoidal,
resp. strict Markov) category over a free (`DD`-)graph monoid.

* `IsFreeMarkov.unique_iso`: if `C` and `C'` are free strict Markov categories over the same free
  `DD`-graph monoid `G`, via `i : G → C` and `i' : G → C'`, there is exactly one strict Markov
  functor `F : C → C'` with `i' = F ∘ i`, and it is an isomorphism: there is a strict Markov functor
  `F' : C' → C` with `i = F' ∘ i'`, `F' ∘ F = 1_C` and `F ∘ F' = 1_{C'}`.
* `IsFreeSymmetric.unique_iso`: the same for free symmetric strict monoidal categories over a free
  graph monoid and strict symmetric monoidal functors (Section 2).
* `Combinatorial.fsM_unique_iso`, `Combinatorial.fsC_unique_iso`: every strict Markov category
  with the universal property of Theorem 4.1 is isomorphic to `F_s(G)/S_M` by exactly one strict
  Markov functor compatible with the homomorphisms from `G`; likewise for `F_s(G)` and Theorem 2.3.

Universes.  `IsFreeMarkov C G i` quantifies over targets in one pair of universes, which are
parameters of the statement.  The argument uses the universal property of `C` with the targets `C'`
(existence of `F`) and `C` (for `F' ∘ F = 1_C`), and that of `C'` with the targets `C` and `C'`, so
the general forms take the four instances as hypotheses; when `C` and `C'` live in the same
universes two hypotheses suffice (`unique_iso'`).  Theorems 2.3 and 4.1 hold for every target
universe, so the corollaries for `F_s(G)` and `F_s(G)/S_M` need only the universal property of the
other category, at the universes of `F_s(G)` (resp. `F_s(G)/S_M`) and at its own.
-/
module

public import FreeMarkov.Stage7.JoyalStreet

@[expose] public section

universe w w₂ u₁ v₁ u₂ v₂ u₃ v₃ u v

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov

/-! ### Graph monoid homomorphisms of composite functors -/

namespace StrictFunctor

variable {C : Type u₁} [Monoid C] [Category.{v₁} C] [StrictSMC C]
  {D : Type u₂} [Monoid D] [Category.{v₂} D] [StrictSMC D]
  {E : Type u₃} [Monoid E] [Category.{v₃} E] [StrictSMC E]

theorem toGraphMonoidHom_comp (K : StrictFunctor D E) (F : StrictFunctor C D) :
    (K.comp F).toGraphMonoidHom = K.toGraphMonoidHom.comp F.toGraphMonoidHom :=
  GraphMonoid.Hom.ext (MonoidHom.ext fun _ => rfl) rfl

theorem toGraphMonoidHom_id :
    (StrictFunctor.id C).toGraphMonoidHom = GraphMonoid.Hom.id (graphMonoid C) :=
  GraphMonoid.Hom.ext (MonoidHom.ext fun _ => rfl) rfl

/-- `(K ∘ F) ∘ i = K ∘ (F ∘ i)` on underlying graph monoid homomorphisms. -/
theorem toGraphMonoidHom_comp_comp {G : GraphMonoid.{w, w₂}} (K : StrictFunctor D E)
    (F : StrictFunctor C D) (i : G.Hom (graphMonoid C)) :
    (K.comp F).toGraphMonoidHom.comp i = K.toGraphMonoidHom.comp (F.toGraphMonoidHom.comp i) := by
  rw [toGraphMonoidHom_comp]; rfl

theorem toGraphMonoidHom_id_comp {G : GraphMonoid.{w, w₂}} (i : G.Hom (graphMonoid C)) :
    (StrictFunctor.id C).toGraphMonoidHom.comp i = i := by
  rw [toGraphMonoidHom_id]; rfl

end StrictFunctor

/-! ### Free symmetric strict monoidal categories -/

section Symmetric

variable {C : Type u₁} [Monoid C] [Category.{v₁} C] [StrictSMC C]
  {C' : Type u₂} [Monoid C'] [Category.{v₂} C'] [StrictSMC C']
  {S : Type w} {G : FreeGraphMonoid.{w, w₂} S}
  {i : G.toGraphMonoid.Hom (graphMonoid C)} {i' : G.toGraphMonoid.Hom (graphMonoid C')}

/-- **Uniqueness of the free symmetric strict monoidal category** (Section 2, after Theorem 2.3).
If `C` and `C'` are free over `G` via `i` and `i'`, there is exactly one strict symmetric monoidal
functor `F : C → C'` with `i' = F ∘ i`, and every such `F` is an isomorphism, with inverse the
strict functor `F'` with `i = F' ∘ i'`.  The four hypotheses are the universal properties of `C`
and `C'` for targets in the universes of `C` and of `C'`. -/
theorem IsFreeSymmetric.unique_iso (hC : IsFreeSymmetric.{w, w₂, u₂, v₂, u₁, v₁} C G i)
    (hC₁ : IsFreeSymmetric.{w, w₂, u₁, v₁, u₁, v₁} C G i)
    (hC' : IsFreeSymmetric.{w, w₂, u₁, v₁, u₂, v₂} C' G i')
    (hC'₁ : IsFreeSymmetric.{w, w₂, u₂, v₂, u₂, v₂} C' G i') :
    (∃! F : StrictFunctor C C', i' = F.toGraphMonoidHom.comp i) ∧
      ∀ F : StrictFunctor C C', i' = F.toGraphMonoidHom.comp i →
        ∃ F' : StrictFunctor C' C, i = F'.toGraphMonoidHom.comp i' ∧
          F'.comp F = StrictFunctor.id C ∧ F.comp F' = StrictFunctor.id C' := by
  refine ⟨hC.existsUnique_lift C' i', fun F hF => ?_⟩
  obtain ⟨F', hF', -⟩ := hC'.existsUnique_lift C i
  refine ⟨F', hF', ?_, ?_⟩
  · obtain ⟨_, -, u⟩ := hC₁.existsUnique_lift C i
    refine (u _ ?_).trans (u _ ?_).symm
    · change i = (F'.comp F).toGraphMonoidHom.comp i
      rw [StrictFunctor.toGraphMonoidHom_comp_comp, ← hF, ← hF']
    · exact (StrictFunctor.toGraphMonoidHom_id_comp i).symm
  · obtain ⟨_, -, u⟩ := hC'₁.existsUnique_lift C' i'
    refine (u _ ?_).trans (u _ ?_).symm
    · change i' = (F.comp F').toGraphMonoidHom.comp i'
      rw [StrictFunctor.toGraphMonoidHom_comp_comp, ← hF', ← hF]
    · exact (StrictFunctor.toGraphMonoidHom_id_comp i').symm

end Symmetric

/-- `IsFreeSymmetric.unique_iso` for `C`, `C'` in the same universes. -/
theorem IsFreeSymmetric.unique_iso' {C : Type u} [Monoid C] [Category.{v} C] [StrictSMC C]
    {C' : Type u} [Monoid C'] [Category.{v} C'] [StrictSMC C']
    {S : Type w} {G : FreeGraphMonoid.{w, w₂} S}
    {i : G.toGraphMonoid.Hom (graphMonoid C)} {i' : G.toGraphMonoid.Hom (graphMonoid C')}
    (hC : IsFreeSymmetric.{w, w₂, u, v, u, v} C G i)
    (hC' : IsFreeSymmetric.{w, w₂, u, v, u, v} C' G i') :
    (∃! F : StrictFunctor C C', i' = F.toGraphMonoidHom.comp i) ∧
      ∀ F : StrictFunctor C C', i' = F.toGraphMonoidHom.comp i →
        ∃ F' : StrictFunctor C' C, i = F'.toGraphMonoidHom.comp i' ∧
          F'.comp F = StrictFunctor.id C ∧ F.comp F' = StrictFunctor.id C' :=
  IsFreeSymmetric.unique_iso hC hC hC' hC'

/-! ### Free strict Markov categories -/

section Markov

variable {C : Type u₁} [Monoid C] [Category.{v₁} C] [StrictMarkov C]
  {C' : Type u₂} [Monoid C'] [Category.{v₂} C'] [StrictMarkov C']
  {S : Type w} {G : FreeDDGraphMonoid.{w, w₂} S}
  {i : G.toGraphMonoid.Hom (graphMonoid C)} {i' : G.toGraphMonoid.Hom (graphMonoid C')}

/-- **Uniqueness of the free strict Markov category** (Introduction).  If `C` and `C'` are free
strict Markov categories over the free `DD`-graph monoid `G`, via `i` and `i'`, there is exactly one
strict Markov functor `F : C → C'` with `i' = F ∘ i`, and every such `F` is an isomorphism: there is
a strict Markov functor `F' : C' → C` with `i = F' ∘ i'`, `F' ∘ F = 1_C` and `F ∘ F' = 1_{C'}`.
The four hypotheses are the universal properties of `C` and `C'` for targets in the universes of
`C` and of `C'`. -/
theorem IsFreeMarkov.unique_iso (hC : IsFreeMarkov.{w, w₂, v₁, u₁, v₂, u₂} C G i)
    (hC₁ : IsFreeMarkov.{w, w₂, v₁, u₁, v₁, u₁} C G i)
    (hC' : IsFreeMarkov.{w, w₂, v₂, u₂, v₁, u₁} C' G i')
    (hC'₁ : IsFreeMarkov.{w, w₂, v₂, u₂, v₂, u₂} C' G i') :
    (∃! F : StrictMarkovFunctor C C', i' = F.toGraphMonoidHom.comp i) ∧
      ∀ F : StrictMarkovFunctor C C', i' = F.toGraphMonoidHom.comp i →
        ∃ F' : StrictMarkovFunctor C' C, i = F'.toGraphMonoidHom.comp i' ∧
          F'.comp F = StrictMarkovFunctor.id C ∧ F.comp F' = StrictMarkovFunctor.id C' := by
  refine ⟨hC.existsUnique_lift C' i' hC'.matchesDupDisc, fun F hF => ?_⟩
  obtain ⟨F', hF', -⟩ := hC'.existsUnique_lift C i hC.matchesDupDisc
  refine ⟨F', hF', ?_, ?_⟩
  · obtain ⟨_, -, u⟩ := hC₁.existsUnique_lift C i hC.matchesDupDisc
    refine (u _ ?_).trans (u _ ?_).symm
    · change i = (F'.toStrictFunctor.comp F.toStrictFunctor).toGraphMonoidHom.comp i
      rw [StrictFunctor.toGraphMonoidHom_comp_comp, ← hF, ← hF']
    · exact (StrictFunctor.toGraphMonoidHom_id_comp i).symm
  · obtain ⟨_, -, u⟩ := hC'₁.existsUnique_lift C' i' hC'.matchesDupDisc
    refine (u _ ?_).trans (u _ ?_).symm
    · change i' = (F.toStrictFunctor.comp F'.toStrictFunctor).toGraphMonoidHom.comp i'
      rw [StrictFunctor.toGraphMonoidHom_comp_comp, ← hF', ← hF]
    · exact (StrictFunctor.toGraphMonoidHom_id_comp i').symm

end Markov

/-- `IsFreeMarkov.unique_iso` for `C`, `C'` in the same universes. -/
theorem IsFreeMarkov.unique_iso' {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C]
    {C' : Type u} [Monoid C'] [Category.{v} C'] [StrictMarkov C']
    {S : Type w} {G : FreeDDGraphMonoid.{w, w₂} S}
    {i : G.toGraphMonoid.Hom (graphMonoid C)} {i' : G.toGraphMonoid.Hom (graphMonoid C')}
    (hC : IsFreeMarkov.{w, w₂, v, u, v, u} C G i) (hC' : IsFreeMarkov.{w, w₂, v, u, v, u} C' G i') :
    (∃! F : StrictMarkovFunctor C C', i' = F.toGraphMonoidHom.comp i) ∧
      ∀ F : StrictMarkovFunctor C C', i' = F.toGraphMonoidHom.comp i →
        ∃ F' : StrictMarkovFunctor C' C, i = F'.toGraphMonoidHom.comp i' ∧
          F'.comp F = StrictMarkovFunctor.id C ∧ F.comp F' = StrictMarkovFunctor.id C' :=
  IsFreeMarkov.unique_iso hC hC hC' hC'

/-! ### Comparison with `F_s(G)` and `F_s(G)/S_M` -/

namespace Combinatorial

/-- **Any free symmetric strict monoidal category over `G` is `F_s(G)`**, unconditional: if `C`
has the universal property of Theorem 2.3 via `i` (for targets in the universes of `F_s(G)` and in
its own), there is exactly one strict symmetric monoidal functor `F : F_s(G) → C` with
`i = F ∘ ι`, and it is an isomorphism. -/
theorem fsC_unique_iso {S : Type w} (G : FreeGraphMonoid.{w, w₂} S) {C : Type u} [Monoid C]
    [Category.{v} C] [StrictSMC C] {i : G.toGraphMonoid.Hom (graphMonoid C)}
    (hC : IsFreeSymmetric.{w, w₂, w, max w w₂, u, v} C G i)
    (hC₁ : IsFreeSymmetric.{w, w₂, u, v, u, v} C G i) :
    (∃! F : StrictFunctor (FsC G) C, i = F.toGraphMonoidHom.comp (FsC.ι G)) ∧
      ∀ F : StrictFunctor (FsC G) C, i = F.toGraphMonoidHom.comp (FsC.ι G) →
        ∃ F' : StrictFunctor C (FsC G), FsC.ι G = F'.toGraphMonoidHom.comp i ∧
          F'.comp F = StrictFunctor.id (FsC G) ∧ F.comp F' = StrictFunctor.id C :=
  IsFreeSymmetric.unique_iso (theorem_2_3 G) (theorem_2_3 G) hC hC₁

/-- **Any free strict Markov category over `G` is `F_s(G)/S_M`**, unconditional: if a strict Markov
category `C` has the universal property of Theorem 4.1 via `i : G → C` (for targets in the universes
of `F_s(G)/S_M` and in its own), there is exactly one strict Markov functor
`F : F_s(G)/S_M → C` with `i = F ∘ i_m`, and it is an isomorphism (its inverse is the strict Markov
functor `F'` with `i_m = F' ∘ i`).

With Fritz–Liang, *Free gs-monoidal categories and free Markov categories* (Corollary 6.7; cited,
not formalized), which shows that their construction of the free Markov category over `G` has this
universal property, this identifies the two constructions: Fritz–Liang's free Markov category (in
its strict form) and the graphical `F_s(G)/S_M` are isomorphic by a unique strict Markov functor
compatible with the homomorphisms from `G`. -/
theorem fsM_unique_iso {S : Type w} (G : FreeDDGraphMonoid.{w, w₂} S) {C : Type u} [Monoid C]
    [Category.{v} C] [StrictMarkov C] {i : G.toGraphMonoid.Hom (graphMonoid C)}
    (hC : IsFreeMarkov.{w, w₂, v, u, max w w₂, w} C G i)
    (hC₁ : IsFreeMarkov.{w, w₂, v, u, v, u} C G i) :
    (∃! F : StrictMarkovFunctor (FsM G) C,
        i = F.toGraphMonoidHom.comp (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).iM) ∧
      ∀ F : StrictMarkovFunctor (FsM G) C,
        i = F.toGraphMonoidHom.comp (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).iM →
        ∃ F' : StrictMarkovFunctor C (FsM G),
          (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).iM = F'.toGraphMonoidHom.comp i ∧
          F'.comp F = StrictMarkovFunctor.id (FsM G) ∧ F.comp F' = StrictMarkovFunctor.id C :=
  IsFreeMarkov.unique_iso (theorem_4_1 G) (theorem_4_1 G) hC hC₁

end Combinatorial

end FreeMarkov
