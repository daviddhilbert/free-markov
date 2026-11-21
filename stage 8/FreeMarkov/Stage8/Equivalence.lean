/-
Free Markov categories, Stage 8: the universal property of the free Markov category for arbitrary
Markov categories, in the form of Fritz–Liang, Theorem 6.6 (item (d)).

For a free `DD`-graph monoid `G`, the free Markov category `F_s(G)/S_M` (`J.FsM`) and a Markov
category `M` with a strictification `T : Strictification M Str` (C2):

* `JoyalStreet.restrict_essSurj`: the restriction functor is essentially surjective (item (b));
* `JoyalStreet.restrict_isEquivalence`: **(d)** restriction to the generators is an equivalence
  between the category of Markov functors `F_s(G)/S_M → M` with monoidal natural transformations and
  the category of interpretations of `G` in `M` (full and faithful by item (c));
* `JoyalStreet.restrictEquiv`: the equivalence itself.

The cited results used: C1 (`J`) and C2 (`T`).
-/
module

public import FreeMarkov.Stage8.Existence

@[expose] public section

universe w v u v'

namespace FreeMarkov

open CategoryTheory

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S}
  {M : Type u} [Category.{v'} M] [MonoidalCategory M] [MarkovCategory M]
  {Str : Type u} [Monoid Str] [Category.{v'} Str] [StrictMarkov Str]

namespace JoyalStreet

variable (J : JoyalStreet G.toFreeGraphMonoid) (T : Strictification M Str)

include T in
/-- **(b)** The restriction functor is essentially surjective. -/
theorem restrict_essSurj : (J.restrict (M := M)).EssSurj :=
  ⟨fun I => ⟨J.realize T I, ⟨J.restrict_realize T I⟩⟩⟩

include T in
/-- **(d)**, in the form of Fritz–Liang, Theorem 6.6: restriction to the generators is an
equivalence between the category of Markov functors `F_s(G)/S_M → M` and monoidal natural
transformations and the category of interpretations of `G` in `M`. -/
theorem restrict_isEquivalence : (J.restrict (M := M)).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := J.restrict_essSurj T

include T in
/-- **(d)** The equivalence `MarkovFun (F_s(G)/S_M) M ≌ Interp G M` given by restriction. -/
noncomputable def restrictEquiv : MarkovFun J.FsM M ≌ Interp G M :=
  haveI := J.restrict_isEquivalence T
  (J.restrict (M := M)).asEquivalence

theorem restrictEquiv_functor : (J.restrictEquiv T).functor = J.restrict (M := M) := rfl

end JoyalStreet

end FreeMarkov
