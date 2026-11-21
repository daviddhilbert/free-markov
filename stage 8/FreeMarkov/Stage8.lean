/-
Free Markov categories, Stage 8 (beyond the paper): the universal property of the free Markov
category for arbitrary (non-strict) Markov categories, with the strictification C2 as hypothesis.

* `Products`: left-bracketed products, comparison isomorphisms of strong monoidal functors out of a
  strict monoidal category, monoidality from single letters.
* `Functors`: Markov functors in arbitrary universes (`MarkovFun`), monoidal natural transformations,
  the category of Markov functors; strict Markov functors as Markov functors.
* `Interp`: **(a)** interpretations of a free `DD`-graph monoid in a Markov category and their
  morphisms; restriction of Markov functors out of `F_s(G)/S_M`.
* `Uniqueness`: **(c)** extension of morphisms of interpretations to unique monoidal natural
  transformations; the restriction functor is full and faithful.
* `Existence`: **(b)** every interpretation extends, through `G → str(M)`, Theorem 4.1 and `eval`.
* `Equivalence`: **(d)** restriction is an equivalence (Fritz–Liang, Theorem 6.6).
* `Effects`: **(e)** Proposition 5.6 for Markov functors into arbitrary Markov categories.
* `Combinatorial`: the unconditional forms (C1 discharged by Stage 7).
-/
module

public import FreeMarkov.Stage8.Products
public import FreeMarkov.Stage8.Functors
public import FreeMarkov.Stage8.Interp
public import FreeMarkov.Stage8.Uniqueness
public import FreeMarkov.Stage8.Existence
public import FreeMarkov.Stage8.Equivalence
public import FreeMarkov.Stage8.Effects
public import FreeMarkov.Stage8.Combinatorial
