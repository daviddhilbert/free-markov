/-
Free Markov categories, Stage 8: the unconditional forms (C1 discharged by Stage 7's
`JoyalStreet.ofCombinatorial`); only the strictification C2 remains as a hypothesis.

For a free `DD`-graph monoid `G` and `F_m(G) = Combinatorial.FsM G` (the combinatorial free Markov
category `F_s(G)/S_M`), a Markov category `M`:

* `Combinatorial.restrict`: restriction to the generators, `MarkovFun (F_m(G)) M ⥤ Interp G M`;
* `Combinatorial.extension_existsUnique`, `Combinatorial.iso_existsUnique`: **(c)**, no hypothesis;
* `Combinatorial.exists_realize`: **(b)**, with `T : Strictification M Str`;
* `Combinatorial.restrict_isEquivalence`, `Combinatorial.restrictEquiv`: **(d)** (Fritz–Liang,
  Theorem 6.6), with `T`;
* `Combinatorial.prop_5_6_markov`: **(e)** for the causal category `Cau(G)` of an ordered DAG `G`
  (Section 6) and a Markov functor `F : Cau(G) → M` (a model in the sense of the application), with
  `T`.
-/
module

public import FreeMarkov.Stage8.Effects
public import FreeMarkov.Stage7.JoyalStreet

@[expose] public section

universe w v u v'

namespace FreeMarkov

namespace Combinatorial

open CategoryTheory FinODAG

variable {M : Type u} [Category.{v'} M] [MonoidalCategory M] [MarkovCategory M]
  {Str : Type u} [Monoid Str] [Category.{v'} Str] [StrictMarkov Str]

section General

variable {S : Type w} (G : FreeDDGraphMonoid.{w, v} S)

/-- The instance of C1 for `G` (Stage 7). -/
noncomputable abbrev jsDD : JoyalStreet G.toFreeGraphMonoid :=
  JoyalStreet.ofCombinatorial G.toFreeGraphMonoid

/-- Restriction of Markov functors `F_m(G) → M` to the generators. -/
noncomputable abbrev restrict : MarkovFun (FsM G) M ⥤ Interp G M := (jsDD G).restrict

/-- **(c)**, unconditional: a morphism of interpretations between the restrictions of two Markov
functors `F_m(G) → M` extends to exactly one monoidal natural transformation. -/
theorem extension_existsUnique {F F' : MarkovFun (FsM G) M}
    (α : (restrict G).obj F ⟶ (restrict G).obj F') : ∃! θ : F ⟶ F', (restrict G).map θ = α :=
  (jsDD G).restrict_existsUnique α

/-- **(c)**, unconditional: an isomorphism between the restrictions lifts to exactly one monoidal
natural isomorphism. -/
theorem iso_existsUnique {F F' : MarkovFun (FsM G) M}
    (e : (restrict G).obj F ≅ (restrict G).obj F') : ∃! θ : F ≅ F', (restrict G).mapIso θ = e :=
  (jsDD G).iso_existsUnique e

instance : (restrict (M := M) G).Full := (jsDD G).restrict_full
instance : (restrict (M := M) G).Faithful := (jsDD G).restrict_faithful

/-- **(b)**, with C2: every interpretation of `G` in `M` extends to a Markov functor
`F_m(G) → M` whose restriction is isomorphic to it. -/
theorem exists_realize (T : Strictification M Str) (I : Interp G M) :
    ∃ F : MarkovFun (FsM G) M, Nonempty ((restrict G).obj F ≅ I) :=
  (jsDD G).exists_realize T I

/-- **(d)**, with C2 (Fritz–Liang, Theorem 6.6): restriction to the generators is an equivalence
between Markov functors `F_m(G) → M` with monoidal natural transformations and interpretations. -/
theorem restrict_isEquivalence (T : Strictification M Str) : (restrict (M := M) G).IsEquivalence :=
  (jsDD G).restrict_isEquivalence T

/-- **(d)**, with C2: the equivalence. -/
noncomputable abbrev restrictEquiv (T : Strictification M Str) : MarkovFun (FsM G) M ≌ Interp G M :=
  (jsDD G).restrictEquiv T

end General

section Causal

variable {G : FinODAG}

/-- **(e)**, with C2: for a model `F : Cau(G) → M` of the causal category of an ordered DAG in an
arbitrary Markov category, the image of the
causal effect `[v_T ‖ v_S]` is the effect in `M` formed from the objects `F(v_i)` and the morphisms
`F(κ_i)` read through the structure isomorphisms, conjugated by the comparison isomorphisms of `F`
and of `eval`. -/
theorem prop_5_6_markov (T : Strictification M Str) (F : MarkovFun (js G).FsM M)
    (S T' : Finset (Fin G.n)) :
    F.map (causalEffectSets (js G) S T') =
      ((js G).cmpW F (finWord S)).inv ≫
        (T.psiW (fun j => F.obj ((js G).letterM j)) (finWord S)).hom ≫
        (G.K.markovData (js G) T F).effect (js G) S T' ≫
        (T.psiW (fun j => F.obj ((js G).letterM j)) (finWord T')).inv ≫
        ((js G).cmpW F (finWord T')).hom :=
  EffSig.prop_5_6_markov F S T'

end Causal

end Combinatorial

end FreeMarkov
