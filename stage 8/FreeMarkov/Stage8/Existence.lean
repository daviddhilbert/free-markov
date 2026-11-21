/-
Free Markov categories, Stage 8: existence (item (b)), with the strictification C2 as hypothesis.

For a free `DD`-graph monoid `G`, the free Markov category `F_s(G)/S_M` (`J.FsM`), a Markov
category `M` and `T : Strictification M Str` (C2):

* `Strictification.evalFun`: `eval : str(M) → M` as a Markov functor (C2, clause 3).
* `Strictification.psiW`: the comparison isomorphism `lp ob w ≅ eval(ob a_1 … ob a_n)` of `eval`.
* `Interp.toStrHom`: the graph monoid homomorphism `G → str(M)` of an interpretation: the word
  `ob(a_1) … ob(a_n)` for `a_1 … a_n`, and for an arrow `x` the unique morphism of `str(M)` that
  `eval` sends to `ψ_{t(x)} ∘ I(x) ∘ ψ_{s(x)}⁻¹` (fullness and faithfulness of `eval`); it matches
  duplicates and discards (`Interp.toStrHom_matches`).
* `JoyalStreet.realize T I`: **(b)** the Markov functor `eval ∘ F_I : F_s(G)/S_M → M`, with
  `F_I : F_s(G)/S_M → str(M)` the strict Markov functor of Theorem 4.1;
  `JoyalStreet.restrict_realize`: its restriction to the generators is isomorphic to `I`, by the
  isomorphism whose components are the identities `eval(ob a) = ob a` (`eqToHom`).

The cited results used: C1 (`J`) and C2 (`T`).
-/
module

public import FreeMarkov.Stage8.Uniqueness

@[expose] public section

universe w v u v'

namespace FreeMarkov

open CategoryTheory MonoidalCategory ComonObj Category Functor.LaxMonoidal Functor.OplaxMonoidal
  StrictSMC StrictMarkov

/-! ### Arrow calculus for the comparisons -/

section ArrowCalc

variable {C : Type*} [Category C]

theorem arrow_whiskerRight_congr [MonoidalCategory C] {X Y X' Y' Z Z' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (h : Arrow.mk f = Arrow.mk f') (hZ : Z = Z') : Arrow.mk (f ▷ Z) = Arrow.mk (f' ▷ Z') := by
  obtain ⟨rfl, rfl, rfl⟩ := (Arrow.mk_eq_mk_iff _ _).1 h
  subst hZ
  simp

theorem arrow_inv_congr {X Y X' Y' : C} {e : X ≅ Y} {e' : X' ≅ Y'}
    (h : Arrow.mk e.hom = Arrow.mk e'.hom) : Arrow.mk e.inv = Arrow.mk e'.inv := by
  obtain ⟨rfl, rfl, h'⟩ := (Arrow.mk_eq_mk_iff _ _).1 h
  simp only [eqToHom_refl, id_comp, comp_id] at h'
  rw [Iso.ext h']

theorem arrow_comp_congr3 {X Y Z W X' Y' Z' W' : C} {f : X ⟶ Y} {g : Y ⟶ Z} {k : Z ⟶ W}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'} {k' : Z' ⟶ W'} (hf : Arrow.mk f = Arrow.mk f')
    (hg : Arrow.mk g = Arrow.mk g') (hk : Arrow.mk k = Arrow.mk k') :
    Arrow.mk (f ≫ g ≫ k) = Arrow.mk (f' ≫ g' ≫ k') :=
  Arrow.mk_comp_congr hf (Arrow.mk_comp_congr hg hk)

theorem arrow_comp_map_eqToHom {D : Type*} [Category D] (E : C ⥤ D) {X : D} {A B : C}
    (f : X ⟶ E.obj A) (h : A = B) : Arrow.mk (f ≫ E.map (eqToHom h)) = Arrow.mk f := by
  subst h; simp

theorem arrow_faithful {D : Type*} [Category D] (E : C ⥤ D) [E.Faithful] {A B B' : C}
    (p : A ⟶ B) (q : A ⟶ B') (hB : B = B') (h : Arrow.mk (E.map p) = Arrow.mk (E.map q)) :
    Arrow.mk p = Arrow.mk q := by
  subst hB
  rw [E.map_injective (Arrow.eq_of_mk_eq h)]

end ArrowCalc

/-! ### Comparison isomorphisms of a composite with a strict functor -/

section CompStrict

variable {S : Type w} {C : Type*} [Monoid C] [Category C] [StrictMarkov C]
  {C' : Type*} [Monoid C'] [Category C'] [StrictMarkov C']
  {M : Type u} [Category.{v'} M] [MonoidalCategory M] [MarkovCategory M]

theorem StrictMarkovFunctor.obj_wR (L : StrictMarkovFunctor C C') (o : S → C) (o' : S → C')
    (ho : ∀ a, L.obj (o a) = o' a) : ∀ r : List S, L.obj (wR o r) = wR o' r
  | [] => L.obj_one
  | [a] => ho a
  | a :: b :: r => by
    rw [wR, L.obj_mul, StrictMarkovFunctor.obj_wR L o o' ho (b :: r), ho a]; rfl

/-- The comparison isomorphisms of `E ∘ L`, for `L` strict, are those of `E` (as arrows). -/
theorem cmpR_comp_strict (E : MarkovFun C' M) (L : StrictMarkovFunctor C C') (o : S → C)
    (o' : S → C') (ho : ∀ a, L.obj (o a) = o' a) : ∀ r : List S,
    Arrow.mk (cmpR (E.comp L.toMarkovFun).toFunctor o r).hom = Arrow.mk (cmpR E.toFunctor o' r).hom
  | [] => by
    rw [cmpR_nil_hom, cmpR_nil_hom, MarkovFun.comp_ε, StrictMarkovFunctor.toMarkovFun_ε]
    exact arrow_comp_map_eqToHom E.toFunctor _ _
  | [a] => Arrow.mk_id_congr (congrArg E.obj (ho a))
  | a :: b :: r => by
    rw [cmpR_cons_hom, cmpR_cons_hom, MarkovFun.comp_μ, StrictMarkovFunctor.toMarkovFun_μ]
    refine Arrow.mk_comp_congr (arrow_whiskerRight_congr
      (cmpR_comp_strict E L o o' ho (b :: r)) (congrArg E.obj (ho a))) ?_
    refine (arrow_comp_map_eqToHom E.toFunctor _ _).trans ?_
    have h₁ := L.obj_wR o o' ho (b :: r)
    have h₂ := ho a
    change Arrow.mk (μ E.toFunctor (L.obj (wR o (b :: r))) (L.obj (o a))) = _
    generalize L.obj (wR o (b :: r)) = X at h₁ ⊢
    generalize L.obj (o a) = Y at h₂ ⊢
    subst h₁ h₂
    rfl

end CompStrict

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S}
  {M : Type u} [Category.{v'} M] [MonoidalCategory M] [MarkovCategory M]
  {Str : Type u} [Monoid Str] [Category.{v'} Str] [StrictMarkov Str]

namespace Strictification

variable (T : Strictification M Str)

/-- `eval : str(M) → M` as a Markov functor (C2, clause 3). -/
def evalFun : MarkovFun Str M where
  toFunctor := T.eval
  braided := T.braided
  map_copy := T.map_copy
  map_discard := T.map_discard

instance : T.evalFun.toFunctor.Full := T.full
instance : T.evalFun.toFunctor.Faithful := T.faithful

variable (ob : S → M)

/-- The letters `ob a` of `str(M)`. -/
abbrev oS (a : S) : Str := T.letter (ob a)

theorem ob_eq : ob = fun a => T.evalFun.obj (T.oS ob a) :=
  funext fun a => (T.eval_letter (ob a)).symm

/-- The monoid homomorphism `W(S) → str(M)`, `a ↦ ob a`. -/
noncomputable def hV : FreeMonoid S →* Str := FreeMonoid.lift (T.oS ob)

theorem wR_eq_hV (w : FreeMonoid S) : wR (T.oS ob) (FreeMonoid.toList w).reverse = T.hV ob w := by
  rw [wR_eq_lift, List.reverse_reverse, FreeMonoid.ofList_toList]; rfl

/-- The comparison isomorphism `lp ob w ≅ eval(ob a_1 … ob a_n)` of `eval`. -/
noncomputable def psiW (w : FreeMonoid S) : lp ob w ≅ T.evalFun.obj (T.hV ob w) :=
  eqToIso (congrArg (fun o => lp o w) (T.ob_eq ob)) ≪≫
    cmpR T.evalFun.toFunctor (T.oS ob) (FreeMonoid.toList w).reverse ≪≫
      T.evalFun.toFunctor.mapIso (eqToIso (T.wR_eq_hV ob w))

theorem arrow_psiW_hom (w : FreeMonoid S) :
    Arrow.mk (T.psiW ob w).hom =
      Arrow.mk (cmpR T.evalFun.toFunctor (T.oS ob) (FreeMonoid.toList w).reverse).hom := by
  simp only [psiW, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom]
  rw [Arrow.arrow_mk_eqToHom_comp]
  exact arrow_comp_map_eqToHom _ _ _

end Strictification

namespace Interp

variable (T : Strictification M Str) (I : Interp G M)

/-- The morphism of `str(M)` interpreting an arrow `x`: the preimage under `eval` of
`ψ_{t(x)} ∘ I(x) ∘ ψ_{s(x)}⁻¹`. -/
noncomputable def strA (x : G.A) : T.hV I.ob (G.s x) ⟶ T.hV I.ob (G.t x) :=
  T.evalFun.toFunctor.preimage ((T.psiW I.ob (G.s x)).inv ≫ I.ar x ≫ (T.psiW I.ob (G.t x)).hom)

theorem eval_strA (x : G.A) :
    T.evalFun.map (I.strA T x) = (T.psiW I.ob (G.s x)).inv ≫ I.ar x ≫ (T.psiW I.ob (G.t x)).hom :=
  T.evalFun.toFunctor.map_preimage _

/-- The graph monoid homomorphism `G → str(M)` of an interpretation. -/
noncomputable def toStrHom : G.toGraphMonoid.Hom (graphMonoid Str) where
  V := T.hV I.ob
  A x := Arrow.mk (I.strA T x)
  s_A _ := rfl
  t_A _ := rfl

theorem arrow_strA_congr {w₁ w₂ w₁' w₂' : FreeMonoid S} (f : lp I.ob w₁ ⟶ lp I.ob w₂)
    (f' : lp I.ob w₁' ⟶ lp I.ob w₂') (h₁ : w₁ = w₁') (h₂ : w₂ = w₂')
    (h : Arrow.mk f = Arrow.mk f') :
    Arrow.mk (T.evalFun.toFunctor.preimage ((T.psiW I.ob w₁).inv ≫ f ≫ (T.psiW I.ob w₂).hom)) =
      Arrow.mk (T.evalFun.toFunctor.preimage ((T.psiW I.ob w₁').inv ≫ f' ≫
        (T.psiW I.ob w₂').hom)) := by
  subst h₁ h₂
  rw [Arrow.eq_of_mk_eq h]

omit [MarkovCategory M] in
theorem arrow_comul_congr {X Y : M} [MarkovCategory M] (h : X = Y) : Arrow.mk Δ[X] = Arrow.mk Δ[Y] := by
  subst h; rfl

theorem arrow_counit_congr {X Y : M} (h : X = Y) : Arrow.mk ε[X] = Arrow.mk ε[Y] := by
  subst h; rfl

theorem arrow_psiW_inv (w : FreeMonoid S) :
    Arrow.mk (T.psiW I.ob w).inv =
      Arrow.mk (cmpR T.evalFun.toFunctor (T.oS I.ob) (FreeMonoid.toList w).reverse).inv :=
  arrow_inv_congr (T.arrow_psiW_hom I.ob w)

/-- The homomorphism `G → str(M)` of an interpretation matches duplicates and discards. -/
theorem toStrHom_matches : G.MatchesDupDisc (I.toStrHom T) where
  dup a := by
    change Arrow.mk (I.strA T (G.dup a)) = _
    refine (I.arrow_strA_congr T (w₁' := FreeMonoid.of a)
      (w₂' := FreeMonoid.of a * FreeMonoid.of a) (I.ar (G.dup a)) Δ[I.ob a]
      (G.s_dup a) (G.t_dup a) (I.ar_dup a)).trans ?_
    refine arrow_faithful T.evalFun.toFunctor _ _ (map_mul _ _ _) ?_
    rw [Functor.map_preimage]
    have hc := T.evalFun.map_copy (T.hV I.ob (FreeMonoid.of a))
    simp only [Functor.Monoidal.μIso_inv] at hc
    have hc' : T.evalFun.toFunctor.map (δ_ (T.hV I.ob (FreeMonoid.of a))) =
        Δ[T.evalFun.obj (T.hV I.ob (FreeMonoid.of a))] ≫
          μ T.evalFun.toFunctor (T.hV I.ob (FreeMonoid.of a)) (T.hV I.ob (FreeMonoid.of a)) := by
      rw [← hc, assoc, Functor.Monoidal.δ_μ, comp_id]
      rfl
    refine Eq.trans ?_ (congrArg Arrow.mk hc').symm
    have h₁ := I.arrow_psiW_inv T (FreeMonoid.of a)
    have h₂ := T.arrow_psiW_hom I.ob (FreeMonoid.of a * FreeMonoid.of a)
    rw [show (FreeMonoid.toList (FreeMonoid.of a)).reverse = [a] from rfl] at h₁
    rw [show (FreeMonoid.toList (FreeMonoid.of a * FreeMonoid.of a)).reverse = [a, a] from rfl,
      cmpR_pair_hom] at h₂
    rw [cmpR_single_inv] at h₁
    refine (arrow_comp_congr3 h₁ (arrow_comul_congr (T.eval_letter (I.ob a)).symm) h₂).trans ?_
    have hv : T.hV I.ob (FreeMonoid.of a) = T.oS I.ob a := FreeMonoid.lift_eval_of _ _
    rw [hv]
    exact congrArg Arrow.mk (id_comp _)
  disc a := by
    change Arrow.mk (I.strA T (G.disc a)) = _
    refine (I.arrow_strA_congr T (w₁' := FreeMonoid.of a) (w₂' := 1) (I.ar (G.disc a)) ε[I.ob a]
      (G.s_disc a) (G.t_disc a) (I.ar_disc a)).trans ?_
    refine arrow_faithful T.evalFun.toFunctor _ _ (map_one _) ?_
    rw [Functor.map_preimage]
    have hc := T.evalFun.map_discard (T.hV I.ob (FreeMonoid.of a))
    simp only [Functor.Monoidal.εIso_inv] at hc
    have hc' : T.evalFun.toFunctor.map (ε_ (T.hV I.ob (FreeMonoid.of a))) =
        ε[T.evalFun.obj (T.hV I.ob (FreeMonoid.of a))] ≫ Functor.LaxMonoidal.ε T.evalFun.toFunctor := by
      rw [← hc, assoc, Functor.Monoidal.η_ε, comp_id]
      rfl
    refine Eq.trans ?_ (congrArg Arrow.mk hc').symm
    have h₁ := I.arrow_psiW_inv T (FreeMonoid.of a)
    have h₂ := T.arrow_psiW_hom I.ob 1
    rw [show (FreeMonoid.toList (FreeMonoid.of a)).reverse = [a] from rfl, cmpR_single_inv] at h₁
    rw [show (FreeMonoid.toList (1 : FreeMonoid S)).reverse = [] from rfl, cmpR_nil_hom] at h₂
    refine (arrow_comp_congr3 h₁ (arrow_counit_congr (T.eval_letter (I.ob a)).symm) h₂).trans ?_
    have hv : T.hV I.ob (FreeMonoid.of a) = T.oS I.ob a := FreeMonoid.lift_eval_of _ _
    rw [hv]
    exact congrArg Arrow.mk (id_comp _)

end Interp

namespace JoyalStreet

variable (J : JoyalStreet G.toFreeGraphMonoid) (T : Strictification M Str) (I : Interp G M)

/-- The strict Markov functor `F_I : F_s(G)/S_M → str(M)` given by Theorem 4.1 for the homomorphism
`G → str(M)` of `I`. -/
noncomputable abbrev liftStr : StrictMarkovFunctor J.FsM Str :=
  J.lift (I.toStrHom T) (I.toStrHom_matches T)

/-- **(b)** The Markov functor `eval ∘ F_I : F_s(G)/S_M → M` realizing the interpretation `I`. -/
noncomputable abbrev realize : MarkovFun J.FsM M :=
  T.evalFun.comp (J.liftStr T I).toMarkovFun

theorem liftStr_letter (a : S) : (J.liftStr T I).obj (J.letterM a) = T.oS I.ob a :=
  lift_obj (I.toStrHom T) (I.toStrHom_matches T) (FreeMonoid.of a)

theorem realize_letter (a : S) : (J.realize T I).obj (J.letterM a) = I.ob a :=
  (congrArg T.evalFun.obj (J.liftStr_letter T I a)).trans (T.eval_letter (I.ob a))

theorem arrow_cmpW_realize (w : FreeMonoid S) :
    Arrow.mk (J.cmpW (J.realize T I) w).hom = Arrow.mk (T.psiW I.ob w).hom := by
  rw [cmpW_hom]
  refine (arrow_comp_map_eqToHom _ _ _).trans ?_
  exact (cmpR_comp_strict T.evalFun (J.liftStr T I) J.letterM (T.oS I.ob) (J.liftStr_letter T I)
    _).trans (T.arrow_psiW_hom I.ob w).symm

/-- **(b)** The restriction of `eval ∘ F_I` agrees with `I` on the letters (`realize_letter`) and,
as arrows of `M`, on every arrow of `G`. -/
theorem realize_ar (x : G.A) :
    Arrow.mk ((J.restrictObj (J.realize T I)).ar x) = Arrow.mk (I.ar x) := by
  rw [restrictObj_ar]
  have hg : Arrow.mk ((J.realize T I).map (J.genM x)) =
      Arrow.mk ((T.psiW I.ob (G.s x)).inv ≫ I.ar x ≫ (T.psiW I.ob (G.t x)).hom) := by
    rw [← Interp.eval_strA]
    exact T.evalFun.toFunctor.mk_map_congr (lift_gen (I.toStrHom T) (I.toStrHom_matches T) x)
  refine (arrow_comp_congr3 (J.arrow_cmpW_realize T I (G.s x)) hg
    (arrow_inv_congr (J.arrow_cmpW_realize T I (G.t x)))).trans ?_
  simp

/-- **(b)** The restriction of `eval ∘ F_I` to the generators is isomorphic to `I`: the components
are the identities `eval(ob a) = ob a`, and the morphisms of the arrows agree as arrows of `M`. -/
noncomputable def restrict_realize : J.restrict.obj (J.realize T I) ≅ I :=
  Interp.isoMk (fun a => eqToIso (J.realize_letter T I a)) (fun x => by
    have hr : (fun a => (J.realize T I).obj (J.letterM a)) = I.ob := funext (J.realize_letter T I)
    change (J.restrictObj (J.realize T I)).ar x ≫ lpMap (fun a => eqToHom (congrFun hr a)) _ =
      lpMap (fun a => eqToHom (congrFun hr a)) _ ≫ I.ar x
    rw [lpMap_eqToHom hr, lpMap_eqToHom hr]
    exact Arrow.comp_eqToHom_eq_of_mk_eq (J.realize_ar T I x) _ _)

theorem restrict_realize_hom_app (a : S) :
    (J.restrict_realize T I).hom.app a = eqToHom (J.realize_letter T I a) := rfl

include T in
/-- **(b)** Every interpretation of `G` in `M` extends to a Markov functor `F_s(G)/S_M → M`. -/
theorem exists_realize : ∃ F : MarkovFun J.FsM M, Nonempty (J.restrict.obj F ≅ I) :=
  ⟨J.realize T I, ⟨J.restrict_realize T I⟩⟩

end JoyalStreet



end FreeMarkov
