/-
Free Markov categories, Stage 8: interpretations of a free `DD`-graph monoid in a Markov category,
and the restriction of Markov functors out of `F_s(G)/S_M` to the generators (item (a)).

* `Interp G M`: an **interpretation** of the free `DD`-graph monoid `G` in the Markov category `M`:
  an object `ob a` of `M` for each letter `a` and, for each arrow `x : s(x) → t(x)` of `G`, a
  morphism `lp ob (s x) → lp ob (t x)` between the left-bracketed products (the objects
  `eval(s(x))`, `eval(t(x))` fixed by C2), such that the duplicate `δ_a` and the discard `ε_a` go to
  the duplicate and the discard of `M` on `ob a`.
* `Interp.Hom`: a **morphism of interpretations**: a family of morphisms `ob a → ob' a` commuting
  with the interpretations of all arrows (through their left-bracketed products); the category
  `Interp G M`.  This is the category `CatHyp(Σ, hyp(C))` of Fritz–Liang, Theorem 6.6, for
  signatures given by free `DD`-graph monoids.
* `JoyalStreet.cmpW`: the comparison isomorphism `lp (F ∘ letter) w ≅ F(w)` of a Markov functor `F`
  out of `F_s(G)/S_M`, built from its structure isomorphisms.
* `JoyalStreet.restrict`: the **restriction functor** from Markov functors `F_s(G)/S_M → M` (with
  monoidal natural transformations) to interpretations: `F ↦ (F(a), φ ∘ F(x) ∘ φ⁻¹)`,
  `θ ↦ (θ_a)_a`.
* `JoyalStreet.inductionM`: the generation principle in the quotient `F_s(G)/S_M`.

The cited result C1 enters only through the free Markov category `J.FsM` (`J : JoyalStreet _`).
-/
module

public import FreeMarkov.Stage8.Functors

@[expose] public section

universe w v u v'

namespace FreeMarkov

open CategoryTheory MonoidalCategory ComonObj Category Functor.LaxMonoidal Functor.OplaxMonoidal
  StrictSMC StrictMarkov

variable {S : Type w} (G : FreeDDGraphMonoid.{w, v} S)
  (M : Type u) [Category.{v'} M] [MonoidalCategory M] [MarkovCategory M]

/-- An **interpretation** of the free `DD`-graph monoid `G` in the Markov category `M`: an object
`ob a` for each letter `a`, and for each arrow `x : s(x) → t(x)` a morphism
`lp ob (s x) → lp ob (t x)` between the left-bracketed products, sending the duplicate and the
discard on `a` to the duplicate and the discard of `M` on `ob a`. -/
structure Interp where
  /-- The object of a letter. -/
  ob : S → M
  /-- The morphism of an arrow. -/
  ar (x : G.A) : lp ob (G.s x) ⟶ lp ob (G.t x)
  /-- `δ_a ↦ δ_{ob a}`. -/
  ar_dup (a : S) : Arrow.mk (ar (G.dup a)) = Arrow.mk Δ[ob a]
  /-- `ε_a ↦ ε_{ob a}`. -/
  ar_disc (a : S) : Arrow.mk (ar (G.disc a)) = Arrow.mk ε[ob a]

namespace Interp

variable {G M}

/-- A **morphism of interpretations** `I → I'`: morphisms `ob a → ob' a` commuting with the
interpretations of all arrows of `G` (through the left-bracketed products). -/
@[ext]
structure Hom (I I' : Interp G M) where
  /-- The component on a letter. -/
  app (a : S) : I.ob a ⟶ I'.ob a
  /-- Compatibility with every arrow `x : s(x) → t(x)` of `G`. -/
  comm (x : G.A) : I.ar x ≫ lpMap app (G.t x) = lpMap app (G.s x) ≫ I'.ar x

/-- The category of interpretations of `G` in `M`. -/
instance category : Category (Interp G M) where
  Hom := Hom
  id I := ⟨fun a => 𝟙 (I.ob a), fun x => by simp⟩
  comp f g := ⟨fun a => f.app a ≫ g.app a, fun x => by
    rw [lpMap_comp, lpMap_comp, ← assoc, f.comm, assoc, g.comm, assoc]⟩

@[ext]
theorem hom_ext {I I' : Interp G M} {f g : I ⟶ I'} (h : ∀ a, f.app a = g.app a) : f = g :=
  Hom.ext (funext h)

@[simp] theorem id_app (I : Interp G M) (a : S) : (𝟙 I : I ⟶ I).app a = 𝟙 _ := rfl

@[simp] theorem comp_app {I I' I'' : Interp G M} (f : I ⟶ I') (g : I' ⟶ I'') (a : S) :
    (f ≫ g).app a = f.app a ≫ g.app a := rfl

/-- An isomorphism of interpretations from isomorphisms on the letters. -/
@[simps]
def isoMk {I I' : Interp G M} (e : ∀ a, I.ob a ≅ I'.ob a)
    (h : ∀ x, I.ar x ≫ lpMap (fun a => (e a).hom) (G.t x) =
      lpMap (fun a => (e a).hom) (G.s x) ≫ I'.ar x) : I ≅ I' where
  hom := ⟨fun a => (e a).hom, h⟩
  inv := ⟨fun a => (e a).inv, fun x => by
    rw [← cancel_epi (lpMapIso e (G.s x)).hom, lpMapIso_hom, ← reassoc_of% (h x)]
    rw [← lpMap_comp, ← lpMap_comp_assoc]
    simp⟩

end Interp

/-! ### Restriction of Markov functors out of `F_s(G)/S_M` -/

namespace JoyalStreet

variable {G} (J : JoyalStreet G.toFreeGraphMonoid) {M}

/-- The one-letter word `a` as an object of `F_s(G)/S_M`. -/
abbrev letterM (a : S) : J.FsM := J.wordM (FreeMonoid.of a)

/-- The generator `x : s(x) → t(x)` of `F_s(G)/S_M` (the morphism `i_m(x)`). -/
noncomputable def genM (x : G.A) : J.wordM (G.s x) ⟶ J.wordM (G.t x) :=
  J.projM.map (J.hom (DHom.gen x))

theorem iM_A_genM (x : G.A) : J.iM.A x = Arrow.mk (J.genM x) := rfl

theorem arrow_genM_dup (a : S) : Arrow.mk (J.genM (G.dup a)) = Arrow.mk (δ_ (J.letterM a)) :=
  J.iM_matches.dup a

theorem arrow_genM_disc (a : S) : Arrow.mk (J.genM (G.disc a)) = Arrow.mk (ε_ (J.letterM a)) :=
  J.iM_matches.disc a

theorem wR_letterM (w : FreeMonoid S) :
    wR J.letterM (FreeMonoid.toList w).reverse = J.wordM w := wR_of_eq w

/-- The comparison isomorphism `lp (F ∘ letter) w ≅ F(w)` of a Markov functor `F` out of
`F_s(G)/S_M`, built from its structure isomorphisms `ε`, `μ`. -/
noncomputable def cmpW (F : MarkovFun J.FsM M) (w : FreeMonoid S) :
    lp (fun a => F.obj (J.letterM a)) w ≅ F.obj (J.wordM w) :=
  cmpR F.toFunctor J.letterM (FreeMonoid.toList w).reverse ≪≫
    F.toFunctor.mapIso (eqToIso (J.wR_letterM w))

theorem cmpW_hom (F : MarkovFun J.FsM M) (w : FreeMonoid S) :
    (J.cmpW F w).hom = (cmpR F.toFunctor J.letterM (FreeMonoid.toList w).reverse).hom ≫
      F.toFunctor.map (eqToHom (J.wR_letterM w)) := rfl

theorem cmpW_inv (F : MarkovFun J.FsM M) (w : FreeMonoid S) :
    (J.cmpW F w).inv = F.toFunctor.map (eqToHom (J.wR_letterM w).symm) ≫
      (cmpR F.toFunctor J.letterM (FreeMonoid.toList w).reverse).inv := rfl

theorem cmpW_of_hom (F : MarkovFun J.FsM M) (a : S) :
    (J.cmpW F (FreeMonoid.of a)).hom = 𝟙 _ := by
  change (cmpR F.toFunctor J.letterM [a]).hom ≫ F.toFunctor.map (𝟙 _) = _
  rw [F.toFunctor.map_id]; exact id_comp _

theorem cmpW_of_inv (F : MarkovFun J.FsM M) (a : S) :
    (J.cmpW F (FreeMonoid.of a)).inv = 𝟙 _ := by
  change F.toFunctor.map (𝟙 _) ≫ (cmpR F.toFunctor J.letterM [a]).inv = _
  rw [F.toFunctor.map_id]; exact id_comp _

theorem cmpW_one_hom (F : MarkovFun J.FsM M) :
    (J.cmpW F 1).hom = Functor.LaxMonoidal.ε F.toFunctor := by
  change (cmpR F.toFunctor J.letterM []).hom ≫ F.toFunctor.map (𝟙 _) = _
  rw [F.toFunctor.map_id]; exact comp_id _

theorem cmpW_one_inv (F : MarkovFun J.FsM M) :
    (J.cmpW F 1).inv = η F.toFunctor := by
  change F.toFunctor.map (𝟙 _) ≫ (cmpR F.toFunctor J.letterM []).inv = _
  rw [F.toFunctor.map_id]; exact id_comp _

theorem cmpW_of_mul_of_inv (F : MarkovFun J.FsM M) (a b : S) :
    (J.cmpW F (J.letterM a * J.letterM b)).inv = δ F.toFunctor (J.letterM a) (J.letterM b) := by
  change F.toFunctor.map (𝟙 _) ≫ (cmpR F.toFunctor J.letterM [b, a]).inv = _
  rw [F.toFunctor.map_id, cmpR_cons_inv, cmpR_single_inv]
  exact (id_comp _).trans ((congrArg _ (id_whiskerRight _ _)).trans (comp_id _))

/-- Conjugating a morphism of `F_s(G)/S_M` by the comparison isomorphisms depends only on it as
an arrow. -/
theorem arrow_conj (F : MarkovFun J.FsM M) {w₁ w₂ w₁' w₂' : FreeMonoid S}
    (g : J.wordM w₁ ⟶ J.wordM w₂) (g' : J.wordM w₁' ⟶ J.wordM w₂') (h : Arrow.mk g = Arrow.mk g') :
    Arrow.mk ((J.cmpW F w₁).hom ≫ F.map g ≫ (J.cmpW F w₂).inv) =
      Arrow.mk ((J.cmpW F w₁').hom ≫ F.map g' ≫ (J.cmpW F w₂').inv) := by
  have h₁ : w₁ = w₁' := (Arrow.left_eq_of_mk_eq h : J.wordM w₁ = J.wordM w₁')
  have h₂ : w₂ = w₂' := (Arrow.right_eq_of_mk_eq h : J.wordM w₂ = J.wordM w₂')
  subst h₁ h₂
  rw [Arrow.eq_of_mk_eq h]

/-- The restriction of a Markov functor `F : F_s(G)/S_M → M` to the generators: the objects
`F(a)` and the morphisms `φ_{t(x)}⁻¹ ∘ F(x) ∘ φ_{s(x)}`. -/
@[reducible] noncomputable def restrictObj (F : MarkovFun J.FsM M) : Interp G M where
  ob a := F.obj (J.letterM a)
  ar x := (J.cmpW F (G.s x)).hom ≫ F.map (J.genM x) ≫ (J.cmpW F (G.t x)).inv
  ar_dup a := by
    refine (J.arrow_conj F _ (δ_ (J.letterM a)) (J.arrow_genM_dup a)).trans ?_
    have h := F.map_copy (J.letterM a)
    simp only [Functor.Monoidal.μIso_inv] at h
    rw [J.cmpW_of_hom, J.cmpW_of_mul_of_inv]
    exact congrArg Arrow.mk ((id_comp _).trans h)
  ar_disc a := by
    refine (J.arrow_conj F _ (ε_ (J.letterM a)) (J.arrow_genM_disc a)).trans ?_
    have h := F.map_discard (J.letterM a)
    simp only [Functor.Monoidal.εIso_inv] at h
    rw [J.cmpW_of_hom]
    change Arrow.mk (_ ≫ F.map _ ≫ (J.cmpW F 1).inv) = _
    rw [J.cmpW_one_inv]
    exact congrArg Arrow.mk ((id_comp _).trans h)

@[simp] theorem restrictObj_ob (F : MarkovFun J.FsM M) (a : S) :
    (J.restrictObj F).ob a = F.obj (J.letterM a) := rfl

theorem restrictObj_ar (F : MarkovFun J.FsM M) (x : G.A) :
    (J.restrictObj F).ar x = (J.cmpW F (G.s x)).hom ≫ F.map (J.genM x) ≫ (J.cmpW F (G.t x)).inv :=
  rfl

/-- A monoidal natural transformation commutes with the comparison isomorphisms. -/
@[reassoc]
theorem cmpW_naturality {F F' : MarkovFun J.FsM M} (θ : F ⟶ F') (w : FreeMonoid S) :
    (J.cmpW F w).hom ≫ θ.nat.app (J.wordM w) =
      lpMap (fun a => θ.nat.app (J.letterM a)) w ≫ (J.cmpW F' w).hom := by
  rw [cmpW_hom, cmpW_hom, assoc, θ.nat.naturality, ← assoc, cmpR_naturality, assoc]

theorem cmpW_inv_naturality {F F' : MarkovFun J.FsM M} (θ : F ⟶ F') (w : FreeMonoid S) :
    (J.cmpW F w).inv ≫ lpMap (fun a => θ.nat.app (J.letterM a)) w =
      θ.nat.app (J.wordM w) ≫ (J.cmpW F' w).inv := by
  rw [Iso.inv_comp_eq, ← assoc, J.cmpW_naturality θ w, assoc, Iso.hom_inv_id, comp_id]

/-- **Restriction** of a monoidal natural transformation to the letters. -/
noncomputable def restrictMap {F F' : MarkovFun J.FsM M} (θ : F ⟶ F') :
    J.restrictObj F ⟶ J.restrictObj F' where
  app a := θ.nat.app (J.letterM a)
  comm x := by
    change ((J.cmpW F (G.s x)).hom ≫ F.map (J.genM x) ≫ (J.cmpW F (G.t x)).inv) ≫
        lpMap (fun a => θ.nat.app (J.letterM a)) (G.t x) =
      lpMap (fun a => θ.nat.app (J.letterM a)) (G.s x) ≫
        ((J.cmpW F' (G.s x)).hom ≫ F'.map (J.genM x) ≫ (J.cmpW F' (G.t x)).inv)
    rw [assoc, assoc, J.cmpW_inv_naturality θ, θ.nat.naturality_assoc, J.cmpW_naturality_assoc]

end JoyalStreet

end FreeMarkov
