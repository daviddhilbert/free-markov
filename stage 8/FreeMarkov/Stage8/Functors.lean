/-
Free Markov categories, Stage 8: Markov functors between Markov categories in arbitrary universes,
and monoidal natural transformations between them.

* `MarkovFun C D`: a **Markov functor** in the sense of the Introduction ("a strong symmetric
  monoidal functor that preserves the distinguished comonoids by way of matching duplicates and
  discards"), with the fields of Stage 6's `MarkovFunctor`, for unbundled Markov categories `C`, `D`
  in arbitrary (possibly different) universes.  Stage 6's `MarkovFunctor` is the case of bundled
  categories in the same universes (`MarkovFunctor.equivMarkovFun`).
* `MarkovFun.Hom`: **monoidal natural transformations** (Mathlib's `NatTrans.IsMonoidal`: compatible
  with the structure morphisms `ε` and `μ`); the category `MarkovFun C D`, the category
  `gsCat(C, D)` of Fritz–Liang, Definition 6.2 / Theorem 6.6, in the strong case.
* `StrictMarkovFunctor.toMarkovFun`: a strict Markov functor is a Markov functor whose structure
  isomorphisms are identities (Stage 6's `StrictMarkovFunctor.toMarkovFunctor` for arbitrary
  universes).
* `MarkovFun.comp`: composition.

No cited result is used in this file.
-/
module

public import FreeMarkov.Stage8.Products
public import FreeMarkov.Stage6.MarCat

@[expose] public section

universe w u₁ v₁ u₂ v₂ u₃ v₃

namespace FreeMarkov

open CategoryTheory MonoidalCategory ComonObj Category Functor.LaxMonoidal Functor.OplaxMonoidal

/-- *Introduction.* A **Markov functor** `C → D` between Markov categories (in Mathlib's sense, in
arbitrary universes): a strong symmetric monoidal functor (`Functor.Braided`) with
`μ⁻¹ ∘ F(δ_X) = δ_{F X}` and `ε⁻¹ ∘ F(ε_X) = ε_{F X}`.  The fields are those of Stage 6's
`MarkovFunctor`. -/
structure MarkovFun (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [MarkovCategory C]
    (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D] [MarkovCategory D] where
  /-- The underlying functor. -/
  toFunctor : C ⥤ D
  /-- The strong symmetric monoidal structure. -/
  braided : toFunctor.Braided
  map_copy (X : C) :
    toFunctor.map Δ[X] ≫ (Functor.Monoidal.μIso toFunctor X X).inv = Δ[toFunctor.obj X]
  map_discard (X : C) :
    toFunctor.map ε[X] ≫ (Functor.Monoidal.εIso toFunctor).inv = ε[toFunctor.obj X]

attribute [instance] MarkovFun.braided

namespace MarkovFun

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MarkovCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [MarkovCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [MarkovCategory E]

/-- The value on objects. -/
abbrev obj (F : MarkovFun C D) (X : C) : D := F.toFunctor.obj X

/-- The value on morphisms. -/
abbrev map (F : MarkovFun C D) {X Y : C} (f : X ⟶ Y) : F.obj X ⟶ F.obj Y := F.toFunctor.map f

/-- A **monoidal natural transformation** between Markov functors (Mathlib's
`NatTrans.IsMonoidal`): a natural transformation `θ : F → G` with `θ_1 ∘ ε_F = ε_G` and
`θ_{X ⊗ Y} ∘ μ_F = μ_G ∘ (θ_X ⊗ θ_Y)`. -/
@[ext]
structure Hom (F G : MarkovFun C D) where
  /-- The underlying natural transformation. -/
  nat : F.toFunctor ⟶ G.toFunctor
  /-- It is monoidal. -/
  isMonoidal : NatTrans.IsMonoidal nat

attribute [instance] Hom.isMonoidal

/-- The category of Markov functors `C → D` and monoidal natural transformations. -/
instance category : Category (MarkovFun C D) where
  Hom := Hom
  id F := ⟨𝟙 F.toFunctor, inferInstance⟩
  comp α β := ⟨α.nat ≫ β.nat, inferInstance⟩

@[ext]
theorem hom_ext {F G : MarkovFun C D} {α β : F ⟶ G} (h : α.nat = β.nat) : α = β := Hom.ext h

@[simp] theorem id_nat (F : MarkovFun C D) : (𝟙 F : F ⟶ F).nat = 𝟙 F.toFunctor := rfl

@[simp] theorem comp_nat {F G H : MarkovFun C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).nat = α.nat ≫ β.nat := rfl

/-- The components of the inverse of an isomorphism of Markov functors. -/
@[simp] theorem inv_hom_app {F G : MarkovFun C D} (e : F ≅ G) (X : C) :
    e.inv.nat.app X ≫ e.hom.nat.app X = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← comp_nat, e.inv_hom_id]; rfl

@[simp] theorem hom_inv_app {F G : MarkovFun C D} (e : F ≅ G) (X : C) :
    e.hom.nat.app X ≫ e.inv.nat.app X = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← comp_nat, e.hom_inv_id]; rfl

/-- Composition of Markov functors. -/
def comp (G : MarkovFun D E) (F : MarkovFun C D) : MarkovFun C E where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  braided := inferInstance
  map_copy X := by
    have hF := F.map_copy X
    have hG := G.map_copy (F.toFunctor.obj X)
    simp only [Functor.Monoidal.μIso_inv] at hF hG ⊢
    change G.toFunctor.map (F.toFunctor.map Δ[X]) ≫
      (G.toFunctor.map (δ F.toFunctor X X) ≫ δ G.toFunctor _ _) = _
    rw [← Category.assoc, ← Functor.map_comp, hF, hG]
  map_discard X := by
    have hF := F.map_discard X
    have hG := G.map_discard (F.toFunctor.obj X)
    simp only [Functor.Monoidal.εIso_inv] at hF hG ⊢
    change G.toFunctor.map (F.toFunctor.map ε[X]) ≫
      (G.toFunctor.map (η F.toFunctor) ≫ η G.toFunctor) = _
    rw [← Category.assoc, ← Functor.map_comp, hF, hG]

theorem comp_ε (G : MarkovFun D E) (F : MarkovFun C D) :
    Functor.LaxMonoidal.ε (G.comp F).toFunctor =
      Functor.LaxMonoidal.ε G.toFunctor ≫ G.toFunctor.map (Functor.LaxMonoidal.ε F.toFunctor) := rfl

theorem comp_μ (G : MarkovFun D E) (F : MarkovFun C D) (X Y : C) :
    μ (G.comp F).toFunctor X Y =
      μ G.toFunctor (F.obj X) (F.obj Y) ≫ G.toFunctor.map (μ F.toFunctor X Y) := rfl

theorem comp_η (G : MarkovFun D E) (F : MarkovFun C D) :
    η (G.comp F).toFunctor = G.toFunctor.map (η F.toFunctor) ≫ η G.toFunctor := rfl

theorem comp_δ (G : MarkovFun D E) (F : MarkovFun C D) (X Y : C) :
    δ (G.comp F).toFunctor X Y =
      G.toFunctor.map (δ F.toFunctor X Y) ≫ δ G.toFunctor (F.obj X) (F.obj Y) := rfl

end MarkovFun

/-! ### Comparison with Stage 6's `MarkovFunctor` -/

namespace MarkovFunctor

variable {C D : MarCat.{v₁, u₁}}

/-- Stage 6's Markov functors between bundled Markov categories in the same universes are exactly
the `MarkovFun`s. -/
def equivMarkovFun : MarkovFunctor C D ≃ MarkovFun C D where
  toFun F := ⟨F.toFunctor, F.braided, F.map_copy, F.map_discard⟩
  invFun F := ⟨F.toFunctor, F.braided, F.map_copy, F.map_discard⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MarkovFunctor

/-! ### Strict Markov functors -/

namespace StrictMarkovFunctor

open StrictSMC StrictMarkov

variable {C : Type u₁} [Monoid C] [Category.{v₁} C] [StrictMarkov C]
  {D : Type u₂} [Monoid D] [Category.{v₂} D] [StrictMarkov D]

/-- The strong monoidal structure of a strict functor (arbitrary universes): the structure
isomorphisms are identities (`eqToIso`), through the Stage 0 bridge. -/
def coreMonoidal' (F : StrictFunctor C D) : F.toFunctor.CoreMonoidal where
  εIso := eqToIso F.obj_one.symm
  μIso X Y := eqToIso (F.obj_mul X Y).symm
  μIso_hom_natural_left f X' := by
    simp only [eqToIso.hom, whiskerRight_eq]
    refine Arrow.comp_eqToHom_eq_of_mk_eq ?_ _ _
    rw [F.map_tensorHom, CategoryTheory.Functor.map_id]
  μIso_hom_natural_right X' f := by
    simp only [eqToIso.hom, whiskerLeft_eq]
    refine Arrow.comp_eqToHom_eq_of_mk_eq ?_ _ _
    rw [F.map_tensorHom, CategoryTheory.Functor.map_id]
  associativity X Y Z := by
    simp only [eqToIso.hom, whiskerRight_eq, whiskerLeft_eq, associator_eq, eqToHom_map,
      eqToHom_tensorHom_id, id_tensorHom_eqToHom, eqToHom_trans]
  left_unitality X := by
    simp only [eqToIso.hom, whiskerRight_eq, leftUnitor_eq, eqToHom_map, eqToHom_tensorHom_id,
      eqToHom_trans]
  right_unitality X := by
    simp only [eqToIso.hom, whiskerLeft_eq, rightUnitor_eq, eqToHom_map, id_tensorHom_eqToHom,
      eqToHom_trans]

/-- The strong symmetric monoidal structure of a strict functor (arbitrary universes). -/
@[instance_reducible]
def braided' (F : StrictFunctor C D) : F.toFunctor.Braided :=
  letI : F.toFunctor.Monoidal := (coreMonoidal' F).toMonoidal
  { braided := fun X Y => by
      show eqToHom (F.obj_mul X Y).symm ≫ F.map (σ_ X Y) =
        σ_ (F.obj X) (F.obj Y) ≫ eqToHom (F.obj_mul Y X).symm
      exact (Arrow.comp_eqToHom_eq_of_mk_eq (F.map_braid X Y).symm (F.obj_mul X Y).symm
        (F.obj_mul Y X).symm).symm }

/-- A strict Markov functor is a Markov functor whose structure isomorphisms are identities. -/
def toMarkovFun (F : StrictMarkovFunctor C D) : MarkovFun C D where
  toFunctor := F.toFunctor
  braided := braided' F.toStrictFunctor
  map_copy X := by
    show F.map (δ_ X) ≫ eqToHom (F.obj_mul X X) = δ_ (F.obj X)
    exact Arrow.eq_of_mk_eq ((Arrow.arrow_mk_comp_eqToHom _ _).trans (F.map_copy X))
  map_discard X := by
    show F.map (ε_ X) ≫ eqToHom F.obj_one = ε_ (F.obj X)
    exact eq_discard _

theorem toMarkovFun_ε (F : StrictMarkovFunctor C D) :
    Functor.LaxMonoidal.ε F.toMarkovFun.toFunctor = eqToHom F.obj_one.symm := rfl

theorem toMarkovFun_μ (F : StrictMarkovFunctor C D) (X Y : C) :
    μ F.toMarkovFun.toFunctor X Y = eqToHom (F.obj_mul X Y).symm := rfl

theorem toMarkovFun_η (F : StrictMarkovFunctor C D) :
    η F.toMarkovFun.toFunctor = eqToHom F.obj_one := rfl

theorem toMarkovFun_δ (F : StrictMarkovFunctor C D) (X Y : C) :
    δ F.toMarkovFun.toFunctor X Y = eqToHom (F.obj_mul X Y) := rfl

end StrictMarkovFunctor

end FreeMarkov
