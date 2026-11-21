/-
Free Markov categories, Stage 6: the target categories of Theorem 6.7 (PLAN.md, D7).

* `StrictMarkovCat`: strict Markov categories (Stage 0's `StrictMarkov`) and strict Markov functors.
* `MarCat`: Markov categories in the sense of Mathlib (`MarkovCategory`: symmetric monoidal, every
  object a commutative comonoid compatible with `⊗`, discards natural) and **Markov functors** in
  the sense of the Introduction: "a strong symmetric monoidal functor `F : C → D` between two Markov
  categories that preserves the distinguished comonoids by way of matching duplicates and discards"
  (`MarkovFunctor`: a Mathlib `Functor.Braided` structure, i.e. a strong monoidal functor whose
  structure isomorphisms commute with the symmetries, with `μ⁻¹ ∘ F(δ_X) = δ_{F X}` and
  `ε⁻¹ ∘ F(ε_X) = ε_{F X}`, the form used for `eval` in Stage 5's `Strictification`).
* `StrictMarkovCat.toMarCat`: the inclusion, sending a strict Markov category to its Mathlib Markov
  category (Stage 0 bridge, associators and unitors `eqToIso`) and a strict Markov functor to the
  Markov functor whose structure isomorphisms are identities (`eqToIso`).

No cited result is used in this file.
-/
module

public import FreeMarkov.Stage6.Prop66

@[expose] public section

universe v u v₁ u₁

namespace FreeMarkov

open CategoryTheory MonoidalCategory StrictSMC StrictMarkov ComonObj Functor.LaxMonoidal
  Functor.OplaxMonoidal

/-! ### Strict Markov categories -/

/-- *Introduction / D7.* A strict Markov category, bundled. -/
structure StrictMarkovCat : Type (max (u + 1) (v + 1)) where
  /-- The objects. -/
  carrier : Type u
  [monoid : Monoid carrier]
  [cat : Category.{v} carrier]
  [str : StrictMarkov carrier]

attribute [instance] StrictMarkovCat.monoid StrictMarkovCat.cat StrictMarkovCat.str

namespace StrictMarkovCat

instance : CoeSort StrictMarkovCat.{v, u} (Type u) := ⟨StrictMarkovCat.carrier⟩

/-- The bundled strict Markov category of `C`. -/
abbrev of (C : Type u) [Monoid C] [Category.{v} C] [StrictMarkov C] : StrictMarkovCat.{v, u} := ⟨C⟩

/-- *D7.* The category **`StrictMarkovCat`** of strict Markov categories and strict Markov
functors. -/
instance category : Category StrictMarkovCat.{v, u} where
  Hom C D := StrictMarkovFunctor C D
  id C := StrictMarkovFunctor.id C
  comp F G := G.comp F
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_def (C : StrictMarkovCat.{v, u}) : (𝟙 C : C ⟶ C) = StrictMarkovFunctor.id C := rfl

@[simp] theorem comp_def {C D E : StrictMarkovCat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) :
    F ≫ G = StrictMarkovFunctor.comp G F := rfl

end StrictMarkovCat

/-! ### Markov categories and Markov functors -/

/-- A Markov category in the sense of Mathlib, bundled. -/
structure MarCat : Type (max (u + 1) (v + 1)) where
  /-- The objects. -/
  carrier : Type u
  [cat : Category.{v} carrier]
  [mon : MonoidalCategory carrier]
  [markov : MarkovCategory carrier]

attribute [instance] MarCat.cat MarCat.mon MarCat.markov

namespace MarCat

instance : CoeSort MarCat.{v, u} (Type u) := ⟨MarCat.carrier⟩

/-- The bundled Markov category of `C`. -/
abbrev of (C : Type u) [Category.{v} C] [MonoidalCategory C] [MarkovCategory C] : MarCat.{v, u} := ⟨C⟩

end MarCat

/-- *Introduction.* A **Markov functor**: a strong symmetric monoidal functor (a Mathlib
`Functor.Braided` structure: strong monoidal, with structure isomorphisms
`μ : F X ⊗ F Y ≅ F (X ⊗ Y)`, `ε : 1 ≅ F 1` commuting with the symmetries) that matches the
duplicates and the discards: `μ⁻¹ ∘ F(δ_X) = δ_{F X}`, `ε⁻¹ ∘ F(ε_X) = ε_{F X}`. -/
structure MarkovFunctor (C D : MarCat.{v, u}) where
  /-- The underlying functor. -/
  toFunctor : C ⥤ D
  /-- The strong symmetric monoidal structure. -/
  braided : toFunctor.Braided
  map_copy (X : C) :
    toFunctor.map Δ[X] ≫ (Functor.Monoidal.μIso toFunctor X X).inv = Δ[toFunctor.obj X]
  map_discard (X : C) :
    toFunctor.map ε[X] ≫ (Functor.Monoidal.εIso toFunctor).inv = ε[toFunctor.obj X]

namespace MarkovFunctor

variable {C D E : MarCat.{v, u}}

theorem ext' {F G : MarkovFunctor C D} (h : F.toFunctor = G.toFunctor)
    (hb : HEq F.braided G.braided) : F = G := by
  cases F; cases G; cases h; cases hb; rfl

/-- Two strong monoidal structures on the same functor with the same `ε` and `μ` are equal. -/
theorem braided_ext {F : C ⥤ D} {b b' : F.Braided}
    (h : b.toLaxMonoidal = b'.toLaxMonoidal) : b = b' :=
  Functor.Braided.toMonoidal_injective F (Functor.Monoidal.toLaxMonoidal_injective F h)

/-- The identity Markov functor. -/
def id (C : MarCat.{v, u}) : MarkovFunctor C C where
  toFunctor := 𝟭 C
  braided := inferInstance
  map_copy X := by simp
  map_discard X := by simp

/-- The strong symmetric monoidal structure of a composite. -/
@[instance_reducible]
def compBraided (G : MarkovFunctor D E) (F : MarkovFunctor C D) :
    (F.toFunctor ⋙ G.toFunctor).Braided :=
  letI := F.braided
  letI := G.braided
  inferInstance

/-- Composition of Markov functors. -/
def comp (G : MarkovFunctor D E) (F : MarkovFunctor C D) : MarkovFunctor C E where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  braided := compBraided G F
  map_copy X := by
    let _ := F.braided
    let _ := G.braided
    have hF := F.map_copy X
    have hG := G.map_copy (F.toFunctor.obj X)
    simp only [Functor.Monoidal.μIso_inv] at hF hG ⊢
    change G.toFunctor.map (F.toFunctor.map Δ[X]) ≫
      (G.toFunctor.map (δ F.toFunctor X X) ≫ δ G.toFunctor _ _) = _
    rw [← Category.assoc, ← Functor.map_comp, hF, hG]
  map_discard X := by
    let _ := F.braided
    let _ := G.braided
    have hF := F.map_discard X
    have hG := G.map_discard (F.toFunctor.obj X)
    simp only [Functor.Monoidal.εIso_inv] at hF hG ⊢
    change G.toFunctor.map (F.toFunctor.map ε[X]) ≫
      (G.toFunctor.map (η F.toFunctor) ≫ η G.toFunctor) = _
    rw [← Category.assoc, ← Functor.map_comp, hF, hG]

theorem comp_ε (G : MarkovFunctor D E) (F : MarkovFunctor C D) :
    @Functor.LaxMonoidal.ε _ _ _ _ _ _ _ (comp G F).braided.toLaxMonoidal =
      @Functor.LaxMonoidal.ε _ _ _ _ _ _ _ G.braided.toLaxMonoidal ≫
        G.toFunctor.map (@Functor.LaxMonoidal.ε _ _ _ _ _ _ _ F.braided.toLaxMonoidal) := rfl

theorem comp_μ (G : MarkovFunctor D E) (F : MarkovFunctor C D) (X Y : C) :
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ _ (comp G F).braided.toLaxMonoidal X Y =
      @Functor.LaxMonoidal.μ _ _ _ _ _ _ _ G.braided.toLaxMonoidal _ _ ≫
        G.toFunctor.map (@Functor.LaxMonoidal.μ _ _ _ _ _ _ _ F.braided.toLaxMonoidal X Y) := rfl

theorem id_ε (C : MarCat.{v, u}) :
    @Functor.LaxMonoidal.ε _ _ _ _ _ _ _ (id C).braided.toLaxMonoidal = 𝟙 _ := rfl

theorem id_μ (C : MarCat.{v, u}) (X Y : C) :
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ _ (id C).braided.toLaxMonoidal X Y = 𝟙 _ := rfl

end MarkovFunctor

namespace MarCat

/-- *D7.* The category **`MarCat`** of Markov categories and Markov functors. -/
instance category : Category MarCat.{v, u} where
  Hom C D := MarkovFunctor C D
  id C := MarkovFunctor.id C
  comp F G := G.comp F
  id_comp F := by
    refine MarkovFunctor.ext' rfl (heq_of_eq (MarkovFunctor.braided_ext ?_))
    ext
    · exact (congrArg (fun x => _ ≫ x) (F.toFunctor.map_id _)).trans (Category.comp_id _)
    · exact (congrArg (fun x => _ ≫ x) (F.toFunctor.map_id _)).trans (Category.comp_id _)
  comp_id F := by
    refine MarkovFunctor.ext' rfl (heq_of_eq (MarkovFunctor.braided_ext ?_))
    ext
    · exact Category.id_comp _
    · exact Category.id_comp _
  assoc F G H := by
    refine MarkovFunctor.ext' rfl (heq_of_eq (MarkovFunctor.braided_ext ?_))
    ext
    · exact (congrArg (fun x => _ ≫ x) (H.toFunctor.map_comp _ _)).trans (Category.assoc _ _ _).symm
    · exact (congrArg (fun x => _ ≫ x) (H.toFunctor.map_comp _ _)).trans (Category.assoc _ _ _).symm

end MarCat

/-! ### The inclusion -/

namespace StrictMarkovFunctor

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C]
  {D : Type u} [Monoid D] [Category.{v} D] [StrictMarkov D]

/-- The strong monoidal structure of a strict functor: the structure isomorphisms are identities
(`eqToIso`), through the Stage 0 bridge. -/
def coreMonoidal (F : StrictFunctor C D) : F.toFunctor.CoreMonoidal where
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

/-- The strong symmetric monoidal structure of a strict functor. -/
@[instance_reducible]
def braided (F : StrictFunctor C D) : F.toFunctor.Braided :=
  letI : F.toFunctor.Monoidal := (coreMonoidal F).toMonoidal
  { braided := fun X Y => by
      show eqToHom (F.obj_mul X Y).symm ≫ F.map (σ_ X Y) =
        σ_ (F.obj X) (F.obj Y) ≫ eqToHom (F.obj_mul Y X).symm
      exact (Arrow.comp_eqToHom_eq_of_mk_eq (F.map_braid X Y).symm (F.obj_mul X Y).symm
        (F.obj_mul Y X).symm).symm }

theorem braided_ε (F : StrictFunctor C D) :
    @Functor.LaxMonoidal.ε _ _ _ _ _ _ F.toFunctor (braided F).toLaxMonoidal =
      eqToHom F.obj_one.symm := rfl

theorem braided_μ (F : StrictFunctor C D) (X Y : C) :
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ F.toFunctor (braided F).toLaxMonoidal X Y =
      eqToHom (F.obj_mul X Y).symm := rfl

/-- *D7.* A strict Markov functor is a Markov functor (whose structure isomorphisms are
identities). -/
def toMarkovFunctor (F : StrictMarkovFunctor C D) : MarkovFunctor (MarCat.of C) (MarCat.of D) where
  toFunctor := F.toFunctor
  braided := braided F.toStrictFunctor
  map_copy X := by
    show F.map (δ_ X) ≫ eqToHom (F.obj_mul X X) = δ_ (F.obj X)
    exact Arrow.eq_of_mk_eq ((Arrow.arrow_mk_comp_eqToHom _ _).trans (F.map_copy X))
  map_discard X := by
    show F.map (ε_ X) ≫ eqToHom F.obj_one = ε_ (F.obj X)
    exact eq_discard _

end StrictMarkovFunctor

namespace StrictMarkovCat

/-- *D7.* The inclusion **`StrictMarkovCat ⥤ MarCat`**: a strict Markov category is a Markov
category (Stage 0 bridge) and a strict Markov functor is a Markov functor. -/
def toMarCat : StrictMarkovCat.{v, u} ⥤ MarCat.{v, u} where
  obj C := MarCat.of C
  map F := StrictMarkovFunctor.toMarkovFunctor F
  map_id C := by
    refine MarkovFunctor.ext' rfl (heq_of_eq (MarkovFunctor.braided_ext ?_))
    ext
    · exact (StrictMarkovFunctor.braided_ε _).trans (by simp; rfl)
    · exact (StrictMarkovFunctor.braided_μ _ _ _).trans (by simp; rfl)
  map_comp F G := by
    refine MarkovFunctor.ext' rfl (heq_of_eq (MarkovFunctor.braided_ext ?_))
    ext
    · refine (StrictMarkovFunctor.braided_ε _).trans ?_
      show _ = eqToHom G.obj_one.symm ≫ G.toFunctor.map (eqToHom F.obj_one.symm)
      simp only [eqToHom_map, eqToHom_trans]
      rfl
    · refine (StrictMarkovFunctor.braided_μ _ _ _).trans ?_
      show _ = eqToHom (G.obj_mul _ _).symm ≫ G.toFunctor.map (eqToHom (F.obj_mul _ _).symm)
      simp only [eqToHom_map, eqToHom_trans]
      rfl

end StrictMarkovCat

end FreeMarkov
