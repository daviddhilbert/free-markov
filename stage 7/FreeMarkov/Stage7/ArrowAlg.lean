/-
Free Markov categories, Stage 7: a one-sorted calculus of arrows in a symmetric strict monoidal
category.

Following design decision D2 (`formalization/PLAN.md`), equations between morphisms whose
endpoints are only propositionally equal are stated in `Arrow C`.  This file adds the operations
needed to compute with whole composites in `Arrow C` without casts:

* `AArr.comp f g`, the composite of two arrows when the target of `f` is the source of `g`
  (and `f` otherwise), with associativity and unit laws under the matching conditions;
* `AArr.tensor`, `AArr.id`, `AArr.braid`, and the axioms of a symmetric strict monoidal
  category in this form (interchange, associativity and units of `⊗`, naturality of the
  symmetry, `σ ∘ σ = 1`, both hexagons, `σ_{1,a} = 1`).

Objects inside `AArr.id`, `AArr.braid` are ordinary arguments, so they can be rewritten freely.
-/
module

public import FreeMarkov.Stage0

@[expose] public section

universe v u

namespace FreeMarkov

open CategoryTheory StrictSMC

namespace AArr

section Category

variable {C : Type u} [Category.{v} C]

/-- The composite of two arrows, "first `f`, then `g`", when they meet; `f` otherwise. -/
noncomputable def comp (f g : Arrow C) : Arrow C := by
  classical
  exact if h : f.right = g.left then Arrow.mk (f.hom ≫ eqToHom h ≫ g.hom) else f

/-- The identity arrow of an object. -/
def id (X : C) : Arrow C := Arrow.mk (𝟙 X)

@[simp] theorem id_left (X : C) : (id X).left = X := rfl
@[simp] theorem id_right (X : C) : (id X).right = X := rfl

theorem comp_eq {f g : Arrow C} (h : f.right = g.left) :
    comp f g = Arrow.mk (f.hom ≫ eqToHom h ≫ g.hom) := by
  unfold comp
  simp [h]

theorem comp_mk {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    comp (Arrow.mk f) (Arrow.mk g) = Arrow.mk (f ≫ g) := by
  rw [comp_eq rfl]; simp

theorem comp_left {f g : Arrow C} (_h : f.right = g.left) : (comp f g).left = f.left := by
  classical
  unfold comp; split <;> rfl

@[simp] theorem comp_left' (f g : Arrow C) : (comp f g).left = f.left := by
  classical
  unfold comp; split <;> rfl

theorem comp_right {f g : Arrow C} (h : f.right = g.left) : (comp f g).right = g.right := by
  rw [comp_eq h]; rfl

open Classical in
@[simp] theorem comp_right_ite (f g : Arrow C) :
    (comp f g).right = if f.right = g.left then g.right else f.right := by
  split_ifs with h
  · exact comp_right h
  · unfold comp; simp [h]

theorem comp_assoc {f g k : Arrow C} (h₁ : f.right = g.left) (h₂ : g.right = k.left) :
    comp (comp f g) k = comp f (comp g k) := by
  rw [comp_eq h₁, comp_eq (by exact h₂), comp_eq h₂, comp_eq (by exact h₁)]
  simp

theorem id_comp {X : C} {f : Arrow C} (h : X = f.left) : comp (id X) f = f := by
  rw [comp_eq h]; simp [id]

theorem comp_id {X : C} {f : Arrow C} (h : f.right = X) : comp f (id X) = f := by
  rw [comp_eq h]; simp [id]

theorem id_congr {X Y : C} (h : X = Y) : id X = id Y := by rw [h]

theorem mk_hom (f : Arrow C) : Arrow.mk f.hom = f := rfl

end Category

section Monoidal

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictSMC C]

/-- The monoidal product of two arrows. -/
def tensor (f g : Arrow C) : Arrow C := Arrow.mk (f.hom ⊗ₛ g.hom)

/-- The symmetry `σ_{X,Y}` as an arrow. -/
def braid (X Y : C) : Arrow C := Arrow.mk (σ_ X Y)

@[simp] theorem tensor_left (f g : Arrow C) : (tensor f g).left = f.left * g.left := rfl
@[simp] theorem tensor_right (f g : Arrow C) : (tensor f g).right = f.right * g.right := rfl
@[simp] theorem braid_left (X Y : C) : (braid X Y).left = X * Y := rfl
@[simp] theorem braid_right (X Y : C) : (braid X Y).right = Y * X := rfl

theorem tensor_mk {a b c d : C} (f : a ⟶ b) (g : c ⟶ d) :
    tensor (Arrow.mk f) (Arrow.mk g) = Arrow.mk (f ⊗ₛ g) := rfl

theorem tensor_id (X Y : C) : tensor (id X) (id Y) = id (X * Y) :=
  congrArg Arrow.mk (tensorHom_id X Y)

/-- The interchange law. -/
theorem tensor_comp {f f' g g' : Arrow C} (h₁ : f.right = f'.left) (h₂ : g.right = g'.left) :
    tensor (comp f f') (comp g g') = comp (tensor f g) (tensor f' g') := by
  rw [comp_eq h₁, comp_eq h₂, comp_eq (by rw [tensor_right, tensor_left, h₁, h₂])]
  simp only [tensor, Arrow.mk_hom, tensorHom_comp]
  simp

theorem tensor_assoc (f g k : Arrow C) : tensor (tensor f g) k = tensor f (tensor g k) :=
  tensorHom_assoc f.hom g.hom k.hom

theorem id_one_tensor (f : Arrow C) : tensor (id 1) f = f :=
  id_one_tensorHom f.hom

theorem tensor_id_one (f : Arrow C) : tensor f (id 1) = f :=
  tensorHom_id_one f.hom

theorem braid_natural (f g : Arrow C) :
    comp (tensor f g) (braid f.right g.right) = comp (braid f.left g.left) (tensor g f) := by
  show comp (Arrow.mk (f.hom ⊗ₛ g.hom)) (Arrow.mk (σ_ f.right g.right)) =
    comp (Arrow.mk (σ_ f.left g.left)) (Arrow.mk (g.hom ⊗ₛ f.hom))
  rw [comp_mk, comp_mk, StrictSMC.braid_natural]

theorem braid_braid (X Y : C) : comp (braid X Y) (braid Y X) = id (X * Y) := by
  rw [braid, braid, comp_mk, StrictSMC.braid_braid]; rfl

theorem hexagon (X Y Z : C) :
    braid X (Y * Z) = comp (tensor (braid X Y) (id Z)) (tensor (id Y) (braid X Z)) := by
  rw [comp_eq (mul_assoc Y X Z)]
  exact StrictSMC.hexagon X Y Z

theorem hexagon_reverse (X Y Z : C) :
    braid (X * Y) Z = comp (tensor (id X) (braid Y Z)) (tensor (braid X Z) (id Y)) := by
  rw [comp_eq (mul_assoc X Z Y).symm]
  exact StrictSMC.hexagon_reverse X Y Z

theorem braid_one_right (X : C) : braid X 1 = id X := by
  have h := hexagon X 1 1
  rw [tensor_id_one, id_one_tensor, mul_one] at h
  -- `h : σ_{X,1} = σ_{X,1} ∘ σ_{X,1}`; compose with `σ_{1,X}`.
  have h2 : comp (braid X 1) (braid 1 X) = comp (comp (braid X 1) (braid X 1)) (braid 1 X) := by
    rw [← h]
  rw [comp_assoc (by simp) rfl, braid_braid, comp_id (by simp)] at h2
  rw [← h2]
  exact id_congr (mul_one X)

theorem braid_one_left (X : C) : braid 1 X = id X := by
  have h := braid_braid 1 X
  rw [braid_one_right, comp_id (by simp)] at h
  rw [h]; exact id_congr (one_mul X)

theorem tensor_id_comp (X : C) {g g' : Arrow C} (h : g.right = g'.left) :
    tensor (id X) (comp g g') = comp (tensor (id X) g) (tensor (id X) g') := by
  rw [← tensor_comp rfl h, id_comp (X := X) (f := id X) rfl]

theorem tensor_comp_id (X : C) {g g' : Arrow C} (h : g.right = g'.left) :
    tensor (comp g g') (id X) = comp (tensor g (id X)) (tensor g' (id X)) := by
  rw [← tensor_comp h rfl, id_comp (X := X) (f := id X) rfl]

/-- `f ⊗ g = (1 ⊗ g) ∘ (f ⊗ 1)`. -/
theorem tensor_eq_comp_id_left (f g : Arrow C) :
    tensor f g = comp (tensor (id f.left) g) (tensor f (id g.right)) := by
  rw [← tensor_comp rfl rfl, id_comp rfl, comp_id rfl]

/-- `f ⊗ g = (f ⊗ 1) ∘ (1 ⊗ g)`. -/
theorem tensor_eq_comp_id_right (f g : Arrow C) :
    tensor f g = comp (tensor f (id g.left)) (tensor (id f.right) g) := by
  rw [← tensor_comp rfl rfl, id_comp rfl, comp_id rfl]

omit [Monoid C] [StrictSMC C] in
/-- Arrows between equal objects: `Arrow.mk (eqToHom h)` is an identity. -/
theorem mk_eqToHom {X Y : C} (h : X = Y) : Arrow.mk (eqToHom h) = id X := Arrow.mk_eqToHom h

end Monoidal

end AArr

/-- Closes equations between the endpoints of arrows built with `AArr`. -/
macro "aobj" : tactic => `(tactic| simp [mul_assoc])

end FreeMarkov
