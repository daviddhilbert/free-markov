/-
Free Markov categories, Stage 8: left-bracketed products and the comparison isomorphisms of a
strong monoidal functor out of a strict monoidal category.

* `lpR ob r`: the left-bracketed product `(…((ob a_1 ⊗ ob a_2) ⊗ ob a_3) … ) ⊗ ob a_n` in a monoidal
  category, indexed by the *reversed* list `r = [a_n, …, a_1]` (so that the recursion is on the last
  factor); `lp ob w` for a word `w`; `lpRMap`, `lpMap` on morphisms.  These are the objects
  `eval(a_1 … a_n)` that the strictification of Section 5 (C2) fixes: `eval(∅) = 1`, `eval(a) = a`,
  `eval(a_1 … a_{n+1}) = eval(a_1 … a_n) ⊗ a_{n+1}`.
* `wR o r`: the corresponding product `o a_1 * … * o a_n` in a monoid (`wR_eq_lift`).
* `cmpR F o r : lpR (F ∘ o) r ≅ F (wR o r)`: the comparison isomorphism of a strong monoidal functor
  `F` out of a strict monoidal category, built from the structure isomorphisms `ε`, `μ` of `F`.
* `cmpR_naturality`: a monoidal natural transformation commutes with the comparison isomorphisms.
* `tensor_of_snoc`: a family of morphisms `θ_X : F X → F' X` that is compatible with `ε` and with
  `μ_{X, o a}` for single letters is compatible with `μ_{X, Y}` for every product `Y` of letters.

No cited result is used in this file.
-/
module

public import FreeMarkov.Stage0.Strict.Markov
public import FreeMarkov.Stage0.Strict.Functor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

@[expose] public section

universe w u₁ v₁ u₂ v₂

namespace FreeMarkov

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Category

variable {S : Type w}

/-! ### Left-bracketed products -/

section Products

variable {M : Type u₂} [Category.{v₂} M] [MonoidalCategory M]

/-- The left-bracketed product of the objects `ob a` along a **reversed** list:
`lpR ob [] = 1`, `lpR ob [a] = ob a`, `lpR ob (a :: r) = lpR ob r ⊗ ob a` for `r ≠ []`. -/
def lpR (ob : S → M) : List S → M
  | [] => 𝟙_ M
  | [a] => ob a
  | a :: b :: r => lpR ob (b :: r) ⊗ ob a

/-- The left-bracketed product of a family of morphisms along a reversed list. -/
def lpRMap {ob ob' : S → M} (f : ∀ a, ob a ⟶ ob' a) : (r : List S) → (lpR ob r ⟶ lpR ob' r)
  | [] => 𝟙 _
  | [a] => f a
  | a :: b :: r => lpRMap f (b :: r) ⊗ₘ f a

/-- The left-bracketed product `(…(ob a_1 ⊗ ob a_2) ⊗ …) ⊗ ob a_n` of a word `a_1 … a_n`:
the object `eval(a_1 … a_n)` of Section 5. -/
abbrev lp (ob : S → M) (w : FreeMonoid S) : M := lpR ob (FreeMonoid.toList w).reverse

/-- The left-bracketed product of a family of morphisms along a word. -/
abbrev lpMap {ob ob' : S → M} (f : ∀ a, ob a ⟶ ob' a) (w : FreeMonoid S) : lp ob w ⟶ lp ob' w :=
  lpRMap f (FreeMonoid.toList w).reverse

@[simp] theorem lpRMap_id (ob : S → M) : ∀ r, lpRMap (fun a => 𝟙 (ob a)) r = 𝟙 (lpR ob r)
  | [] => rfl
  | [_] => rfl
  | a :: b :: r => by
    change lpRMap _ (b :: r) ⊗ₘ 𝟙 _ = _
    rw [lpRMap_id ob (b :: r)]
    exact id_tensorHom_id _ _

theorem lpRMap_comp {ob ob' ob'' : S → M} (f : ∀ a, ob a ⟶ ob' a) (g : ∀ a, ob' a ⟶ ob'' a) :
    ∀ r, lpRMap (fun a => f a ≫ g a) r = lpRMap f r ≫ lpRMap g r
  | [] => (comp_id _).symm
  | [_] => rfl
  | a :: b :: r => by
    change lpRMap _ (b :: r) ⊗ₘ (f a ≫ g a) = (lpRMap f (b :: r) ⊗ₘ f a) ≫ (lpRMap g (b :: r) ⊗ₘ g a)
    rw [lpRMap_comp f g (b :: r), tensorHom_comp_tensorHom]

theorem lpRMap_eqToHom {ob ob' : S → M} (h : ob = ob') (r : List S) :
    lpRMap (fun a => eqToHom (congrFun h a)) r = eqToHom (congrArg (fun o => lpR o r) h) := by
  subst h
  simp

@[simp] theorem lpMap_id (ob : S → M) (w : FreeMonoid S) : lpMap (fun a => 𝟙 (ob a)) w = 𝟙 _ :=
  lpRMap_id ob _

@[reassoc]
theorem lpMap_comp {ob ob' ob'' : S → M} (f : ∀ a, ob a ⟶ ob' a) (g : ∀ a, ob' a ⟶ ob'' a)
    (w : FreeMonoid S) : lpMap (fun a => f a ≫ g a) w = lpMap f w ≫ lpMap g w :=
  lpRMap_comp f g _

theorem lpMap_eqToHom {ob ob' : S → M} (h : ob = ob') (w : FreeMonoid S) :
    lpMap (fun a => eqToHom (congrFun h a)) w = eqToHom (congrArg (fun o => lp o w) h) :=
  lpRMap_eqToHom h _

/-- A family of isomorphisms gives an isomorphism of left-bracketed products. -/
@[simps]
def lpMapIso {ob ob' : S → M} (f : ∀ a, ob a ≅ ob' a) (w : FreeMonoid S) : lp ob w ≅ lp ob' w where
  hom := lpMap (fun a => (f a).hom) w
  inv := lpMap (fun a => (f a).inv) w
  hom_inv_id := by rw [← lpMap_comp]; simp
  inv_hom_id := by rw [← lpMap_comp]; simp

theorem lp_of (ob : S → M) (a : S) : lp ob (FreeMonoid.of a) = ob a := rfl

theorem lp_of_mul_of (ob : S → M) (a b : S) :
    lp ob (FreeMonoid.of a * FreeMonoid.of b) = ob a ⊗ ob b := rfl

theorem lp_one (ob : S → M) : lp ob 1 = 𝟙_ M := rfl

end Products

/-! ### Products of letters in a monoid -/

section Words

variable {C : Type u₁} [Monoid C]

/-- The product `o a_1 * … * o a_n` along the reversed list `[a_n, …, a_1]`, with the same recursion
as `lpR`. -/
def wR (o : S → C) : List S → C
  | [] => 1
  | [a] => o a
  | a :: b :: r => wR o (b :: r) * o a

theorem wR_eq_lift (o : S → C) : ∀ r : List S, wR o r = FreeMonoid.lift o (FreeMonoid.ofList r.reverse)
  | [] => by simp [wR]
  | [a] => by simp [wR]
  | a :: b :: r => by
    rw [wR, wR_eq_lift o (b :: r), List.reverse_cons (a := a), FreeMonoid.ofList_append, map_mul]
    simp

theorem wR_of_eq (w : FreeMonoid S) : wR FreeMonoid.of (FreeMonoid.toList w).reverse = w := by
  rw [wR_eq_lift, List.reverse_reverse, FreeMonoid.ofList_toList]
  exact DFunLike.congr_fun (FreeMonoid.hom_eq (f := FreeMonoid.lift FreeMonoid.of)
    (g := MonoidHom.id _) (fun _ => by simp)) w

theorem wR_map (o : S → C) {D : Type*} [Monoid D] (φ : C →* D) :
    ∀ r : List S, φ (wR o r) = wR (fun a => φ (o a)) r
  | [] => map_one φ
  | [_] => rfl
  | a :: b :: r => by rw [wR, map_mul, wR_map o φ (b :: r)]; rfl

end Words

/-! ### Comparison isomorphisms -/

section Comparison

open StrictSMC

variable {C : Type u₁} [Monoid C] [Category.{v₁} C] [StrictSMC C]
  {M : Type u₂} [Category.{v₂} M] [MonoidalCategory M]

/-- The **comparison isomorphism** `lpR (F ∘ o) r ≅ F (o a_1 * … * o a_n)` of a strong monoidal
functor `F` out of a strict monoidal category: `ε` for the empty word, the identity for one letter,
and `(φ_r ⊗ 1) ≫ μ_{wR r, o a}` for the product with one more letter. -/
noncomputable def cmpR (F : C ⥤ M) [F.Monoidal] (o : S → C) :
    (r : List S) → (lpR (fun a => F.obj (o a)) r ≅ F.obj (wR o r))
  | [] => Functor.Monoidal.εIso F
  | [_] => Iso.refl _
  | a :: b :: r => whiskerRightIso (cmpR F o (b :: r)) (F.obj (o a)) ≪≫
      Functor.Monoidal.μIso F (wR o (b :: r)) (o a)

variable (F : C ⥤ M) [F.Monoidal] (o : S → C)

@[simp] theorem cmpR_nil_hom : (cmpR F o []).hom = ε F := rfl
@[simp] theorem cmpR_nil_inv : (cmpR F o []).inv = η F := rfl
@[simp] theorem cmpR_single_hom (a : S) : (cmpR F o [a]).hom = 𝟙 _ := rfl
@[simp] theorem cmpR_single_inv (a : S) : (cmpR F o [a]).inv = 𝟙 _ := rfl
theorem cmpR_cons_hom (a b : S) (r : List S) :
    (cmpR F o (a :: b :: r)).hom = (cmpR F o (b :: r)).hom ▷ F.obj (o a) ≫ μ F (wR o (b :: r)) (o a) :=
  rfl
theorem cmpR_pair_hom (a b : S) : (cmpR F o [b, a]).hom = μ F (o a) (o b) :=
  (congrArg (· ≫ _) (id_whiskerRight _ _)).trans (id_comp _)

theorem cmpR_cons_inv (a b : S) (r : List S) :
    (cmpR F o (a :: b :: r)).inv = δ F (wR o (b :: r)) (o a) ≫ (cmpR F o (b :: r)).inv ▷ F.obj (o a) :=
  rfl

omit [Monoid C] [StrictSMC C] [MonoidalCategory M] in
/-- Every family of morphisms indexed by the objects is natural with respect to `eqToHom`. -/
theorem family_eqToHom {F F' : C ⥤ M} (θ : ∀ X : C, F.obj X ⟶ F'.obj X) {X Y : C} (h : X = Y) :
    F.map (eqToHom h) ≫ θ Y = θ X ≫ F'.map (eqToHom h) := by
  subst h; simp

variable {F}

theorem μ_one_right (X : C) :
    μ F X (𝟙_ C) = F.obj X ◁ η F ≫ (ρ_ (F.obj X)).hom ≫ F.map (eqToHom (mul_one X).symm) := by
  rw [Functor.LaxMonoidal.right_unitality F X]
  simp

theorem μ_one_left (X : C) :
    μ F (𝟙_ C) X = η F ▷ F.obj X ≫ (λ_ (F.obj X)).hom ≫ F.map (eqToHom (one_mul X).symm) := by
  rw [Functor.LaxMonoidal.left_unitality F X]
  simp

@[reassoc]
theorem whiskerLeft_μ_comp_μ' (X Y Z : C) :
    F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z ≫
        F.map (eqToHom (mul_assoc X Y Z)) := by
  have h := Functor.LaxMonoidal.associativity F X Y Z
  simp only [StrictSMC.associator_eq, eqToIso.hom] at h
  rw [h, Iso.inv_hom_id_assoc]

/-- A monoidal natural transformation commutes with the comparison isomorphisms. -/
theorem cmpR_naturality {F' : C ⥤ M} [F'.Monoidal] (θ : F ⟶ F') [NatTrans.IsMonoidal θ] :
    ∀ r : List S, (cmpR F o r).hom ≫ θ.app (wR o r) =
      lpRMap (fun a => θ.app (o a)) r ≫ (cmpR F' o r).hom
  | [] => by
    simp only [cmpR_nil_hom, lpRMap]
    exact (NatTrans.IsMonoidal.unit (τ := θ)).trans (id_comp _).symm
  | [_] => (id_comp _).trans (comp_id _).symm
  | a :: b :: r => by
    rw [cmpR_cons_hom, cmpR_cons_hom]
    change (_ ▷ _ ≫ μ F _ _) ≫ θ.app (wR o (b :: r) ⊗ o a) =
      (lpRMap _ (b :: r) ⊗ₘ θ.app (o a)) ≫ _
    rw [assoc, NatTrans.IsMonoidal.tensor, ← assoc, ← assoc]
    congr 1
    rw [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.tensorHom_id, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, cmpR_naturality θ (b :: r), id_comp, comp_id]

/-- The unit case of monoidality: `μ_{1,Y}` followed by a component on `1 ⊗ Y = Y`. -/
theorem unit_case {F' : C ⥤ M} [F'.Monoidal] (Y : C) (f : F.obj Y ⟶ F'.obj Y) :
    μ F (𝟙_ C) Y ≫ F.map (eqToHom (one_mul Y)) ≫ f ≫ F'.map (eqToHom (one_mul Y).symm) =
      ((η F ≫ ε F') ⊗ₘ f) ≫ μ F' (𝟙_ C) Y := by
  rw [μ_one_left (F := F), μ_one_left (F := F'), assoc, assoc, ← F.map_comp_assoc, eqToHom_trans,
    eqToHom_refl, F.map_id, id_comp, tensorHom_def, assoc, whisker_exchange_assoc,
    ← comp_whiskerRight_assoc, assoc, Functor.Monoidal.ε_η, comp_id,
    leftUnitor_naturality_assoc]

omit [Monoid C] [StrictSMC C] in
@[reassoc]
theorem whiskerRight_comp_tensorHom' {X Y X' Y' Z : M} (f : X ⟶ Y) (g : Y ⟶ X') (h : Z ⟶ Y') :
    f ▷ Z ≫ (g ⊗ₘ h) = (f ≫ g) ⊗ₘ h := by
  rw [← MonoidalCategory.tensorHom_id, tensorHom_comp_tensorHom, id_comp]

omit [Monoid C] [StrictSMC C] in
@[reassoc]
theorem whiskerLeft_comp_tensorHom' {X Y X' Y' Z : M} (f : X ⟶ Y) (g : Z ⟶ X') (h : Y ⟶ Y') :
    Z ◁ f ≫ (g ⊗ₘ h) = g ⊗ₘ (f ≫ h) := by
  rw [← MonoidalCategory.id_tensorHom, tensorHom_comp_tensorHom, id_comp]

omit [Monoid C] [StrictSMC C] in
@[reassoc]
theorem comp_tensorHom' {X Y X' Y' Z : M} (f : X ⟶ Y) (g : Y ⟶ X') (h : Z ⟶ Y') :
    (f ≫ g) ⊗ₘ h = (f ⊗ₘ h) ≫ g ▷ Y' := by
  rw [← MonoidalCategory.tensorHom_id, tensorHom_comp_tensorHom, comp_id]

omit [Monoid C] [StrictSMC C] in
@[reassoc]
theorem tensorHom_comp' {X Y X' Y' Z : M} (f : X ⟶ Y) (g : Y ⟶ X') (h : Z ⟶ Y') :
    h ⊗ₘ (f ≫ g) = (h ⊗ₘ f) ≫ Y' ◁ g := by
  rw [← MonoidalCategory.id_tensorHom, tensorHom_comp_tensorHom, comp_id]

/-- Monoidality from single letters: a family `θ_X : F X → F' X` compatible with `ε` and with
`μ_{X, o a}` for every letter `a` is compatible with `μ_{X, Y}` for every product `Y` of letters. -/
theorem tensor_of_snoc {F' : C ⥤ M} [F'.Monoidal] (θ : ∀ X : C, F.obj X ⟶ F'.obj X)
    (h1 : ε F ≫ θ (𝟙_ C) = ε F')
    (h2 : ∀ (X : C) (a : S), μ F X (o a) ≫ θ (X ⊗ o a) = (θ X ⊗ₘ θ (o a)) ≫ μ F' X (o a))
    (X : C) : ∀ r : List S,
      μ F X (wR o r) ≫ θ (X ⊗ wR o r) = (θ X ⊗ₘ θ (wR o r)) ≫ μ F' X (wR o r)
  | [] => by
    have hθ : θ (𝟙_ C) = η F ≫ ε F' := by rw [← h1, Functor.Monoidal.η_ε_assoc]
    change μ F X (𝟙_ C) ≫ θ (X ⊗ 𝟙_ C) = (θ X ⊗ₘ θ (𝟙_ C)) ≫ μ F' X (𝟙_ C)
    rw [μ_one_right (F := F), μ_one_right (F := F'), assoc, assoc]
    change _ ≫ _ ≫ F.map (eqToHom (mul_one X).symm) ≫ θ (X * 1) = _
    rw [family_eqToHom θ (mul_one X).symm]
    have key : (θ X ⊗ₘ (η F ≫ ε F')) ≫ F'.obj X ◁ η F' ≫ (ρ_ (F'.obj X)).hom =
        F.obj X ◁ η F ≫ (ρ_ (F.obj X)).hom ≫ θ X := by
      rw [tensorHom_def', assoc, ← whisker_exchange_assoc, ← whiskerLeft_comp_assoc, assoc,
        Functor.Monoidal.ε_η, comp_id, rightUnitor_naturality]
    rw [hθ, reassoc_of% key]
  | [a] => h2 X a
  | a :: b :: r => by
    have ih := tensor_of_snoc θ h1 h2 X (b :: r)
    have hB := h2 (wR o (b :: r)) a
    have hXB := h2 (X ⊗ wR o (b :: r)) a
    change μ F X (wR o (b :: r) ⊗ o a) ≫ θ (X ⊗ (wR o (b :: r) ⊗ o a)) =
      (θ X ⊗ₘ θ (wR o (b :: r) ⊗ o a)) ≫ μ F' X (wR o (b :: r) ⊗ o a)
    rw [← cancel_epi (F.obj X ◁ μ F (wR o (b :: r)) (o a)), whiskerLeft_μ_comp_μ'_assoc (F := F),
      show θ (X ⊗ (wR o (b :: r) ⊗ o a)) = θ (X * (wR o (b :: r) * o a)) from rfl,
      family_eqToHom θ (mul_assoc X (wR o (b :: r)) (o a)),
      show θ (X * wR o (b :: r) * o a) = θ ((X ⊗ wR o (b :: r)) ⊗ o a) from rfl,
      reassoc_of% hXB, whiskerRight_comp_tensorHom'_assoc, ih, comp_tensorHom', assoc,
      ← associator_inv_naturality_assoc, ← whiskerLeft_μ_comp_μ' (F := F'),
      whiskerLeft_comp_tensorHom'_assoc, hB, tensorHom_comp', assoc]

end Comparison

end FreeMarkov
