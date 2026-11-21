/-
Free Markov categories, Stage 3: duplicates and discards on words in a quotient
`F_s(G) / S_T`, from duplicates and discards on letters.

Given, for every letter `a ∈ S`, a comonoid structure `(δ_a, ε_a)` on the one-letter word
`a` in `F_s(G) / S_T`, the comonoid on a word `a_1 ⋯ a_n` is the monoidal product of the
comonoids on its letters (Mathlib's `ComonObj (A ⊗ B)` in a braided category, through the
bridge of Stage 0).  This is the paper's definition read through (1.2): "`δ_{ab}` and
`(1_a ⊗ σ_{ab} ⊗ 1_b) ∘ (δ_a ⊗ δ_b)` are represented by the same diagram ... and
`ε_{ab} = ε_a ⊗ ε_b`".  The comonoid laws (1.1) and the equations (1.2) for all words
follow from the letters by Mathlib's theory of comonoids (`Comon.monoidal`).
-/
module

public import FreeMarkov.Stage3.Induction
public import Mathlib.CategoryTheory.Monoidal.CommComon_

@[expose] public section

universe u w v u₁ v₁

namespace FreeMarkov

open CategoryTheory MonoidalCategory StrictSMC ComonObj

/-! ### Two facts on comonoid objects -/

section Comon

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- Comonoid structures with the same counit and comultiplication are equal. -/
theorem ComonObj.ext' {X : C} {c₁ c₂ : ComonObj X} (h₁ : c₁.counit = c₂.counit)
    (h₂ : c₁.comul = c₂.comul) : c₁ = c₂ := by
  cases c₁
  cases c₂
  cases h₁
  cases h₂
  rfl

/-- If the identity (or a morphism equal to it) is a comonoid morphism between two
comonoid structures on the same object, the two structures are equal. -/
theorem ComonObj.eq_of_isComonHom {X : C} (c₁ c₂ : ComonObj X) (f : X ⟶ X) (hf : f = 𝟙 X)
    (h : @IsComonHom C _ _ X X c₁ c₂ f) : c₂ = c₁ := by
  have h₁ := @IsComonHom.hom_counit C _ _ X X c₁ c₂ f h
  have h₂ := @IsComonHom.hom_comul C _ _ X X c₁ c₂ f h
  rw [hf, Category.id_comp] at h₁ h₂
  rw [id_tensorHom_id, Category.comp_id] at h₂
  exact ComonObj.ext' h₁ h₂

end Comon

/-! ### Comonoids on words in `F_s(G) / S_T` -/

namespace JoyalStreet

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} (J : JoyalStreet G)
  (T : Set (Template.{u} G)) (hT : Template.IsSymmetric T)

/-- A word, regarded as an object of `F_s(G) / S_T`. -/
def word (a : FreeMonoid S) : J.Quot T hT := a

/-- The monoidal product of two comonoids (Mathlib's instance for braided categories). -/
@[reducible] noncomputable def tensorComon (A B : J.Quot T hT) (cA : ComonObj A)
    (cB : ComonObj B) : ComonObj (A ⊗ B) :=
  inferInstance

theorem tensorComon_comul (A B : J.Quot T hT) (cA : ComonObj A) (cB : ComonObj B) :
    (J.tensorComon T hT A B cA cB).comul = (cA.comul ⊗ₘ cB.comul) ≫ tensorμ A A B B :=
  Comon.tensorObj_comul A B

theorem tensorComon_counit (A B : J.Quot T hT) (cA : ComonObj A) (cB : ComonObj B) :
    (J.tensorComon T hT A B cA cB).counit =
      (cA.counit ⊗ₘ cB.counit) ≫ (λ_ (𝟙_ (J.Quot T hT))).hom :=
  Comon.tensorObj_counit A B

/-- The unit comonoid is a left unit for the monoidal product of comonoids. -/
theorem tensorComon_unit_left (B : J.Quot T hT) (cB : ComonObj B) :
    J.tensorComon T hT (𝟙_ _) B (ComonObj.instTensorUnit _) cB = cB := by
  have hU : (𝟙_ (Comon (J.Quot T hT))).comon = ComonObj.instTensorUnit (J.Quot T hT) :=
    ComonObj.ext' (Comon.monoidal_tensorUnit_comon_counit _)
      (Comon.monoidal_tensorUnit_comon_comul _)
  have hf : (λ_ (Comon.mk B)).hom.hom = 𝟙 B := by
    rw [Comon.monoidal_leftUnitor_hom_hom]
    show (𝟙 _ ⊗ₛ 𝟙 _) ≫ eqToHom (one_mul _) = _
    rw [StrictSMC.tensorHom_id, Category.id_comp]
    exact eqToHom_refl _ _
  have := ComonObj.eq_of_isComonHom (X := B) _ cB _ hf (λ_ (Comon.mk B)).hom.isComonHom_hom
  rw [← hU]
  exact this.symm

/-- The unit comonoid is a right unit for the monoidal product of comonoids on a
one-letter word. -/
theorem tensorComon_unit_right (x : S) (cA : ComonObj (J.word T hT (FreeMonoid.of x))) :
    J.tensorComon T hT (J.word T hT (FreeMonoid.of x)) (𝟙_ _) cA
      (ComonObj.instTensorUnit _) = cA := by
  have hU : (𝟙_ (Comon (J.Quot T hT))).comon = ComonObj.instTensorUnit (J.Quot T hT) :=
    ComonObj.ext' (Comon.monoidal_tensorUnit_comon_counit _)
      (Comon.monoidal_tensorUnit_comon_comul _)
  have hf : (ρ_ (@Comon.mk _ _ _ (J.word T hT (FreeMonoid.of x)) cA)).hom.hom =
      𝟙 (J.word T hT (FreeMonoid.of x)) := by
    rw [Comon.monoidal_rightUnitor_hom_hom]
    show (𝟙 _ ⊗ₛ 𝟙 _) ≫ eqToHom (mul_one _) = _
    rw [StrictSMC.tensorHom_id, Category.id_comp]
    exact eqToHom_refl _ _
  have := ComonObj.eq_of_isComonHom (X := J.word T hT (FreeMonoid.of x)) _ cA _ hf
    (ρ_ (@Comon.mk _ _ _ (J.word T hT (FreeMonoid.of x)) cA)).hom.isComonHom_hom
  rw [← hU]
  exact this.symm

/-- Associativity of the monoidal product of comonoids, when the first factor is a
one-letter word (so that both bracketings are the same object). -/
theorem tensorComon_assoc (x : S) (cA : ComonObj (J.word T hT (FreeMonoid.of x)))
    (B C : J.Quot T hT) (cB : ComonObj B) (cC : ComonObj C) :
    J.tensorComon T hT _ _ cA (J.tensorComon T hT B C cB cC) =
      J.tensorComon T hT _ _ (J.tensorComon T hT _ B cA cB) cC := by
  have hf : (α_ (@Comon.mk _ _ _ (J.word T hT (FreeMonoid.of x)) cA) (Comon.mk B)
      (Comon.mk C)).hom.hom = 𝟙 _ := by
    rw [Comon.monoidal_associator_hom_hom]
    show (𝟙 _ ⊗ₛ 𝟙 _) ≫ eqToHom (mul_assoc _ _ _) ≫ (𝟙 _ ⊗ₛ 𝟙 _) = _
    rw [StrictSMC.tensorHom_id, StrictSMC.tensorHom_id, Category.id_comp, Category.comp_id]
    exact eqToHom_refl _ _
  exact ComonObj.eq_of_isComonHom _ _ _ hf
    (α_ (@Comon.mk _ _ _ (J.word T hT (FreeMonoid.of x)) cA) (Comon.mk B)
      (Comon.mk C)).hom.isComonHom_hom

variable (L : (x : S) → ComonObj (J.word T hT (FreeMonoid.of x)))

/-- The comonoid on a word: the monoidal product of the comonoids on its letters, the
unit comonoid on the empty word. -/
@[reducible] noncomputable def wordComon :
    (l : List S) → ComonObj (J.word T hT (FreeMonoid.ofList l))
  | [] => ComonObj.instTensorUnit (J.Quot T hT)
  | x :: l => J.tensorComon T hT (J.word T hT (FreeMonoid.of x))
      (J.word T hT (FreeMonoid.ofList l)) (L x) (wordComon l)

/-- The comonoid on a concatenation is the monoidal product of the comonoids. -/
theorem wordComon_append (l l' : List S) :
    J.wordComon T hT L (l ++ l') =
      J.tensorComon T hT _ _ (J.wordComon T hT L l) (J.wordComon T hT L l') := by
  induction l with
  | nil => exact (J.tensorComon_unit_left T hT _ _).symm
  | cons x l ih =>
    change J.tensorComon T hT _ _ (L x) (J.wordComon T hT L (l ++ l')) = _
    rw [ih]
    exact J.tensorComon_assoc T hT x (L x) _ _ _ _

theorem wordComon_singleton (x : S) : J.wordComon T hT L [x] = L x :=
  J.tensorComon_unit_right T hT x (L x)

variable (Lc : ∀ x : S, @IsCommComonObj _ _ _ _ (J.word T hT (FreeMonoid.of x)) (L x))

include Lc in
/-- The comonoid on a word is commutative if those on the letters are. -/
theorem wordComm : (l : List S) →
    @IsCommComonObj _ _ _ _ (J.word T hT (FreeMonoid.ofList l)) (J.wordComon T hT L l)
  | [] => by
    let := ComonObj.instTensorUnit (J.Quot T hT)
    exact CommComon.instCommComonObjUnit
  | x :: l =>
    @instIsCommComonObjTensorObj (J.Quot T hT) _ _ _ (J.word T hT (FreeMonoid.of x))
      (J.word T hT (FreeMonoid.ofList l)) (L x) (J.wordComon T hT L l) (Lc x) (wordComm l)

/-- An object of `F_s(G) / S_T`, as a word. -/
def unword (a : J.Quot T hT) : FreeMonoid S := a

/-- The comonoid on an object of `F_s(G) / S_T` (a word). -/
@[reducible] noncomputable def objComon (a : J.Quot T hT) : ComonObj a :=
  J.wordComon T hT L (FreeMonoid.toList (J.unword T hT a))

theorem objComon_mul (a b : J.Quot T hT) :
    J.objComon T hT L (a * b) =
      J.tensorComon T hT a b (J.objComon T hT L a) (J.objComon T hT L b) :=
  J.wordComon_append T hT L _ _

/-- The duplicate `δ_a` on a word `a`. -/
noncomputable def copyW (a : J.Quot T hT) : a ⟶ a * a :=
  (J.objComon T hT L a).comul

/-- The discard `ε_a` on a word `a`. -/
noncomputable def discardW (a : J.Quot T hT) : a ⟶ 1 :=
  (J.objComon T hT L a).counit

theorem copyW_assoc (a : J.Quot T hT) :
    Arrow.mk (J.copyW T hT L a ≫ (J.copyW T hT L a ⊗ₛ 𝟙 a)) =
      Arrow.mk (J.copyW T hT L a ≫ (𝟙 a ⊗ₛ J.copyW T hT L a)) := by
  have h := @ComonObj.comul_assoc _ _ _ a (J.objComon T hT L a)
  simp only [whiskerLeft_eq, whiskerRight_eq, associator_eq, eqToIso.hom] at h
  refine Eq.trans ?_ (congrArg Arrow.mk h).symm
  rw [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
  rfl

theorem discardW_copyW (a : J.Quot T hT) :
    Arrow.mk (J.copyW T hT L a ≫ (J.discardW T hT L a ⊗ₛ 𝟙 a)) = Arrow.mk (𝟙 a) := by
  have h := @ComonObj.counit_comul _ _ _ a (J.objComon T hT L a)
  simp only [whiskerRight_eq, leftUnitor_eq, eqToIso.inv] at h
  exact (congrArg Arrow.mk h).trans (Arrow.mk_eqToHom _)

theorem copyW_discardW (a : J.Quot T hT) :
    Arrow.mk (J.copyW T hT L a ≫ (𝟙 a ⊗ₛ J.discardW T hT L a)) = Arrow.mk (𝟙 a) := by
  have h := @ComonObj.comul_counit _ _ _ a (J.objComon T hT L a)
  simp only [whiskerLeft_eq, rightUnitor_eq, eqToIso.inv] at h
  exact (congrArg Arrow.mk h).trans (Arrow.mk_eqToHom _)

include Lc in
theorem copyW_comm (a : J.Quot T hT) : J.copyW T hT L a ≫ σ_ a a = J.copyW T hT L a := by
  have h := @IsCommComonObj.comul_comm _ _ _ _ a (J.objComon T hT L a)
    (J.wordComm T hT L Lc (FreeMonoid.toList (J.unword T hT a)))
  simp only [braiding_hom_eq] at h
  exact h

theorem copyW_tensor (a b : J.Quot T hT) :
    Arrow.mk (J.copyW T hT L (a * b)) =
      Arrow.mk ((J.copyW T hT L a ⊗ₛ J.copyW T hT L b) ≫
        eqToHom (by simp only [mul_assoc] : a * a * (b * b) = a * (a * b) * b) ≫
        ((𝟙 a ⊗ₛ σ_ a b) ⊗ₛ 𝟙 b)) := by
  have e : (J.objComon T hT L (a * b)).comul =
      ((J.objComon T hT L a).comul ⊗ₘ (J.objComon T hT L b).comul) ≫ tensorμ a a b b := by
    rw [J.objComon_mul T hT L a b]
    exact J.tensorComon_comul T hT a b _ _
  refine (congrArg Arrow.mk e).trans ?_
  simp only [tensorμ, tensorObj_eq, tensorHom_eq, whiskerLeft_eq, whiskerRight_eq,
    associator_eq, eqToIso.hom, eqToIso.inv, braiding_hom_eq, id_tensorHom_eqToHom]
  refine Arrow.mk_comp_congr rfl ?_
  simp only [Arrow.arrow_mk_eqToHom_comp, eqToHom_trans, Arrow.arrow_mk_comp_eqToHom]
  exact (StrictSMC.tensorHom_assoc (𝟙 a) (σ_ a b) (𝟙 b)).symm

theorem discardW_tensor (a b : J.Quot T hT) :
    Arrow.mk (J.discardW T hT L (a * b)) =
      Arrow.mk (J.discardW T hT L a ⊗ₛ J.discardW T hT L b) := by
  have e : (J.objComon T hT L (a * b)).counit =
      ((J.objComon T hT L a).counit ⊗ₘ (J.objComon T hT L b).counit) ≫
        (λ_ (𝟙_ (J.Quot T hT))).hom := by
    rw [J.objComon_mul T hT L a b]
    exact J.tensorComon_counit T hT a b _ _
  refine (congrArg Arrow.mk e).trans ?_
  simp only [tensorHom_eq, leftUnitor_eq, eqToIso.hom, Arrow.arrow_mk_comp_eqToHom]
  rfl

theorem copyW_of (x : S) :
    J.copyW T hT L (J.word T hT (FreeMonoid.of x)) = (L x).comul := by
  change (J.wordComon T hT L [x]).comul = _
  rw [wordComon_singleton]
  rfl

theorem discardW_of (x : S) :
    J.discardW T hT L (J.word T hT (FreeMonoid.of x)) = (L x).counit := by
  change (J.wordComon T hT L [x]).counit = _
  rw [wordComon_singleton]
  rfl

end JoyalStreet

end FreeMarkov
