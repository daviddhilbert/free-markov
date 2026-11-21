/-
Free Markov categories, Stage 5: straight categories, multipliers (Definition 5.1) and the
`m`-fold copy (Remarks 5.2 and 5.7), in an arbitrary strict Markov category.

* `Straight C`: the monoid of objects has no idempotents and no elements of finite order other
  than `1`; `straight_iff` is the reformulation "`w^n ≠ w^m` for all `w ≠ 1` and `n ≠ m`".
* `IsMult W f` (Definition 5.1): `f` is generated from the duplicates, discards, symmetries and
  identities on the members of `W` by composition and monoidal product; a **multiplier on
  `(W, v)`** is a morphism `f : ⊗ W ⟶ v` with `IsMult W (Arrow.mk f)`.
* `copyN w m : w ⟶ w ^ m`, the **`m`-fold copy** (Remark 5.7): `ε_w`, `1_w`, and
  `(copyN w m ⊗ 1_w) ∘ δ_w` for `m + 1` with `m ≥ 1` (the recursion of Remark 5.2).
* `IsMult.exists_preimage`: multipliers in the target of a strict Markov functor that is
  injective on the products of the given objects come from multipliers in the source; this is
  the step "composable morphisms in its image come from composable morphisms" of Remarks 5.2
  and 5.3.

No cited result is used in this file.
-/
module

public import FreeMarkov.Stage4

@[expose] public section

universe v u v₂ u₂

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov

/-! ### Straight categories -/

/-- *Section 5.* "`M` is **straight**; this just means that `M` is strict and the monoid
`(M₀, ⊗, 1)` has no idempotents or elements of finite order other than `1`."  The strictness is
the ambient `StrictMarkov` structure; `Straight C` is the condition on the monoid of objects. -/
structure Straight (C : Type u) [Monoid C] : Prop where
  /-- No idempotents other than `1`. -/
  idem : ∀ w : C, w * w = w → w = 1
  /-- No elements of finite order other than `1`. -/
  torsion : ∀ (w : C) (n : ℕ), 0 < n → w ^ n = 1 → w = 1

section Straight

variable {C : Type u} [Monoid C]

theorem pow_add_eq_of_pow_eq {w : C} {n d : ℕ} (h : w ^ n = w ^ (n + d)) {j : ℕ} (hj : n ≤ j) :
    w ^ (j + d) = w ^ j := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show n + i + d = (n + d) + i by omega, pow_add, ← h, ← pow_add]

theorem pow_add_mul_eq_of_pow_eq {w : C} {n d : ℕ} (h : w ^ n = w ^ (n + d)) {j : ℕ}
    (hj : n ≤ j) : ∀ k, w ^ (j + k * d) = w ^ j
  | 0 => by simp
  | k + 1 => by
    rw [show j + (k + 1) * d = (j + k * d) + d by rw [Nat.succ_mul]; omega,
      pow_add_eq_of_pow_eq h (le_trans hj (Nat.le_add_right _ _)), pow_add_mul_eq_of_pow_eq h hj k]

/-- *Section 5.* "Note that the second condition holds if and only if `w^n ≠ w^m` for all
`w ≠ 1` and all `n ≠ m`; here `w^n` is the monoidal product of `n` copies of `w`; this includes
the empty product `w^0 = 1`." -/
theorem straight_iff : Straight C ↔ ∀ w : C, w ≠ 1 → ∀ n m : ℕ, n ≠ m → w ^ n ≠ w ^ m := by
  constructor
  · intro hS w hw n m hnm hpow
    wlog hlt : n < m generalizing n m
    · exact this m n hnm.symm hpow.symm (lt_of_le_of_ne (not_lt.1 hlt) hnm.symm)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h : w ^ n = w ^ (n + (d + 1)) := by rw [hpow, Nat.add_assoc]
    -- `u = w ^ ((n + 1) (d + 1))` is idempotent
    set N := (n + 1) * (d + 1) with hN
    have hnN : n ≤ N := by rw [hN, Nat.mul_succ]; omega
    have hu : w ^ N * w ^ N = w ^ N := by
      rw [← pow_add]
      exact pow_add_mul_eq_of_pow_eq h hnN (n + 1)
    exact hw (hS.torsion w N (by rw [hN]; exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
      (hS.idem _ hu))
  · intro h
    refine ⟨fun w hw => ?_, fun w n hn hw => ?_⟩
    · by_contra hne
      exact h w hne 2 1 (by omega) (by rw [pow_two, pow_one, hw])
    · by_contra hne
      exact h w hne n 0 (by omega) (by rw [hw, pow_zero])

end Straight

/-! ### Multipliers (Definition 5.1) -/

theorem _root_.CategoryTheory.Arrow.mk_comp_comp_eqToHom {T : Type u} [Category.{v} T]
    {X Y Z Z' : T} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z = Z') :
    Arrow.mk (f ≫ g ≫ eqToHom h) = Arrow.mk (f ≫ g) := by
  subst h; simp

/-- `x` is a monoidal product of members of `W` (with repetitions, in any order). -/
def IsProdOf {C : Type u} [Monoid C] (W : List C) (x : C) : Prop :=
  ∃ l : List C, (∀ y ∈ l, y ∈ W) ∧ l.prod = x

section ProdOf

variable {C : Type u} [Monoid C]

theorem IsProdOf.one (W : List C) : IsProdOf W 1 := ⟨[], by simp, rfl⟩

theorem IsProdOf.of_mem {W : List C} {w : C} (h : w ∈ W) : IsProdOf W w := ⟨[w], by simpa, by simp⟩

theorem IsProdOf.mul {W : List C} {x y : C} (hx : IsProdOf W x) (hy : IsProdOf W y) :
    IsProdOf W (x * y) := by
  obtain ⟨l, hl, rfl⟩ := hx
  obtain ⟨l', hl', rfl⟩ := hy
  exact ⟨l ++ l', fun z hz => (List.mem_append.1 hz).elim (hl z) (hl' z), by simp⟩

end ProdOf

section Mult

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C]

/-- *Definition 5.1.* The morphisms **generated from the duplicates, discards, symmetries, and
identities on** the members of `W` by composition and monoidal product, as elements of the
one-sorted type of arrows.  `idOne` is the empty monoidal product `1_1`. -/
inductive IsMult (W : List C) : Arrow C → Prop
  | copy {w : C} : w ∈ W → IsMult W (Arrow.mk (δ_ w))
  | discard {w : C} : w ∈ W → IsMult W (Arrow.mk (ε_ w))
  | braid {w w' : C} : w ∈ W → w' ∈ W → IsMult W (Arrow.mk (σ_ w w'))
  | id {w : C} : w ∈ W → IsMult W (Arrow.mk (𝟙 w))
  | idOne : IsMult W (Arrow.mk (𝟙 (1 : C)))
  | comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
      IsMult W (Arrow.mk f) → IsMult W (Arrow.mk g) → IsMult W (Arrow.mk (f ≫ g))
  | tensor {a b c d : C} (f : a ⟶ b) (g : c ⟶ d) :
      IsMult W (Arrow.mk f) → IsMult W (Arrow.mk g) → IsMult W (Arrow.mk (f ⊗ₛ g))

/-- *Definition 5.1.* "Let `W = (w_1, …, w_n)` be a sequence of objects and `w = ⊗_i w_i`. A
morphism `w → v` in `M` is called a **multiplier on `(W, v)`** if it is generated from the
duplicates, discards, symmetries, and identities on `w_i`, `1 ≤ i ≤ n`." -/
def IsMultiplier (W : List C) (v : C) (f : W.prod ⟶ v) : Prop := IsMult W (Arrow.mk f)

namespace IsMult

variable {W : List C}

/-- Composition through an identification of the middle objects. -/
theorem comp' {a b b' c : C} (f : a ⟶ b) (h : b = b') (g : b' ⟶ c) (hf : IsMult W (Arrow.mk f))
    (hg : IsMult W (Arrow.mk g)) : IsMult W (Arrow.mk (f ≫ eqToHom h ≫ g)) := by
  subst h
  simpa using IsMult.comp f g hf hg

theorem of_eqToHom_comp {a a' b : C} (h : a = a') (f : a' ⟶ b) (hf : IsMult W (Arrow.mk f)) :
    IsMult W (Arrow.mk (eqToHom h ≫ f)) := by
  subst h
  simpa using hf

theorem comp_eqToHom {a b b' : C} (f : a ⟶ b) (h : b = b') (hf : IsMult W (Arrow.mk f)) :
    IsMult W (Arrow.mk (f ≫ eqToHom h)) := by
  subst h
  simpa using hf

/-- The source and target of a generated morphism are products of members of `W`. -/
theorem mem_closure {f : Arrow C} (hf : IsMult W f) :
    IsProdOf W f.left ∧ IsProdOf W f.right := by
  induction hf with
  | copy hw => exact ⟨.of_mem hw, (IsProdOf.of_mem hw).mul (.of_mem hw)⟩
  | discard hw => exact ⟨.of_mem hw, .one W⟩
  | braid hw hw' => exact ⟨(IsProdOf.of_mem hw).mul (.of_mem hw'), (IsProdOf.of_mem hw').mul (.of_mem hw)⟩
  | id hw => exact ⟨.of_mem hw, .of_mem hw⟩
  | idOne => exact ⟨.one W, .one W⟩
  | comp f g _ _ h₁ h₂ => exact ⟨h₁.1, h₂.2⟩
  | tensor f g _ _ h₁ h₂ => exact ⟨h₁.1.mul h₂.1, h₁.2.mul h₂.2⟩

theorem mono {W W' : List C} (hW : ∀ w ∈ W, w ∈ W') {f : Arrow C} (hf : IsMult W f) :
    IsMult W' f := by
  induction hf with
  | copy hw => exact .copy (hW _ hw)
  | discard hw => exact .discard (hW _ hw)
  | braid hw hw' => exact .braid (hW _ hw) (hW _ hw')
  | id hw => exact .id (hW _ hw)
  | idOne => exact .idOne
  | comp f g _ _ h₁ h₂ => exact .comp f g h₁ h₂
  | tensor f g _ _ h₁ h₂ => exact .tensor f g h₁ h₂

end IsMult

/-! ### The `m`-fold copy (Remarks 5.2 and 5.7) -/

/-- *Remarks 5.2 and 5.7.* The **`m`-fold copy** on `w`: `ε_w` for `m = 0`, `1_w` for `m = 1`,
and `(copyN w m ⊗ 1_w) ∘ δ_w : w → w^m ⊗ w = w^{m+1}` for `m + 1` with `m ≥ 1`
("the recursion in Remark 5.2 still defines a multiplier `w → w^m`"). -/
def copyN (w : C) : (m : ℕ) → (w ⟶ w ^ m)
  | 0 => ε_ w ≫ eqToHom (pow_zero w).symm
  | 1 => eqToHom (pow_one w).symm
  | m + 2 => δ_ w ≫ (copyN w (m + 1) ⊗ₛ 𝟙 w) ≫ eqToHom (pow_succ w (m + 1)).symm

theorem copyN_zero (w : C) : Arrow.mk (copyN w 0) = Arrow.mk (ε_ w) := by
  simp [copyN]

theorem copyN_one (w : C) : Arrow.mk (copyN w 1) = Arrow.mk (𝟙 w) := by
  simp [copyN]

theorem copyN_two (w : C) : Arrow.mk (copyN w 2) = Arrow.mk (δ_ w) := by
  have : Arrow.mk (copyN w 1 ⊗ₛ 𝟙 w) = Arrow.mk (𝟙 w ⊗ₛ 𝟙 w) :=
    mk_tensorHom_congr (copyN_one w) rfl
  rw [tensorHom_id] at this
  change Arrow.mk (δ_ w ≫ (copyN w 1 ⊗ₛ 𝟙 w) ≫ eqToHom _) = _
  rw [Arrow.mk_comp_comp_eqToHom, Arrow.mk_comp_congr rfl this]
  simp

/-- *Remark 5.2.* `ι_{w → w^{m+1}} = (ι_{w → w^m} ⊗ 1_w) ∘ δ_w` for `m ≥ 1`. -/
theorem copyN_succ (w : C) {m : ℕ} (hm : 1 ≤ m) :
    Arrow.mk (copyN w (m + 1)) = Arrow.mk (δ_ w ≫ (copyN w m ⊗ₛ 𝟙 w)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [copyN]
  rw [Arrow.mk_comp_comp_eqToHom]

/-- The `m`-fold copy is a multiplier on `(w, w^m)`. -/
theorem isMult_copyN (w : C) : ∀ m, IsMult [w] (Arrow.mk (copyN w m))
  | 0 => by rw [copyN_zero]; exact .discard (by simp)
  | 1 => by rw [copyN_one]; exact .id (by simp)
  | m + 2 => by
    simp only [copyN]
    rw [Arrow.mk_comp_comp_eqToHom]
    exact .comp _ _ (.copy (by simp)) (.tensor _ _ (isMult_copyN w (m + 1)) (.id (by simp)))

theorem isMultiplier_copyN (w : C) (m : ℕ) :
    IsMultiplier [w] (w ^ m) (eqToHom (by simp) ≫ copyN w m) := by
  unfold IsMultiplier
  exact IsMult.of_eqToHom_comp _ _ (isMult_copyN w m)

end Mult

/-! ### Strict Markov functors and multipliers -/

section Functor

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C]
  {D : Type u₂} [Monoid D] [Category.{v₂} D] [StrictMarkov D]

theorem StrictFunctor.obj_pow (F : StrictFunctor C D) (w : C) : ∀ m : ℕ, F.obj (w ^ m) = F.obj w ^ m
  | 0 => by simp [F.obj_one]
  | m + 1 => by rw [pow_succ, F.obj_mul, StrictFunctor.obj_pow F w m, pow_succ]

/-- *Remark 5.7.* "A strict Markov functor sends the `m`-fold copy on `w` to the `m`-fold copy on
the image of `w`." -/
theorem StrictMarkovFunctor.map_copyN (F : StrictMarkovFunctor C D) (w : C) :
    ∀ m, Arrow.mk (F.map (copyN w m)) = Arrow.mk (copyN (F.obj w) m)
  | 0 => by
    rw [copyN_zero]
    simp only [copyN, Functor.map_comp, eqToHom_map]
    rw [Arrow.arrow_mk_comp_eqToHom, F.map_discard]
  | 1 => by
    rw [copyN_one]
    simp [copyN, eqToHom_map]
  | m + 2 => by
    simp only [copyN, Functor.map_comp, eqToHom_map]
    rw [Arrow.mk_comp_comp_eqToHom, Arrow.mk_comp_comp_eqToHom]
    refine Arrow.mk_comp_congr (F.map_copy w) ?_
    refine (F.map_tensorHom _ _).trans (mk_tensorHom_congr (StrictMarkovFunctor.map_copyN F w (m + 1)) ?_)
    simp

/-- *Remarks 5.2 and 5.3.* If a strict Markov functor `F : C → D` is injective on the products
of the members of `W`, then every morphism of `D` generated from the duplicates, discards,
symmetries and identities on the `F(w)`, `w ∈ W`, is the image of a morphism of `C` generated
from those on the `w ∈ W`: "composable morphisms in its image come from composable morphisms". -/
theorem IsMult.exists_preimage (F : StrictMarkovFunctor C D) (W : List C)
    (hinj : ∀ x y, IsProdOf W x → IsProdOf W y → F.obj x = F.obj y → x = y)
    {f : Arrow D} (hf : IsMult (W.map F.obj) f) :
    ∃ g : Arrow C, IsMult W g ∧ Arrow.mk (F.map g.hom) = f := by
  induction hf with
  | @copy w hw =>
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
    exact ⟨Arrow.mk (δ_ w'), .copy hw', F.map_copy w'⟩
  | @discard w hw =>
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
    exact ⟨Arrow.mk (ε_ w'), .discard hw', F.map_discard w'⟩
  | @braid w₁ w₂ hw₁ hw₂ =>
    obtain ⟨w₁', hw₁', rfl⟩ := List.mem_map.1 hw₁
    obtain ⟨w₂', hw₂', rfl⟩ := List.mem_map.1 hw₂
    exact ⟨Arrow.mk (σ_ w₁' w₂'), .braid hw₁' hw₂', F.map_braid w₁' w₂'⟩
  | @id w hw =>
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
    exact ⟨Arrow.mk (𝟙 w'), .id hw', by simp⟩
  | idOne => exact ⟨Arrow.mk (𝟙 1), .idOne, by simpa using Arrow.mk_id_congr F.obj_one⟩
  | comp f g _ _ ih₁ ih₂ =>
    obtain ⟨g₁, hg₁, e₁⟩ := ih₁
    obtain ⟨g₂, hg₂, e₂⟩ := ih₂
    have hb : g₁.right = g₂.left := by
      refine hinj _ _ hg₁.mem_closure.2 hg₂.mem_closure.1 ?_
      exact (Arrow.right_eq_of_mk_eq e₁).trans (Arrow.left_eq_of_mk_eq e₂).symm
    refine ⟨Arrow.mk (g₁.hom ≫ eqToHom hb ≫ g₂.hom), IsMult.comp' _ _ _ hg₁ hg₂, ?_⟩
    change Arrow.mk (F.map (g₁.hom ≫ eqToHom hb ≫ g₂.hom)) = _
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map]
    refine Arrow.mk_comp_congr e₁ ?_
    simpa using e₂
  | tensor f g _ _ ih₁ ih₂ =>
    obtain ⟨g₁, hg₁, e₁⟩ := ih₁
    obtain ⟨g₂, hg₂, e₂⟩ := ih₂
    exact ⟨Arrow.mk (g₁.hom ⊗ₛ g₂.hom), .tensor _ _ hg₁ hg₂,
      (F.map_tensorHom _ _).trans (mk_tensorHom_congr e₁ e₂)⟩

end Functor

end FreeMarkov
