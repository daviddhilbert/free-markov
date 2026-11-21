/-
Free Markov categories, Stage 2: `S_T` is a monoidal congruence (after Definition 3.4).

"It is also easy to see that if `[Γ] ⇝_T [Γ']` and `[Υ] ⇝_T [Υ']` then
`[Υ] ⊗ [Γ] ⇝_T [Υ'] ⊗ [Γ']` and `[Υ] ∘ [Γ] ⇝_T [Υ'] ∘ [Γ']` if the compositions are
defined."

The proof uses the class form of Lemma 3.3: a `T`-surgery is a pair
`h ∘ [Ω^♯] ∘ g`, `h ∘ [Λ^♯] ∘ g`; composing with `[Υ]` changes `g` or `h`
(associativity), and tensoring with `[Υ]` replaces `g`, `Ω^♯`, `h` by `g ⊗ [Υ]`,
`Ω^♯ ⊗ 1`, `h ⊗ 1` (interchange law), where `Ω^♯ ⊗ 1 = Ω ⊎ (R ⊎ cod Υ)`.  Associativity and
the interchange law are those of `F_s(G)`, so the cited result C1 (`JoyalStreet G`) is a
hypothesis here.
-/
module

public import FreeMarkov.Stage2.Templates

@[expose] public section

universe u w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace FreeMarkov

open Relation

/-! ### Orderings of `K ⊎ (R ⊕ R')` -/

namespace Enumeration

variable {E : Type u₁} {E' : Type u₂} {P : E → Prop} {P' : E' → Prop}

/-- The ordering of a sum: first `o`, then `o'`. -/
def sumAll (o : Enumeration P) (o' : Enumeration P') :
    Enumeration fun _ : {e // P e} ⊕ {e' // P' e'} => True where
  list := o.sub.map .inl ++ o'.sub.map .inr
  nodup := List.nodup_append.2 ⟨o.nodup_sub.map Sum.inl_injective,
    o'.nodup_sub.map Sum.inr_injective, by simp⟩
  mem_iff x := iff_of_true (by rcases x with x | x <;> simp [mem_sub]) trivial

theorem mapEquiv_list' {E'' : Type u₃} {P'' : E'' → Prop} (o : Enumeration P'')
    (σ : {e // P'' e} ≃ {e' // P' e'}) (f : E'' → E') (hf : ∀ x, (σ x).1 = f x.1) :
    (o.mapEquiv σ).list = o.list.map f := by
  rw [mapEquiv_list, ← o.sub_map_val, List.map_map]
  exact List.map_congr_left fun x _ => hf x

/-- `{_x : α // True} ≃ {_x : β // True}` from `α ≃ β`. -/
def trueEquiv {α : Type u₃} {β : Type u₄} (e : α ≃ β) : {_x : α // True} ≃ {_x : β // True} :=
  e.subtypeEquiv fun _ => Iff.rfl

theorem sumAll_mapEquiv {E'' : Type u₃} {P'' : E'' → Prop} (o : Enumeration P)
    (σ : {e // P e} ≃ {e'' // P'' e''}) (o' : Enumeration P') :
    sumAll (o.mapEquiv σ) o' = (sumAll o o').mapEquiv (trueEquiv (Equiv.sumCongr σ (Equiv.refl _))) :=
  ext_list (by
    rw [mapEquiv_list' _ _ (Sum.map σ id) (fun _ => rfl)]
    simp [sumAll, sub_mapEquiv, List.map_map, Function.comp_def])

theorem sumAll_mapEquiv' {E'' : Type u₃} {P'' : E'' → Prop} (o : Enumeration P)
    (o' : Enumeration P') (σ : {e // P' e} ≃ {e'' // P'' e''}) :
    sumAll o (o'.mapEquiv σ) = (sumAll o o').mapEquiv (trueEquiv (Equiv.sumCongr (Equiv.refl _) σ)) :=
  ext_list (by
    rw [mapEquiv_list' _ _ (Sum.map id σ) (fun _ => rfl)]
    simp [sumAll, sub_mapEquiv, List.map_map, Function.comp_def])

/-- The ordering `0, 1, …, n - 1` of `Fin n`. -/
def finEnum (n : ℕ) : Enumeration fun _ : Fin n => True :=
  ⟨List.finRange n, List.nodup_finRange n, fun _ => iff_of_true (List.mem_finRange _) trivial⟩

end Enumeration

namespace PGraph

variable {N : Type u₁} {E : Type u₂} (K : PGraph N E) (R : Type u₃) (R' : Type u₄)

/-- `dom(K ⊎ R) ⊎ R' = dom(K ⊎ (R ⊕ R'))`. -/
def appendDom : {_x : {k // (K.addLoose R).IsDom k} ⊕ {_r : R' // True} // True} ≃
    {k // (K.addLoose (R ⊕ R')).IsDom k} where
  toFun x := match x with
    | ⟨.inl ⟨.inl d, h⟩, _⟩ => ⟨.inl d, h⟩
    | ⟨.inl ⟨.inr ρ, _⟩, _⟩ => ⟨.inr (.inl ρ), rfl⟩
    | ⟨.inr ⟨ρ, _⟩, _⟩ => ⟨.inr (.inr ρ), rfl⟩
  invFun k := match k with
    | ⟨.inl d, h⟩ => ⟨.inl ⟨.inl d, h⟩, trivial⟩
    | ⟨.inr (.inl ρ), _⟩ => ⟨.inl ⟨.inr ρ, rfl⟩, trivial⟩
    | ⟨.inr (.inr ρ), _⟩ => ⟨.inr ⟨ρ, trivial⟩, trivial⟩
  left_inv := by rintro ⟨(⟨_ | _, _⟩ | ⟨_, _⟩), _⟩ <;> rfl
  right_inv := by rintro ⟨_ | _ | _, _⟩ <;> rfl

/-- `cod(K ⊎ R) ⊎ R' = cod(K ⊎ (R ⊕ R'))`. -/
def appendCod : {_x : {k // (K.addLoose R).IsCod k} ⊕ {_r : R' // True} // True} ≃
    {k // (K.addLoose (R ⊕ R')).IsCod k} where
  toFun x := match x with
    | ⟨.inl ⟨.inl d, h⟩, _⟩ => ⟨.inl d, h⟩
    | ⟨.inl ⟨.inr ρ, _⟩, _⟩ => ⟨.inr (.inl ρ), rfl⟩
    | ⟨.inr ⟨ρ, _⟩, _⟩ => ⟨.inr (.inr ρ), rfl⟩
  invFun k := match k with
    | ⟨.inl d, h⟩ => ⟨.inl ⟨.inl d, h⟩, trivial⟩
    | ⟨.inr (.inl ρ), _⟩ => ⟨.inl ⟨.inr ρ, rfl⟩, trivial⟩
    | ⟨.inr (.inr ρ), _⟩ => ⟨.inr ⟨ρ, trivial⟩, trivial⟩
  left_inv := by rintro ⟨(⟨_ | _, _⟩ | ⟨_, _⟩), _⟩ <;> rfl
  right_inv := by rintro ⟨_ | _ | _, _⟩ <;> rfl

/-- `R' ⊎ dom(K ⊎ R) = dom(K ⊎ (R' ⊕ R))`. -/
def prependDom : {_x : {_r : R' // True} ⊕ {k // (K.addLoose R).IsDom k} // True} ≃
    {k // (K.addLoose (R' ⊕ R)).IsDom k} where
  toFun x := match x with
    | ⟨.inr ⟨.inl d, h⟩, _⟩ => ⟨.inl d, h⟩
    | ⟨.inr ⟨.inr ρ, _⟩, _⟩ => ⟨.inr (.inr ρ), rfl⟩
    | ⟨.inl ⟨ρ, _⟩, _⟩ => ⟨.inr (.inl ρ), rfl⟩
  invFun k := match k with
    | ⟨.inl d, h⟩ => ⟨.inr ⟨.inl d, h⟩, trivial⟩
    | ⟨.inr (.inr ρ), _⟩ => ⟨.inr ⟨.inr ρ, rfl⟩, trivial⟩
    | ⟨.inr (.inl ρ), _⟩ => ⟨.inl ⟨ρ, trivial⟩, trivial⟩
  left_inv := by rintro ⟨(⟨_, _⟩ | ⟨_ | _, _⟩), _⟩ <;> rfl
  right_inv := by rintro ⟨_ | _ | _, _⟩ <;> rfl

/-- `R' ⊎ cod(K ⊎ R) = cod(K ⊎ (R' ⊕ R))`. -/
def prependCod : {_x : {_r : R' // True} ⊕ {k // (K.addLoose R).IsCod k} // True} ≃
    {k // (K.addLoose (R' ⊕ R)).IsCod k} where
  toFun x := match x with
    | ⟨.inr ⟨.inl d, h⟩, _⟩ => ⟨.inl d, h⟩
    | ⟨.inr ⟨.inr ρ, _⟩, _⟩ => ⟨.inr (.inr ρ), rfl⟩
    | ⟨.inl ⟨ρ, _⟩, _⟩ => ⟨.inr (.inl ρ), rfl⟩
  invFun k := match k with
    | ⟨.inl d, h⟩ => ⟨.inr ⟨.inl d, h⟩, trivial⟩
    | ⟨.inr (.inr ρ), _⟩ => ⟨.inr ⟨.inr ρ, rfl⟩, trivial⟩
    | ⟨.inr (.inl ρ), _⟩ => ⟨.inl ⟨ρ, trivial⟩, trivial⟩
  left_inv := by rintro ⟨(⟨_, _⟩ | ⟨_ | _, _⟩), _⟩ <;> rfl
  right_inv := by rintro ⟨_ | _ | _, _⟩ <;> rfl

/-- `dom(K) ⊎ R = dom(K ⊎ R)`. -/
def plusDom : {_x : {e // K.IsDom e} ⊕ {_r : R // True} // True} ≃ {k // (K.addLoose R).IsDom k} where
  toFun x := match x with
    | ⟨.inl ⟨d, h⟩, _⟩ => ⟨.inl d, h⟩
    | ⟨.inr ⟨ρ, _⟩, _⟩ => ⟨.inr ρ, rfl⟩
  invFun k := match k with
    | ⟨.inl d, h⟩ => ⟨.inl ⟨d, h⟩, trivial⟩
    | ⟨.inr ρ, _⟩ => ⟨.inr ⟨ρ, trivial⟩, trivial⟩
  left_inv := by rintro ⟨(⟨_, _⟩ | ⟨_, _⟩), _⟩ <;> rfl
  right_inv := by rintro ⟨_ | _, _⟩ <;> rfl

/-- `cod(K) ⊎ R = cod(K ⊎ R)`. -/
def plusCod : {_x : {e // K.IsCod e} ⊕ {_r : R // True} // True} ≃ {k // (K.addLoose R).IsCod k} where
  toFun x := match x with
    | ⟨.inl ⟨d, h⟩, _⟩ => ⟨.inl d, h⟩
    | ⟨.inr ⟨ρ, _⟩, _⟩ => ⟨.inr ρ, rfl⟩
  invFun k := match k with
    | ⟨.inl d, h⟩ => ⟨.inl ⟨d, h⟩, trivial⟩
    | ⟨.inr ρ, _⟩ => ⟨.inr ⟨ρ, trivial⟩, trivial⟩
  left_inv := by rintro ⟨(⟨_, _⟩ | ⟨_, _⟩), _⟩ <;> rfl
  right_inv := by rintro ⟨_ | _, _⟩ <;> rfl

variable {K R R'} {N' : Type u₅} {E' : Type u₆} {Ω : PGraph N' E'}

theorem appendDom_liftDom (α : {e // K.IsDom e} ≃ {e // Ω.IsDom e}) :
    (Enumeration.trueEquiv (Equiv.sumCongr (liftDom α R).symm (Equiv.refl _))).trans
      (appendDom K R R') = (appendDom Ω R R').trans (liftDom α (R ⊕ R')).symm := by
  rw [liftDom_symm, liftDom_symm]
  ext ⟨(⟨d | ρ, h⟩ | ⟨ρ, h⟩), _⟩ <;> rfl

theorem appendCod_liftCod (β : {e // K.IsCod e} ≃ {e // Ω.IsCod e}) :
    (Enumeration.trueEquiv (Equiv.sumCongr (liftCod β R).symm (Equiv.refl _))).trans
      (appendCod K R R') = (appendCod Ω R R').trans (liftCod β (R ⊕ R')).symm := by
  rw [liftCod_symm, liftCod_symm]
  ext ⟨(⟨d | ρ, h⟩ | ⟨ρ, h⟩), _⟩ <;> rfl

theorem prependDom_liftDom (α : {e // K.IsDom e} ≃ {e // Ω.IsDom e}) :
    (Enumeration.trueEquiv (Equiv.sumCongr (Equiv.refl _) (liftDom α R).symm)).trans
      (prependDom K R R') = (prependDom Ω R R').trans (liftDom α (R' ⊕ R)).symm := by
  rw [liftDom_symm, liftDom_symm]
  ext ⟨(⟨ρ, h⟩ | ⟨d | ρ, h⟩), _⟩ <;> rfl

theorem prependCod_liftCod (β : {e // K.IsCod e} ≃ {e // Ω.IsCod e}) :
    (Enumeration.trueEquiv (Equiv.sumCongr (Equiv.refl _) (liftCod β R).symm)).trans
      (prependCod K R R') = (prependCod Ω R R').trans (liftCod β (R' ⊕ R)).symm := by
  rw [liftCod_symm, liftCod_symm]
  ext ⟨(⟨ρ, h⟩ | ⟨d | ρ, h⟩), _⟩ <;> rfl

theorem plusDom_liftDom (α : {e // K.IsDom e} ≃ {e // Ω.IsDom e}) :
    (Enumeration.trueEquiv (Equiv.sumCongr α.symm (Equiv.refl _))).trans (plusDom K R) =
      (plusDom Ω R).trans (liftDom α R).symm := by
  rw [liftDom_symm]
  ext ⟨(⟨d, h⟩ | ⟨ρ, h⟩), _⟩ <;> rfl

theorem plusCod_liftCod (β : {e // K.IsCod e} ≃ {e // Ω.IsCod e}) :
    (Enumeration.trueEquiv (Equiv.sumCongr β.symm (Equiv.refl _))).trans (plusCod K R) =
      (plusCod Ω R).trans (liftCod β R).symm := by
  rw [liftCod_symm]
  ext ⟨(⟨d, h⟩ | ⟨ρ, h⟩), _⟩ <;> rfl

end PGraph

namespace Enumeration

variable {N : Type u₁} {E : Type u₂} {K : PGraph N E} {R : Type u₃} {R' : Type u₄}

/-- An ordering of `dom(K ⊎ R)` followed by an ordering of `R'`. -/
def appendR (o : Enumeration (K.addLoose R).IsDom) (ρ : Enumeration fun _ : R' => True) :
    Enumeration (K.addLoose (R ⊕ R')).IsDom :=
  (sumAll o ρ).mapEquiv (K.appendDom R R')

/-- An ordering of `cod(K ⊎ R)` followed by an ordering of `R'`. -/
def appendRc (o : Enumeration (K.addLoose R).IsCod) (ρ : Enumeration fun _ : R' => True) :
    Enumeration (K.addLoose (R ⊕ R')).IsCod :=
  (sumAll o ρ).mapEquiv (K.appendCod R R')

/-- An ordering of `R'` followed by an ordering of `dom(K ⊎ R)`. -/
def prependR (ρ : Enumeration fun _ : R' => True) (o : Enumeration (K.addLoose R).IsDom) :
    Enumeration (K.addLoose (R' ⊕ R)).IsDom :=
  (sumAll ρ o).mapEquiv (K.prependDom R R')

/-- An ordering of `R'` followed by an ordering of `cod(K ⊎ R)`. -/
def prependRc (ρ : Enumeration fun _ : R' => True) (o : Enumeration (K.addLoose R).IsCod) :
    Enumeration (K.addLoose (R' ⊕ R)).IsCod :=
  (sumAll ρ o).mapEquiv (K.prependCod R R')

/-- An ordering of `dom(K)` followed by an ordering of `R`. -/
def plus (o : Enumeration K.IsDom) (ρ : Enumeration fun _ : R => True) :
    Enumeration (K.addLoose R).IsDom :=
  (sumAll o ρ).mapEquiv (K.plusDom R)

/-- An ordering of `cod(K)` followed by an ordering of `R`. -/
def plusc (o : Enumeration K.IsCod) (ρ : Enumeration fun _ : R => True) :
    Enumeration (K.addLoose R).IsCod :=
  (sumAll o ρ).mapEquiv (K.plusCod R)

theorem appendR_list (o : Enumeration (K.addLoose R).IsDom) (ρ : Enumeration fun _ : R' => True) :
    (appendR o ρ).list = o.list.map (Sum.map id .inl) ++ ρ.list.map (.inr ∘ .inr) := by
  rw [appendR, mapEquiv_list' _ _ (Sum.elim (fun k => Sum.map id .inl k.1) fun r => .inr (.inr r.1))
    (by rintro ⟨(⟨d | ρ, h⟩ | ⟨ρ, h⟩), _⟩ <;> rfl)]
  simp [sumAll, ← o.sub_map_val, ← ρ.sub_map_val, List.map_map, Function.comp_def]

theorem appendRc_list (o : Enumeration (K.addLoose R).IsCod) (ρ : Enumeration fun _ : R' => True) :
    (appendRc o ρ).list = o.list.map (Sum.map id .inl) ++ ρ.list.map (.inr ∘ .inr) := by
  rw [appendRc, mapEquiv_list' _ _ (Sum.elim (fun k => Sum.map id .inl k.1) fun r => .inr (.inr r.1))
    (by rintro ⟨(⟨d | ρ, h⟩ | ⟨ρ, h⟩), _⟩ <;> rfl)]
  simp [sumAll, ← o.sub_map_val, ← ρ.sub_map_val, List.map_map, Function.comp_def]

theorem prependR_list (ρ : Enumeration fun _ : R' => True) (o : Enumeration (K.addLoose R).IsDom) :
    (prependR ρ o).list = ρ.list.map (.inr ∘ .inl) ++ o.list.map (Sum.map id .inr) := by
  rw [prependR, mapEquiv_list' _ _ (Sum.elim (fun r => .inr (.inl r.1)) fun k => Sum.map id .inr k.1)
    (by rintro ⟨(⟨ρ, h⟩ | ⟨d | ρ, h⟩), _⟩ <;> rfl)]
  simp [sumAll, ← o.sub_map_val, ← ρ.sub_map_val, List.map_map, Function.comp_def]

theorem prependRc_list (ρ : Enumeration fun _ : R' => True) (o : Enumeration (K.addLoose R).IsCod) :
    (prependRc ρ o).list = ρ.list.map (.inr ∘ .inl) ++ o.list.map (Sum.map id .inr) := by
  rw [prependRc, mapEquiv_list' _ _ (Sum.elim (fun r => .inr (.inl r.1)) fun k => Sum.map id .inr k.1)
    (by rintro ⟨(⟨ρ, h⟩ | ⟨d | ρ, h⟩), _⟩ <;> rfl)]
  simp [sumAll, ← o.sub_map_val, ← ρ.sub_map_val, List.map_map, Function.comp_def]

theorem plus_list (o : Enumeration K.IsDom) (ρ : Enumeration fun _ : R => True) :
    (plus o ρ).list = o.list.map .inl ++ ρ.list.map .inr := by
  rw [plus, mapEquiv_list' _ _ (Sum.elim (fun k => .inl k.1) fun r => .inr r.1)
    (by rintro ⟨(⟨d, h⟩ | ⟨ρ, h⟩), _⟩ <;> rfl)]
  simp [sumAll, ← o.sub_map_val, ← ρ.sub_map_val, List.map_map, Function.comp_def]

theorem plusc_list (o : Enumeration K.IsCod) (ρ : Enumeration fun _ : R => True) :
    (plusc o ρ).list = o.list.map .inl ++ ρ.list.map .inr := by
  rw [plusc, mapEquiv_list' _ _ (Sum.elim (fun k => .inl k.1) fun r => .inr r.1)
    (by rintro ⟨(⟨d, h⟩ | ⟨ρ, h⟩), _⟩ <;> rfl)]
  simp [sumAll, ← o.sub_map_val, ← ρ.sub_map_val, List.map_map, Function.comp_def]

variable {N' : Type u₅} {E' : Type u₆} {Ω : PGraph N' E'}

theorem appendR_liftDom (α : {e // K.IsDom e} ≃ {e // Ω.IsDom e})
    (o : Enumeration (Ω.addLoose R).IsDom) (ρ : Enumeration fun _ : R' => True) :
    appendR (o.mapEquiv (PGraph.liftDom α R).symm) ρ =
      (appendR o ρ).mapEquiv (PGraph.liftDom α (R ⊕ R')).symm := by
  rw [appendR, appendR, sumAll_mapEquiv, mapEquiv_mapEquiv, mapEquiv_mapEquiv,
    PGraph.appendDom_liftDom]

theorem appendRc_liftCod (β : {e // K.IsCod e} ≃ {e // Ω.IsCod e})
    (o : Enumeration (Ω.addLoose R).IsCod) (ρ : Enumeration fun _ : R' => True) :
    appendRc (o.mapEquiv (PGraph.liftCod β R).symm) ρ =
      (appendRc o ρ).mapEquiv (PGraph.liftCod β (R ⊕ R')).symm := by
  rw [appendRc, appendRc, sumAll_mapEquiv, mapEquiv_mapEquiv, mapEquiv_mapEquiv,
    PGraph.appendCod_liftCod]

theorem prependR_liftDom (α : {e // K.IsDom e} ≃ {e // Ω.IsDom e})
    (ρ : Enumeration fun _ : R' => True) (o : Enumeration (Ω.addLoose R).IsDom) :
    prependR ρ (o.mapEquiv (PGraph.liftDom α R).symm) =
      (prependR ρ o).mapEquiv (PGraph.liftDom α (R' ⊕ R)).symm := by
  rw [prependR, prependR, sumAll_mapEquiv', mapEquiv_mapEquiv, mapEquiv_mapEquiv,
    PGraph.prependDom_liftDom]

theorem prependRc_liftCod (β : {e // K.IsCod e} ≃ {e // Ω.IsCod e})
    (ρ : Enumeration fun _ : R' => True) (o : Enumeration (Ω.addLoose R).IsCod) :
    prependRc ρ (o.mapEquiv (PGraph.liftCod β R).symm) =
      (prependRc ρ o).mapEquiv (PGraph.liftCod β (R' ⊕ R)).symm := by
  rw [prependRc, prependRc, sumAll_mapEquiv', mapEquiv_mapEquiv, mapEquiv_mapEquiv,
    PGraph.prependCod_liftCod]

theorem plus_liftDom (α : {e // K.IsDom e} ≃ {e // Ω.IsDom e}) (o : Enumeration Ω.IsDom)
    (ρ : Enumeration fun _ : R => True) :
    plus (o.mapEquiv α.symm) ρ = (plus o ρ).mapEquiv (PGraph.liftDom α R).symm := by
  rw [plus, plus, sumAll_mapEquiv, mapEquiv_mapEquiv, mapEquiv_mapEquiv, PGraph.plusDom_liftDom]

theorem plusc_liftCod (β : {e // K.IsCod e} ≃ {e // Ω.IsCod e}) (o : Enumeration Ω.IsCod)
    (ρ : Enumeration fun _ : R => True) :
    plusc (o.mapEquiv β.symm) ρ = (plusc o ρ).mapEquiv (PGraph.liftCod β R).symm := by
  rw [plusc, plusc, sumAll_mapEquiv, mapEquiv_mapEquiv, mapEquiv_mapEquiv, PGraph.plusCod_liftCod]

end Enumeration

/-! ### `Ω^♯ ⊗ 1 = Ω ⊎ (R ⊕ cod)` and `1 ⊗ Ω^♯ = Ω ⊎ (cod ⊕ R)` -/

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {NK : Type u₁} {EK : Type u₂}
  (K : PDiagram G NK EK) {R : Type u₃} (r : R → S)
  (dK : Enumeration (K.toPGraph.addLoose R).IsDom) (cK : Enumeration (K.toPGraph.addLoose R).IsCod)

theorem sumAssoc_comp_inl {α : Type u₄} {β : Type u₅} {γ : Type u₆} :
    (Equiv.sumAssoc α β γ) ∘ Sum.inl = Sum.map id .inl := by
  funext x; rcases x with x | x <;> rfl

theorem sumAssoc_comp_inr {α : Type u₄} {β : Type u₅} {γ : Type u₆} :
    (Equiv.sumAssoc α β γ) ∘ Sum.inr = Sum.inr ∘ Sum.inr := rfl

/-- `α ⊕ (β ⊕ γ) ≃ β ⊕ (α ⊕ γ)`. -/
def sumSwapAssoc (α : Type u₄) (β : Type u₅) (γ : Type u₆) : α ⊕ (β ⊕ γ) ≃ β ⊕ (α ⊕ γ) :=
  (Equiv.sumAssoc α β γ).symm.trans ((Equiv.sumCongr (Equiv.sumComm α β) (Equiv.refl γ)).trans
    (Equiv.sumAssoc β α γ))

/-- `[Ω^♯] ⊗ 1_b = [Ω ⊎ (R ⊕ b)]`, with the orderings of `R` and of the strands of `b`
appended. -/
noncomputable def tensorIdIso (b : FreeMonoid S) :
    (((K.addLoose r).anchor dK cK).tensor (idD G b)).Iso
      ((K.addLoose (Sum.elim r (letters b))).anchor (dK.appendR (Enumeration.finEnum _))
        (cK.appendRc (Enumeration.finEnum _))) :=
  Diagram.Iso.ofProj (Sum.elim id fun e => e.elim) (Equiv.sumAssoc _ _ _) id id
    (by rintro (x | x) (y | y) h; exacts [congrArg Sum.inl h, y.elim, x.elim, x.elim])
    Function.injective_id (Equiv.injective _) Function.injective_id
    (fun t => ⟨fun _ => ⟨t, rfl⟩, fun _ => ⟨.inl t, rfl⟩⟩)
    (fun t => ⟨fun _ => ⟨t, rfl⟩, fun _ => ⟨(Equiv.sumAssoc _ _ _).symm t, by simp⟩⟩)
    (by
      rintro (z | e) n' rfl
      · simp [Diagram.tensor, AGraph.tensor, PGraph.tensor, PDiagram.anchor, AGraph.ofPGraph,
          List.map_map, Function.comp_def]
      · exact e.elim)
    (by
      rintro (z | e) n' rfl
      · simp [Diagram.tensor, AGraph.tensor, PGraph.tensor, PDiagram.anchor, AGraph.ofPGraph,
          List.map_map, Function.comp_def]
      · exact e.elim)
    (by
      change ((dK.list.map Sum.inl ++ (List.finRange _).map Sum.inr)).map _ =
        (dK.appendR (Enumeration.finEnum _)).list.map id
      rw [Enumeration.appendR_list, List.map_append, List.map_map, List.map_map, List.map_id,
        sumAssoc_comp_inl, sumAssoc_comp_inr]
      rfl)
    (by
      change ((cK.list.map Sum.inl ++ (List.finRange _).map Sum.inr)).map _ =
        (cK.appendRc (Enumeration.finEnum _)).list.map id
      rw [Enumeration.appendRc_list, List.map_append, List.map_map, List.map_map, List.map_id,
        sumAssoc_comp_inl, sumAssoc_comp_inr]
      rfl)
    (by rintro ((d | ρ) | i) e' rfl <;> rfl)
    (by rintro (z | e) n' rfl; exacts [rfl, e.elim])

theorem sumSwapAssoc_comp_inr {α : Type u₄} {β : Type u₅} {γ : Type u₆} :
    (sumSwapAssoc α β γ) ∘ Sum.inr = Sum.map id .inr := by
  funext x; rcases x with x | x <;> rfl

theorem sumSwapAssoc_comp_inl {α : Type u₄} {β : Type u₅} {γ : Type u₆} :
    (sumSwapAssoc α β γ) ∘ Sum.inl = Sum.inr ∘ Sum.inl := rfl

/-- `1_b ⊗ [Ω^♯] = [Ω ⊎ (b ⊕ R)]`, with the orderings of the strands of `b` and of `R`
prepended. -/
noncomputable def idTensorIso (b : FreeMonoid S) :
    ((idD G b).tensor ((K.addLoose r).anchor dK cK)).Iso
      ((K.addLoose (Sum.elim (letters b) r)).anchor
        (Enumeration.prependR (Enumeration.finEnum _) dK)
        (Enumeration.prependRc (Enumeration.finEnum _) cK)) :=
  Diagram.Iso.ofProj (Sum.elim (fun e => e.elim) id) (sumSwapAssoc _ _ _) id id
    (by rintro (x | x) (y | y) h; exacts [x.elim, x.elim, y.elim, congrArg Sum.inr h])
    Function.injective_id (Equiv.injective _) Function.injective_id
    (fun t => ⟨fun _ => ⟨t, rfl⟩, fun _ => ⟨.inr t, rfl⟩⟩)
    (fun t => ⟨fun _ => ⟨t, rfl⟩, fun _ => ⟨(sumSwapAssoc _ _ _).symm t, by simp⟩⟩)
    (by
      rintro (e | z) n' rfl
      · exact e.elim
      · simp [Diagram.tensor, AGraph.tensor, PGraph.tensor, PDiagram.anchor, AGraph.ofPGraph,
          List.map_map, Function.comp_def]
        exact fun _ _ => rfl)
    (by
      rintro (e | z) n' rfl
      · exact e.elim
      · simp [Diagram.tensor, AGraph.tensor, PGraph.tensor, PDiagram.anchor, AGraph.ofPGraph,
          List.map_map, Function.comp_def]
        exact fun _ _ => rfl)
    (by
      change (((List.finRange _).map Sum.inl ++ dK.list.map Sum.inr)).map _ =
        (Enumeration.prependR (Enumeration.finEnum _) dK).list.map id
      rw [Enumeration.prependR_list, List.map_append, List.map_map, List.map_map, List.map_id,
        sumSwapAssoc_comp_inr, sumSwapAssoc_comp_inl]
      rfl)
    (by
      change (((List.finRange _).map Sum.inl ++ cK.list.map Sum.inr)).map _ =
        (Enumeration.prependRc (Enumeration.finEnum _) cK).list.map id
      rw [Enumeration.prependRc_list, List.map_append, List.map_map, List.map_map, List.map_id,
        sumSwapAssoc_comp_inr, sumSwapAssoc_comp_inl]
      rfl)
    (by rintro (i | d | ρ) e' rfl <;> rfl)
    (by rintro (e | z) n' rfl; exacts [e.elim, rfl])

end Diagram

/-! ### Laws of `F_s(G)` on classes (under C1) -/

namespace JoyalStreet

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} (J : JoyalStreet G)

include J

theorem cls_assoc {c d e : DClass G} (h₁ : c.cod = d.dom) (h₂ : d.cod = e.dom) :
    (c.comp d).comp e = c.comp (d.comp e) :=
  congrArg Subtype.val (J.dhom_assoc (⟨c, rfl, rfl⟩ : DHom G c.dom c.cod)
    ⟨d, h₁.symm, rfl⟩ ⟨e, h₂.symm, rfl⟩)

theorem cls_interchange {c c' d d' : DClass G} (hc : c.cod = c'.dom) (hd : d.cod = d'.dom) :
    (c.comp c').tensor (d.comp d') = (c.tensor d).comp (c'.tensor d') :=
  congrArg Subtype.val (J.dhom_tensor_comp (⟨c, rfl, rfl⟩ : DHom G c.dom c.cod)
    ⟨c', hc.symm, rfl⟩ (⟨d, rfl, rfl⟩ : DHom G d.dom d.cod) ⟨d', hd.symm, rfl⟩)

theorem cls_comp_id (c : DClass G) : c.comp (DClass.mk (Diagram.idD G c.cod)) = c :=
  congrArg Subtype.val (J.dhom_comp_id (⟨c, rfl, rfl⟩ : DHom G c.dom c.cod))

theorem cls_id_comp (c : DClass G) : (DClass.mk (Diagram.idD G c.dom)).comp c = c :=
  congrArg Subtype.val (J.dhom_id_comp (⟨c, rfl, rfl⟩ : DHom G c.dom c.cod))

end JoyalStreet

/-! ### Decompositions of `T`-surgery steps -/

open Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-- A `T`-surgery step read on classes (the class form of Lemma 3.3):
`c = h ∘ [Ω ⊎ R] ∘ g` and `d = h ∘ [Λ ⊎ R] ∘ g` for a template in `T`. -/
def TDecomp (T : Set (Template.{u} G)) (c d : DClass G) : Prop :=
  ∃ τ ∈ T, ∃ (R : Type) (_ : Finite R) (r : R → S)
    (dK : Enumeration (τ.Ω.toPGraph.addLoose R).IsDom)
    (cK : Enumeration (τ.Ω.toPGraph.addLoose R).IsCod) (g h : DClass G),
    g.cod = ((τ.Ω.addLoose r).anchor dK cK).domWord ∧
    ((τ.Ω.addLoose r).anchor dK cK).codWord = h.dom ∧
    (g.comp (DClass.mk ((τ.Ω.addLoose r).anchor dK cK))).comp h = c ∧
    (g.comp (DClass.mk ((τ.Λ.addLoose r).anchor (dK.mapEquiv (PGraph.liftDom τ.α R).symm)
      (cK.mapEquiv (PGraph.liftCod τ.β R).symm)))).comp h = d

variable {T : Set (Template.{u} G)}

theorem TStep.tDecomp {N E : Type} [Finite N] [Finite E] {N' : Type u₁} {E' : Type u₂}
    [Finite N'] [Finite E'] {Γ : Diagram G N E} {Ξ : Diagram G N' E'} (h : TStep T Γ Ξ) :
    TDecomp T (DClass.mk Γ) (DClass.mk Ξ) := by
  obtain ⟨τ, hτ, A, hA, φ, ⟨i⟩⟩ := h
  refine ⟨τ, hτ, hA.sharpLayer.R, inferInstance, Γ.rLabel hA.sharpLayer, Enumeration.ofFinite _,
    Enumeration.ofFinite _, _, _, ?_, ?_, (Γ.mk_eq_decomp _ φ _ _).symm,
    (Γ.mk_surgeryAt_eq_decomp _ φ τ.α τ.β τ.hα τ.hβ _ _).symm.trans (DClass.mk_eq_mk i)⟩
  · rw [DClass.cod_mk]
    exact Γ.lowerA_codWord _ φ _ _
  · rw [DClass.dom_mk]
    exact Γ.midΩ_codWord _ φ _ _

theorem TDecomp.tStep {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄} [Finite N]
    [Finite E] [Finite N'] [Finite E'] {X : Diagram G N E} {Ξ : Diagram G N' E'}
    (h : TDecomp T (DClass.mk X) (DClass.mk Ξ)) : TStep T X Ξ := by
  obtain ⟨τ, hτ, R, hR, r, dK, cK, g, h, hg, hh, hX, hΞ⟩ := h
  obtain ⟨A, hA, φ, ⟨k⟩⟩ := classRecognition X Ξ τ.α τ.β τ.hα τ.hβ r dK cK g h hg hh hX hΞ
  exact ⟨τ, hτ, A, hA, φ, ⟨k⟩⟩

section Laws

variable (J : JoyalStreet G)

include J in
theorem TDecomp.comp_right {c d : DClass G} (h : TDecomp T c d) (e : DClass G)
    (hce : c.cod = e.dom) : TDecomp T (c.comp e) (d.comp e) := by
  obtain ⟨τ, hτ, R, hR, r, dK, cK, g, h, hg, hh, rfl, rfl⟩ := h
  have hgM := hg.trans (DClass.dom_mk _).symm
  have hMh := (DClass.cod_mk _).trans hh
  have hcod := DClass.cod_comp (c := g.comp _) (d := h) (by rw [DClass.cod_comp hgM]; exact hMh)
  refine ⟨τ, hτ, R, hR, r, dK, cK, g, h.comp e, hg, ?_, ?_, ?_⟩
  · rw [DClass.dom_comp (hcod.symm.trans hce)]
    exact hh
  · rw [J.cls_assoc (by rw [DClass.cod_comp hgM]; exact hMh) (hcod.symm.trans hce)]
  · have hgM' : g.cod = (DClass.mk ((τ.Λ.addLoose r).anchor
        (dK.mapEquiv (PGraph.liftDom τ.α R).symm) (cK.mapEquiv (PGraph.liftCod τ.β R).symm))).dom := by
      rw [DClass.dom_mk, anchor_liftDom_domWord τ.α τ.β τ.hα r dK cK]
      exact hg
    have hMh' : (DClass.mk ((τ.Λ.addLoose r).anchor
        (dK.mapEquiv (PGraph.liftDom τ.α R).symm) (cK.mapEquiv (PGraph.liftCod τ.β R).symm))).cod =
        h.dom := by
      rw [DClass.cod_mk, anchor_liftCod_codWord τ.α τ.β τ.hβ r dK cK]
      exact hh
    rw [J.cls_assoc (by rw [DClass.cod_comp hgM']; exact hMh') (hcod.symm.trans hce)]

include J in
theorem TDecomp.comp_left {c d : DClass G} (h : TDecomp T c d) (e : DClass G)
    (hec : e.cod = c.dom) : TDecomp T (e.comp c) (e.comp d) := by
  obtain ⟨τ, hτ, R, hR, r, dK, cK, g, h, hg, hh, rfl, rfl⟩ := h
  have hgM := hg.trans (DClass.dom_mk _).symm
  have hMh := (DClass.cod_mk _).trans hh
  have hdom : (g.comp (DClass.mk ((τ.Ω.addLoose r).anchor dK cK))).dom = g.dom :=
    DClass.dom_comp hgM
  have hdom' := DClass.dom_comp (c := g.comp _) (d := h) (by rw [DClass.cod_comp hgM]; exact hMh)
  have heg : e.cod = g.dom := hec.trans (hdom'.trans hdom)
  refine ⟨τ, hτ, R, hR, r, dK, cK, e.comp g, h, ?_, hh, ?_, ?_⟩
  · rw [DClass.cod_comp heg]
    exact hg
  · rw [J.cls_assoc heg hgM, J.cls_assoc (heg.trans hdom.symm)
      (by rw [DClass.cod_comp hgM]; exact hMh)]
  · have hgM' : g.cod = (DClass.mk ((τ.Λ.addLoose r).anchor
        (dK.mapEquiv (PGraph.liftDom τ.α R).symm) (cK.mapEquiv (PGraph.liftCod τ.β R).symm))).dom := by
      rw [DClass.dom_mk, anchor_liftDom_domWord τ.α τ.β τ.hα r dK cK]
      exact hg
    have hMh' : (DClass.mk ((τ.Λ.addLoose r).anchor
        (dK.mapEquiv (PGraph.liftDom τ.α R).symm) (cK.mapEquiv (PGraph.liftCod τ.β R).symm))).cod =
        h.dom := by
      rw [DClass.cod_mk, anchor_liftCod_codWord τ.α τ.β τ.hβ r dK cK]
      exact hh
    rw [J.cls_assoc heg hgM', J.cls_assoc (heg.trans (DClass.dom_comp hgM').symm)
      (by rw [DClass.cod_comp hgM']; exact hMh')]

include J in
theorem JoyalStreet.cls_tensor_right_eq {g M h : DClass G} (e : DClass G) (h₁ : g.cod = M.dom)
    (h₂ : M.cod = h.dom) :
    ((g.comp M).comp h).tensor e = ((g.tensor e).comp (M.tensor (DClass.mk (idD G e.cod)))).comp
      (h.tensor (DClass.mk (idD G e.cod))) := by
  have hid : e.cod = (DClass.mk (idD G e.cod)).dom := by rw [DClass.dom_mk, idD_domWord]
  have he : (e.comp (DClass.mk (idD G e.cod))).comp (DClass.mk (idD G e.cod)) = e := by
    rw [J.cls_comp_id, J.cls_comp_id]
  have hide : (e.comp (DClass.mk (idD G e.cod))).cod = (DClass.mk (idD G e.cod)).dom := by
    rw [DClass.cod_comp hid, DClass.cod_mk, DClass.dom_mk, idD_codWord, idD_domWord]
  calc ((g.comp M).comp h).tensor e
      = ((g.comp M).comp h).tensor ((e.comp (DClass.mk (idD G e.cod))).comp
          (DClass.mk (idD G e.cod))) := by rw [he]
    _ = ((g.comp M).tensor (e.comp (DClass.mk (idD G e.cod)))).comp
          (h.tensor (DClass.mk (idD G e.cod))) :=
        J.cls_interchange (by rw [DClass.cod_comp h₁]; exact h₂) hide
    _ = _ := by rw [J.cls_interchange h₁ hid]

include J in
theorem JoyalStreet.cls_tensor_left_eq {g M h : DClass G} (e : DClass G) (h₁ : g.cod = M.dom)
    (h₂ : M.cod = h.dom) :
    e.tensor ((g.comp M).comp h) = ((e.tensor g).comp ((DClass.mk (idD G e.cod)).tensor M)).comp
      ((DClass.mk (idD G e.cod)).tensor h) := by
  have hid : e.cod = (DClass.mk (idD G e.cod)).dom := by rw [DClass.dom_mk, idD_domWord]
  have he : (e.comp (DClass.mk (idD G e.cod))).comp (DClass.mk (idD G e.cod)) = e := by
    rw [J.cls_comp_id, J.cls_comp_id]
  have hide : (e.comp (DClass.mk (idD G e.cod))).cod = (DClass.mk (idD G e.cod)).dom := by
    rw [DClass.cod_comp hid, DClass.cod_mk, DClass.dom_mk, idD_codWord, idD_domWord]
  calc e.tensor ((g.comp M).comp h)
      = ((e.comp (DClass.mk (idD G e.cod))).comp (DClass.mk (idD G e.cod))).tensor
          ((g.comp M).comp h) := by rw [he]
    _ = ((e.comp (DClass.mk (idD G e.cod))).tensor (g.comp M)).comp
          ((DClass.mk (idD G e.cod)).tensor h) :=
        J.cls_interchange hide (by rw [DClass.cod_comp h₁]; exact h₂)
    _ = _ := by rw [J.cls_interchange hid h₁]

include J in
theorem TDecomp.tensor_right {c d : DClass G} (h : TDecomp T c d) (e : DClass G) :
    TDecomp T (c.tensor e) (d.tensor e) := by
  obtain ⟨τ, hτ, R, hR, r, dK, cK, g, h, hg, hh, rfl, rfl⟩ := h
  have hgM := hg.trans (DClass.dom_mk _).symm
  have hMh := (DClass.cod_mk _).trans hh
  have hgM' : g.cod = (DClass.mk ((τ.Λ.addLoose r).anchor
      (dK.mapEquiv (PGraph.liftDom τ.α R).symm) (cK.mapEquiv (PGraph.liftCod τ.β R).symm))).dom := by
    rw [DClass.dom_mk, anchor_liftDom_domWord τ.α τ.β τ.hα r dK cK]
    exact hg
  have hMh' : (DClass.mk ((τ.Λ.addLoose r).anchor
      (dK.mapEquiv (PGraph.liftDom τ.α R).symm) (cK.mapEquiv (PGraph.liftCod τ.β R).symm))).cod =
      h.dom := by
    rw [DClass.cod_mk, anchor_liftCod_codWord τ.α τ.β τ.hβ r dK cK]
    exact hh
  let iΩ := tensorIdIso τ.Ω r dK cK e.cod
  let iΛ := tensorIdIso τ.Λ r (dK.mapEquiv (PGraph.liftDom τ.α R).symm)
    (cK.mapEquiv (PGraph.liftCod τ.β R).symm) e.cod
  refine ⟨τ, hτ, R ⊕ Fin (wlen e.cod), inferInstance, Sum.elim r (letters e.cod),
    dK.appendR (Enumeration.finEnum _), cK.appendRc (Enumeration.finEnum _), g.tensor e,
    h.tensor (DClass.mk (idD G e.cod)), ?_, ?_, ?_, ?_⟩
  · rw [DClass.cod_tensor, iΩ.domWord_eq, tensor_domWord, idD_domWord, hg]
  · rw [DClass.dom_tensor, iΩ.codWord_eq, tensor_codWord, idD_codWord, DClass.dom_mk,
      idD_domWord, hh]
  · rw [J.cls_tensor_right_eq e hgM hMh, DClass.mk_tensor, DClass.mk_eq_mk iΩ]
  · rw [J.cls_tensor_right_eq e hgM' hMh', DClass.mk_tensor, DClass.mk_eq_mk iΛ,
      Enumeration.appendR_liftDom, Enumeration.appendRc_liftCod]

include J in
theorem TDecomp.tensor_left {c d : DClass G} (h : TDecomp T c d) (e : DClass G) :
    TDecomp T (e.tensor c) (e.tensor d) := by
  obtain ⟨τ, hτ, R, hR, r, dK, cK, g, h, hg, hh, rfl, rfl⟩ := h
  have hgM := hg.trans (DClass.dom_mk _).symm
  have hMh := (DClass.cod_mk _).trans hh
  have hgM' : g.cod = (DClass.mk ((τ.Λ.addLoose r).anchor
      (dK.mapEquiv (PGraph.liftDom τ.α R).symm) (cK.mapEquiv (PGraph.liftCod τ.β R).symm))).dom := by
    rw [DClass.dom_mk, anchor_liftDom_domWord τ.α τ.β τ.hα r dK cK]
    exact hg
  have hMh' : (DClass.mk ((τ.Λ.addLoose r).anchor
      (dK.mapEquiv (PGraph.liftDom τ.α R).symm) (cK.mapEquiv (PGraph.liftCod τ.β R).symm))).cod =
      h.dom := by
    rw [DClass.cod_mk, anchor_liftCod_codWord τ.α τ.β τ.hβ r dK cK]
    exact hh
  let iΩ := idTensorIso τ.Ω r dK cK e.cod
  let iΛ := idTensorIso τ.Λ r (dK.mapEquiv (PGraph.liftDom τ.α R).symm)
    (cK.mapEquiv (PGraph.liftCod τ.β R).symm) e.cod
  refine ⟨τ, hτ, Fin (wlen e.cod) ⊕ R, inferInstance, Sum.elim (letters e.cod) r,
    Enumeration.prependR (Enumeration.finEnum _) dK,
    Enumeration.prependRc (Enumeration.finEnum _) cK, e.tensor g,
    (DClass.mk (idD G e.cod)).tensor h, ?_, ?_, ?_, ?_⟩
  · rw [DClass.cod_tensor, iΩ.domWord_eq, tensor_domWord, idD_domWord, hg]
  · rw [DClass.dom_tensor, iΩ.codWord_eq, tensor_codWord, idD_codWord, DClass.dom_mk,
      idD_domWord, hh]
  · rw [J.cls_tensor_left_eq e hgM hMh, DClass.mk_tensor, DClass.mk_eq_mk iΩ]
  · rw [J.cls_tensor_left_eq e hgM' hMh', DClass.mk_tensor, DClass.mk_eq_mk iΛ,
      Enumeration.prependR_liftDom, Enumeration.prependRc_liftCod]

end Laws

end FreeMarkov
