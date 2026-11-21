/-
Free Markov categories, Stage 2: `S_T` is a monoidal congruence relation on `F_s(G)` and
the quotient `F_s(G) / S_T` is a symmetric strict monoidal category (after
Definition 3.4).

"So `T`-equivalence is indeed a monoidal congruence relation on `F_s(G)`; we denote it by
`S_T`. It follows that the quotient `F_s(G) / S_T` is a symmetric strict monoidal
category."

The quotient follows the device used for `Syn_s(G)` in Stage 0: the objects are the
words, the hom-sets are plain quotients of the hom-sets of `F_s(G)`, and the laws are
transported along the projection functor, which is strict symmetric monoidal.
-/
module

public import FreeMarkov.Stage2.Congruence

@[expose] public section

universe u w v

namespace FreeMarkov

open CategoryTheory StrictSMC Relation Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-! ### `S_T` is a monoidal congruence -/

namespace SRel

variable {T : Set (Template.{u} G)} (J : JoyalStreet G)

include J in
theorem tensor_right_aux (h0 : Template.empty G ∈ T) {a b : FinDiag G} (h : TEquiv T a b)
    (Υ : FinDiag G) :
    SRel T ((DClass.mk a.2).tensor (DClass.mk Υ.2)) ((DClass.mk b.2).tensor (DClass.mk Υ.2)) := by
  induction h with
  | refl => exact SRel.refl _
  | @tail b c _ hbc ih =>
    refine ih.trans h0 ?_
    have h' := (TStep.tDecomp (Γ := b.2) (Ξ := c.2) hbc).tensor_right J (DClass.mk Υ.2)
    rw [DClass.mk_tensor, DClass.mk_tensor] at h' ⊢
    exact SRel.of_tStep h'.tStep

include J in
theorem tensor_left_aux (h0 : Template.empty G ∈ T) {a b : FinDiag G} (h : TEquiv T a b)
    (Υ : FinDiag G) :
    SRel T ((DClass.mk Υ.2).tensor (DClass.mk a.2)) ((DClass.mk Υ.2).tensor (DClass.mk b.2)) := by
  induction h with
  | refl => exact SRel.refl _
  | @tail b c _ hbc ih =>
    refine ih.trans h0 ?_
    have h' := (TStep.tDecomp (Γ := b.2) (Ξ := c.2) hbc).tensor_left J (DClass.mk Υ.2)
    rw [DClass.mk_tensor, DClass.mk_tensor] at h' ⊢
    exact SRel.of_tStep h'.tStep

include J in
theorem comp_right_aux (h0 : Template.empty G ∈ T) {a b : FinDiag G} (h : TEquiv T a b)
    (Υ : FinDiag G) (hc : a.2.codWord = Υ.2.domWord) :
    SRel T ((DClass.mk a.2).comp (DClass.mk Υ.2)) ((DClass.mk b.2).comp (DClass.mk Υ.2)) := by
  induction h with
  | refl => exact SRel.refl _
  | @tail b c hab hbc ih =>
    refine ih.trans h0 ?_
    have hb : b.2.codWord = Υ.2.domWord := (TEquiv.codWord_eq hab).trans hc
    have hc' : c.2.codWord = Υ.2.domWord := (TStep.codWord_eq hbc).trans hb
    have h' := (TStep.tDecomp (Γ := b.2) (Ξ := c.2) hbc).comp_right J (DClass.mk Υ.2) (by rw [DClass.cod_mk, DClass.dom_mk, hb])
    rw [DClass.mk_comp _ _ hb, DClass.mk_comp _ _ hc'] at h' ⊢
    exact SRel.of_tStep h'.tStep

include J in
theorem comp_left_aux (h0 : Template.empty G ∈ T) {a b : FinDiag G} (h : TEquiv T a b)
    (Υ : FinDiag G) (hc : Υ.2.codWord = a.2.domWord) :
    SRel T ((DClass.mk Υ.2).comp (DClass.mk a.2)) ((DClass.mk Υ.2).comp (DClass.mk b.2)) := by
  induction h with
  | refl => exact SRel.refl _
  | @tail b c hab hbc ih =>
    refine ih.trans h0 ?_
    have hb : Υ.2.codWord = b.2.domWord := hc.trans (TEquiv.domWord_eq hab).symm
    have hc' : Υ.2.codWord = c.2.domWord := hb.trans (TStep.domWord_eq hbc).symm
    have h' := (TStep.tDecomp (Γ := b.2) (Ξ := c.2) hbc).comp_left J (DClass.mk Υ.2) (by rw [DClass.cod_mk, DClass.dom_mk, hb])
    rw [DClass.mk_comp _ _ hb, DClass.mk_comp _ _ hc'] at h' ⊢
    exact SRel.of_tStep h'.tStep

theorem exists_fin (c : DClass G) : ∃ Γ : FinDiag G, Quotient.mk _ Γ = c ∧ c = DClass.mk Γ.2 := by
  obtain ⟨Γ, rfl⟩ := Quotient.exists_rep c
  exact ⟨Γ, rfl, DClass.mk_fin Γ⟩

include J in
theorem tensor_right (hT : Template.IsSymmetric T) {c c' : DClass G} (h : SRel T c c')
    (e : DClass G) : SRel T (c.tensor e) (c'.tensor e) := by
  obtain ⟨a, b, rfl, rfl, h⟩ := h
  obtain ⟨Υ, -, rfl⟩ := exists_fin e
  rw [DClass.mk_fin a, DClass.mk_fin b]
  exact tensor_right_aux J hT.empty_mem h Υ

include J in
theorem tensor_left (hT : Template.IsSymmetric T) {c c' : DClass G} (h : SRel T c c')
    (e : DClass G) : SRel T (e.tensor c) (e.tensor c') := by
  obtain ⟨a, b, rfl, rfl, h⟩ := h
  obtain ⟨Υ, -, rfl⟩ := exists_fin e
  rw [DClass.mk_fin a, DClass.mk_fin b]
  exact tensor_left_aux J hT.empty_mem h Υ

include J in
theorem comp_right (hT : Template.IsSymmetric T) {c c' : DClass G} (h : SRel T c c')
    (e : DClass G) (hce : c.cod = e.dom) : SRel T (c.comp e) (c'.comp e) := by
  obtain ⟨a, b, rfl, rfl, h⟩ := h
  obtain ⟨Υ, -, rfl⟩ := exists_fin e
  rw [DClass.mk_fin a, DClass.mk_fin b]
  rw [DClass.mk_fin a, DClass.cod_mk, DClass.dom_mk] at hce
  exact comp_right_aux J hT.empty_mem h Υ hce

include J in
theorem comp_left (hT : Template.IsSymmetric T) {c c' : DClass G} (h : SRel T c c')
    (e : DClass G) (hec : e.cod = c.dom) : SRel T (e.comp c) (e.comp c') := by
  obtain ⟨a, b, rfl, rfl, h⟩ := h
  obtain ⟨Υ, -, rfl⟩ := exists_fin e
  rw [DClass.mk_fin a, DClass.mk_fin b]
  rw [DClass.mk_fin a, DClass.cod_mk, DClass.dom_mk] at hec
  exact comp_left_aux J hT.empty_mem h Υ hec

include J in
/-- "If `[Γ] ⇝_T [Γ']` and `[Υ] ⇝_T [Υ']` then `[Υ] ⊗ [Γ] ⇝_T [Υ'] ⊗ [Γ']`." -/
theorem tensor (hT : Template.IsSymmetric T) {c c' d d' : DClass G} (h₁ : SRel T c c')
    (h₂ : SRel T d d') : SRel T (c.tensor d) (c'.tensor d') :=
  (h₁.tensor_right J hT d).trans hT.empty_mem (h₂.tensor_left J hT c')

include J in
/-- "... and `[Υ] ∘ [Γ] ⇝_T [Υ'] ∘ [Γ']` if the compositions are defined." -/
theorem comp (hT : Template.IsSymmetric T) {c c' d d' : DClass G} (h₁ : SRel T c c')
    (h₂ : SRel T d d') (hcd : c.cod = d.dom) : SRel T (c.comp d) (c'.comp d') :=
  (h₁.comp_right J hT d hcd).trans hT.empty_mem
    (h₂.comp_left J hT c' (h₁.cod_eq.trans hcd))

end SRel

/-! ### The quotient category `F_s(G) / S_T` -/

namespace JoyalStreet

variable (J : JoyalStreet G) (T : Set (Template.{u} G)) (hT : Template.IsSymmetric T)

/-- `S_T` on the hom-set `F_s(G)(a, b)`. -/
def homSetoid (_J : JoyalStreet G) (a b : FreeMonoid S) : Setoid (DHom G a b) where
  r f g := SRel T f.1 g.1
  iseqv := ⟨fun _ => SRel.refl _, fun h => h.symm hT.symm_mem, fun h h' => h.trans hT.empty_mem h'⟩

/-- **The quotient `F_s(G) / S_T`**: objects the words over `S`, morphisms the classes of
`F_s(G)` modulo `S_T`. -/
def Quot (_J : JoyalStreet G) (_T : Set (Template.{u} G)) (_hT : Template.IsSymmetric _T) :
    Type w :=
  FreeMonoid S

instance : Monoid (J.Quot T hT) := inferInstanceAs (Monoid (FreeMonoid S))

noncomputable instance quotCategory : Category.{max w v} (J.Quot T hT) where
  Hom a b := Quotient (J.homSetoid T hT a b)
  id a := Quotient.mk _ (DHom.id G a)
  comp f g := Quotient.map₂ DHom.comp
    (fun f _ hf g _ hg => SRel.comp J hT hf hg (f.2.2.trans g.2.1.symm)) f g
  id_comp f := by
    induction f using Quotient.ind
    exact congrArg (Quotient.mk _) (J.dhom_id_comp _)
  comp_id f := by
    induction f using Quotient.ind
    exact congrArg (Quotient.mk _) (J.dhom_comp_id _)
  assoc f g h := by
    induction f using Quotient.ind
    induction g using Quotient.ind
    induction h using Quotient.ind
    exact congrArg (Quotient.mk _) (J.dhom_assoc _ _ _)

/-- The projection `F_s(G) → F_s(G) / S_T`. -/
noncomputable def quotProj : J.Fs ⥤ J.Quot T hT where
  obj a := a
  map f := Quotient.mk _ f
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable instance quotStrictSMC : StrictSMC (J.Quot T hT) where
  tensorHom f g := Quotient.map₂ DHom.tensor (fun _ _ hf _ _ hg => SRel.tensor J hT hf hg) f g
  braid a b := Quotient.mk _ (DHom.braid G a b)
  tensorHom_id a c := congrArg (Quotient.mk _) (J.dhom_tensor_id a c)
  tensorHom_comp f f' g g' := by
    induction f using Quotient.ind
    induction f' using Quotient.ind
    induction g using Quotient.ind
    induction g' using Quotient.ind
    exact congrArg (Quotient.mk _) (J.dhom_tensor_comp _ _ _ _)
  tensorHom_assoc x y z := by
    induction x using Quotient.ind
    induction y using Quotient.ind
    induction z using Quotient.ind
    exact (J.quotProj T hT).mk_map_congr (StrictSMC.tensorHom_assoc (C := J.Fs) _ _ _)
  id_one_tensorHom f := by
    induction f using Quotient.ind
    exact (J.quotProj T hT).mk_map_congr (StrictSMC.id_one_tensorHom (C := J.Fs) _)
  tensorHom_id_one f := by
    induction f using Quotient.ind
    exact (J.quotProj T hT).mk_map_congr (StrictSMC.tensorHom_id_one (C := J.Fs) _)
  braid_natural f g := by
    induction f using Quotient.ind
    induction g using Quotient.ind
    exact congrArg (Quotient.mk _) (J.dhom_braid_natural _ _)
  braid_braid a b := congrArg (Quotient.mk _) (J.dhom_braid_braid a b)
  hexagon a b c := by
    have := (J.quotProj T hT).mk_map_congr (StrictSMC.hexagon (C := J.Fs) a b c)
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map] at this
    exact this

/-- The projection `F_s(G) → F_s(G) / S_T` is a strict symmetric monoidal functor. -/
noncomputable def quotProjStrict : StrictFunctor J.Fs (J.Quot T hT) where
  toFunctor := J.quotProj T hT
  obj_one := rfl
  obj_mul _ _ := rfl
  map_tensorHom _ _ := rfl
  map_braid _ _ := rfl

/-- Two morphisms of `F_s(G)` have the same image in `F_s(G) / S_T` exactly when they are
`T`-equivalent. -/
theorem quotProj_map_eq_iff {a b : J.Fs} (f g : a ⟶ b) :
    (J.quotProj T hT).map f = (J.quotProj T hT).map g ↔ SRel T (J.cls f) (J.cls g) :=
  Quotient.eq

end JoyalStreet

end FreeMarkov
