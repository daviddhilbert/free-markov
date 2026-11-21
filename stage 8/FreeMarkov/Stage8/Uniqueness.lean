/-
Free Markov categories, Stage 8: uniqueness (item (c)).

For a free `DD`-graph monoid `G`, the free Markov category `F_s(G)/S_M` (`J.FsM`) and a Markov
category `M`:

* `JoyalStreet.restrict`: the restriction functor `MarkovFun (F_s(G)/S_M) M ⥤ Interp G M`.
* `JoyalStreet.inductionM`: the generation principle in `F_s(G)/S_M` (quotient form of
  `JoyalStreet.induction`).
* `JoyalStreet.extend`: a morphism of interpretations `α : F|_G → F'|_G` between the restrictions of
  two Markov functors extends to a monoidal natural transformation `F → F'`, with components
  `θ_w = φ'_w ∘ (α_{a_1} ⊗ … ⊗ α_{a_n}) ∘ φ_w⁻¹` (naturality on the generators gives naturality on
  all morphisms by the generation principle).
* `JoyalStreet.restrict_existsUnique`: **(c)** it is the only monoidal natural transformation
  restricting to `α`; `restrict_full`, `restrict_faithful`: the restriction functor is full and
  faithful; `iso_existsUnique`: an isomorphism between the restrictions lifts to exactly one monoidal
  natural isomorphism.

The cited result C1 enters only through `J : JoyalStreet _`.
-/
module

public import FreeMarkov.Stage8.Interp

@[expose] public section

universe w v u v'

namespace FreeMarkov

open CategoryTheory MonoidalCategory ComonObj Category Functor.LaxMonoidal Functor.OplaxMonoidal
  StrictSMC StrictMarkov

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S}
  {M : Type u} [Category.{v'} M] [MonoidalCategory M] [MarkovCategory M]

namespace JoyalStreet

variable (J : JoyalStreet G.toFreeGraphMonoid)

/-- **Generation principle** in `F_s(G)/S_M`: every morphism is built from the generators `i_m(x)`,
identities and symmetries by composition and monoidal product. -/
theorem inductionM {P : ∀ {a b : J.FsM}, (a ⟶ b) → Prop}
    (h_gen : ∀ x : G.A, P (J.genM x))
    (h_id : ∀ a : J.FsM, P (𝟙 a))
    (h_braid : ∀ a b : J.FsM, P (σ_ a b))
    (h_comp : ∀ {a b c : J.FsM} (f : a ⟶ b) (g : b ⟶ c), P f → P g → P (f ≫ g))
    (h_tensor : ∀ {a b c d : J.FsM} (f : a ⟶ b) (g : c ⟶ d), P f → P g → P (f ⊗ₛ g))
    {a b : J.FsM} (f : a ⟶ b) : P f := by
  induction f using Quotient.ind with
  | _ g =>
  change P (J.projM.map (J.hom g))
  refine J.induction (P := fun {a b} g => P (J.projM.map g)) h_gen (fun a => h_id a)
    (fun a b => h_braid a b) (fun f g hf hg => ?_) (fun f g hf hg => h_tensor _ _ hf hg) (J.hom g)
  rw [Functor.map_comp]
  exact h_comp _ _ hf hg

/-- The **restriction functor** from Markov functors `F_s(G)/S_M → M` and monoidal natural
transformations to interpretations of `G` in `M` and their morphisms. -/
noncomputable def restrict : MarkovFun J.FsM M ⥤ Interp G M where
  obj := J.restrictObj
  map := J.restrictMap
  map_id _ := Interp.hom_ext fun _ => rfl
  map_comp _ _ := Interp.hom_ext fun _ => rfl

@[simp] theorem restrict_obj (F : MarkovFun J.FsM M) : J.restrict.obj F = J.restrictObj F := rfl

@[simp] theorem restrict_map_app {F F' : MarkovFun J.FsM M} (θ : F ⟶ F') (a : S) :
    (J.restrict.map θ).app a = θ.nat.app (J.letterM a) := rfl

/-! ### Extension of a morphism of interpretations -/

variable {F F' : MarkovFun J.FsM M} (α : J.restrictObj F ⟶ J.restrictObj F')

/-- `Θ_r = φ'_r ∘ lpRMap α r ∘ φ_r⁻¹` on the products of letters along reversed lists. -/
noncomputable def extR (r : List S) :
    F.obj (wR J.letterM r) ⟶ F'.obj (wR J.letterM r) :=
  (cmpR F.toFunctor J.letterM r).inv ≫ lpRMap α.app r ≫ (cmpR F'.toFunctor J.letterM r).hom

theorem extR_nil : J.extR α [] = η F.toFunctor ≫ Functor.LaxMonoidal.ε F'.toFunctor :=
  congrArg (_ ≫ ·) (id_comp _)

theorem extR_single (a : S) : J.extR α [a] = α.app a :=
  (id_comp _).trans (comp_id _)

theorem extR_cons (a b : S) (r : List S) :
    J.extR α (a :: b :: r) = δ F.toFunctor (wR J.letterM (b :: r)) (J.letterM a) ≫
      (J.extR α (b :: r) ⊗ₘ α.app a) ≫ μ F'.toFunctor (wR J.letterM (b :: r)) (J.letterM a) := by
  change (δ F.toFunctor (wR J.letterM (b :: r)) (J.letterM a) ≫
      (cmpR F.toFunctor J.letterM (b :: r)).inv ▷ F.obj (J.letterM a)) ≫
      (lpRMap α.app (b :: r) ⊗ₘ α.app a) ≫
      ((cmpR F'.toFunctor J.letterM (b :: r)).hom ▷ F'.obj (J.letterM a) ≫
        μ F'.toFunctor (wR J.letterM (b :: r)) (J.letterM a)) = _
  rw [assoc, whiskerRight_comp_tensorHom'_assoc, ← comp_tensorHom'_assoc, assoc]
  rfl

/-- The components `θ_w = φ'_w ∘ lpMap α w ∘ φ_w⁻¹` of the extension. -/
noncomputable def extApp (X : J.FsM) : F.obj X ⟶ F'.obj X :=
  (J.cmpW F (J.unword _ _ X)).inv ≫ lpMap α.app (J.unword _ _ X) ≫ (J.cmpW F' (J.unword _ _ X)).hom

theorem extApp_wordM (w : FreeMonoid S) :
    J.extApp α (J.wordM w) = (J.cmpW F w).inv ≫ lpMap α.app w ≫ (J.cmpW F' w).hom := rfl

theorem extApp_eq (X : J.FsM) (r : List S) (h : (FreeMonoid.toList (J.unword _ _ X)).reverse = r) :
    J.extApp α X = F.toFunctor.map (eqToHom (by subst h; exact (J.wR_letterM _).symm)) ≫
      (cmpR F.toFunctor J.letterM r).inv ≫ lpRMap α.app r ≫ (cmpR F'.toFunctor J.letterM r).hom ≫
        F'.toFunctor.map (eqToHom (by subst h; exact J.wR_letterM _)) := by
  subst h
  rw [extApp, cmpW_inv, cmpW_hom]
  exact Category.assoc (F.toFunctor.map _) _ _

omit J in
theorem rev_wR_of (r : List S) : (FreeMonoid.toList (wR FreeMonoid.of r)).reverse = r := by
  have h : wR FreeMonoid.of r = FreeMonoid.ofList r.reverse := by
    rw [wR_eq_lift]
    exact DFunLike.congr_fun (FreeMonoid.hom_eq (f := FreeMonoid.lift FreeMonoid.of)
      (g := MonoidHom.id _) (fun _ => by simp)) _
  rw [h, FreeMonoid.toList_ofList, List.reverse_reverse]

theorem rev_wR (r : List S) : (FreeMonoid.toList (J.unword _ _ (wR J.letterM r))).reverse = r :=
  rev_wR_of r

theorem extApp_wR (r : List S) : J.extApp α (wR J.letterM r) = J.extR α r := by
  rw [J.extApp_eq α (wR J.letterM r) r (J.rev_wR r)]
  simp [extR]

theorem extApp_letter (a : S) : J.extApp α (J.letterM a) = α.app a := by
  rw [extApp_wordM, J.cmpW_of_inv, J.cmpW_of_hom]
  exact (id_comp _).trans (comp_id _)

theorem extApp_one : J.extApp α 1 = η F.toFunctor ≫ Functor.LaxMonoidal.ε F'.toFunctor := by
  show J.extApp α (J.wordM 1) = _
  rw [extApp_wordM, J.cmpW_one_inv, J.cmpW_one_hom]
  exact congrArg (_ ≫ ·) (id_comp _)

theorem extApp_unit :
    Functor.LaxMonoidal.ε F.toFunctor ≫ J.extApp α (𝟙_ J.FsM) = Functor.LaxMonoidal.ε F'.toFunctor := by
  show _ ≫ J.extApp α 1 = _
  rw [J.extApp_one, Functor.Monoidal.ε_η_assoc]

theorem extApp_snoc (X : J.FsM) (a : S) :
    μ F.toFunctor X (J.letterM a) ≫ J.extApp α (X ⊗ J.letterM a) =
      (J.extApp α X ⊗ₘ J.extApp α (J.letterM a)) ≫ μ F'.toFunctor X (J.letterM a) := by
  obtain ⟨r, rfl⟩ : ∃ r, X = wR J.letterM r := ⟨_, (J.wR_letterM (J.unword _ _ X)).symm⟩
  rcases r with _ | ⟨b, r⟩
  · have e : (FreeMonoid.toList (J.unword _ _ (wR J.letterM [] ⊗ J.letterM a))).reverse = [a] := rfl
    rw [J.extApp_eq α _ [a] e, J.extApp_wR, J.extApp_letter, extR_nil]
    simp only [cmpR_single_hom, cmpR_single_inv]
    exact (congrArg (μ F.toFunctor _ _ ≫ ·) (congrArg (_ ≫ ·) ((id_comp _).trans
      (congrArg (_ ≫ ·) (id_comp _))))).trans (unit_case (F := F.toFunctor) (J.letterM a) (α.app a))
  · change μ F.toFunctor (wR J.letterM (b :: r)) (J.letterM a) ≫
        J.extApp α (wR J.letterM (a :: b :: r)) =
      (J.extApp α (wR J.letterM (b :: r)) ⊗ₘ J.extApp α (J.letterM a)) ≫
        μ F'.toFunctor (wR J.letterM (b :: r)) (J.letterM a)
    rw [J.extApp_wR, J.extApp_wR, J.extApp_letter, extR_cons]
    exact Functor.Monoidal.μ_δ_assoc F.toFunctor _ _ _

/-- The extension is monoidal: `θ_{X ⊗ Y} ∘ μ_F = μ_{F'} ∘ (θ_X ⊗ θ_Y)`. -/
theorem extApp_tensor (X Y : J.FsM) :
    μ F.toFunctor X Y ≫ J.extApp α (X ⊗ Y) = (J.extApp α X ⊗ₘ J.extApp α Y) ≫ μ F'.toFunctor X Y := by
  obtain ⟨r, rfl⟩ : ∃ r, Y = wR J.letterM r := ⟨_, (J.wR_letterM (J.unword _ _ Y)).symm⟩
  exact tensor_of_snoc J.letterM (J.extApp α) (J.extApp_unit α) (J.extApp_snoc α) X r

theorem extApp_tensor' (X Y : J.FsM) :
    J.extApp α (X ⊗ Y) = δ F.toFunctor X Y ≫ (J.extApp α X ⊗ₘ J.extApp α Y) ≫ μ F'.toFunctor X Y := by
  rw [← J.extApp_tensor α, Functor.Monoidal.δ_μ_assoc]

theorem extApp_mul' (X Y : J.FsM) :
    J.extApp α (X * Y) = δ F.toFunctor X Y ≫ (J.extApp α X ⊗ₘ J.extApp α Y) ≫ μ F'.toFunctor X Y :=
  J.extApp_tensor' α X Y

/-- The extension is natural: naturality on the generators (the morphism of interpretations)
extends to all morphisms by the generation principle. -/
theorem extApp_naturality {X Y : J.FsM} (f : X ⟶ Y) :
    F.map f ≫ J.extApp α Y = J.extApp α X ≫ F'.map f := by
  induction f using J.inductionM with
  | h_gen x =>
    rw [extApp_wordM, extApp_wordM]
    have hc := α.comm x
    change ((J.cmpW F (G.s x)).hom ≫ F.map (J.genM x) ≫ (J.cmpW F (G.t x)).inv) ≫
        lpMap α.app (G.t x) =
      lpMap α.app (G.s x) ≫
        ((J.cmpW F' (G.s x)).hom ≫ F'.map (J.genM x) ≫ (J.cmpW F' (G.t x)).inv) at hc
    rw [← cancel_epi (J.cmpW F (G.s x)).hom]
    simp only [assoc] at hc ⊢
    rw [reassoc_of% hc, Iso.inv_hom_id, comp_id, Iso.hom_inv_id_assoc]
  | h_id a => simp
  | h_braid a b =>
    change F.map (β_ a b).hom ≫ J.extApp α (b ⊗ a) = J.extApp α (a ⊗ b) ≫ F'.map (β_ a b).hom
    rw [MarkovFun.map, MarkovFun.map, Functor.map_braiding, Functor.map_braiding, J.extApp_tensor',
      J.extApp_tensor']
    simp only [assoc, Functor.Monoidal.μ_δ_assoc, BraidedCategory.braiding_naturality_assoc]
  | h_comp f g hf hg =>
    rw [MarkovFun.map, MarkovFun.map, Functor.map_comp, Functor.map_comp, assoc]
    erw [hg, ← assoc, hf, assoc]
  | h_tensor f g hf hg =>
    change F.map (f ⊗ₘ g) ≫ _ = _ ≫ F'.map (f ⊗ₘ g)
    rw [MarkovFun.map, MarkovFun.map, Functor.Monoidal.map_tensor, Functor.Monoidal.map_tensor,
      J.extApp_mul', J.extApp_mul']
    simp only [assoc, Functor.Monoidal.μ_δ_assoc, tensorHom_comp_tensorHom_assoc]
    rw [hf, hg]

/-- **Extension**: a morphism of interpretations `α : F|_G → F'|_G` extends to a monoidal natural
transformation `F → F'`. -/
noncomputable def extend : F ⟶ F' where
  nat := { app := J.extApp α, naturality := fun _ _ f => J.extApp_naturality α f }
  isMonoidal := { unit := J.extApp_unit α, tensor := J.extApp_tensor α }

theorem extend_app (X : J.FsM) : (J.extend α).nat.app X = J.extApp α X := rfl

theorem restrict_extend : J.restrict.map (J.extend α) = α :=
  Interp.hom_ext fun a => J.extApp_letter α a

/-- A monoidal natural transformation is determined by its components on the letters. -/
theorem eq_extend (θ : F ⟶ F') (h : J.restrict.map θ = α) : θ = J.extend α := by
  subst h
  refine MarkovFun.hom_ext (NatTrans.ext (funext fun X => ?_))
  have hn := J.cmpW_naturality θ (J.unword _ _ X)
  change θ.nat.app X = (J.cmpW F (J.unword _ _ X)).inv ≫
    lpMap (fun a => θ.nat.app (J.letterM a)) (J.unword _ _ X) ≫ (J.cmpW F' (J.unword _ _ X)).hom
  exact (Iso.eq_inv_comp _).2 hn

/-- **(c)** A morphism of interpretations between the restrictions of two Markov functors
`F_s(G)/S_M → M` extends to exactly one monoidal natural transformation between them. -/
theorem restrict_existsUnique : ∃! θ : F ⟶ F', J.restrict.map θ = α :=
  ⟨J.extend α, J.restrict_extend α, fun θ h => J.eq_extend α θ h⟩

end JoyalStreet

namespace JoyalStreet

variable (J : JoyalStreet G.toFreeGraphMonoid)

instance restrict_full : (J.restrict (M := M)).Full where
  map_surjective α := ⟨J.extend α, J.restrict_extend α⟩

instance restrict_faithful : (J.restrict (M := M)).Faithful where
  map_injective {_ _ θ₁ θ₂} h := (J.eq_extend _ θ₁ rfl).trans (J.eq_extend _ θ₂ h.symm).symm

/-- **(c)**, isomorphisms: an isomorphism between the restrictions of two Markov functors lifts to
exactly one monoidal natural isomorphism between them. -/
theorem iso_existsUnique {F F' : MarkovFun J.FsM M} (e : J.restrictObj F ≅ J.restrictObj F') :
    ∃! θ : F ≅ F', J.restrict.mapIso θ = e := by
  refine ⟨J.restrict.preimageIso e, Iso.ext (J.restrict.map_preimage e.hom), fun θ h => ?_⟩
  ext1
  apply J.restrict.map_injective
  exact (congrArg Iso.hom h).trans (J.restrict.map_preimage e.hom).symm



end JoyalStreet

end FreeMarkov
