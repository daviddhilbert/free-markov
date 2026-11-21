/-
Free Markov categories, Stage 3: Theorem 4.1, `F_s(G) / S_M` is the free Markov category
over `G`.

* `i_s = J.ι : G → F_s(G)` (Stage 1) and `i_m = (- / S_M) ∘ i_s`, which matches duplicates
  and discards (`iM_matches`).
* For a strict Markov category `D` and `f : G → D` matching duplicates and discards, `F_s`
  is the strict symmetric monoidal functor with `f = F_s ∘ i_s` (Theorem 2.3); it is
  constant on `S_M`-classes (`liftS_kernel`, by the criterion `sRelClosed_markov`, which is
  the paper's appeal to Corollary 3.5), so it induces `F_m` with `F_s = F_m ∘ (- / S_M)`;
  `F_m` is a strict Markov functor; it is the only one with `f = F_m ∘ i_m`.
* **Theorem 4.1** `theorem_4_1 : IsFreeMarkov (F_s(G) / S_M) G i_m`, under `JoyalStreet G`
  only.
-/
module

public import FreeMarkov.Stage3.Markov

@[expose] public section

universe w v u' v' u₁ v₁ u₂ v₂

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov

variable {S : Type w}

/-! ### Strict functors and `Arrow` -/

section Strict

variable {C : Type u₁} [Monoid C] [Category.{v₁} C] {D : Type u₂} [Monoid D] [Category.{v₂} D]

theorem StrictSMC.mk_braid_congr [StrictSMC D] {a b a' b' : D} (ha : a = a') (hb : b = b') :
    Arrow.mk (σ_ a b) = Arrow.mk (σ_ a' b') := by
  subst ha hb
  rfl

theorem StrictMarkov.mk_copy_congr [StrictMarkov D] {a a' : D} (ha : a = a') :
    Arrow.mk (δ_ a) = Arrow.mk (δ_ a') := by
  subst ha
  rfl

/-- A strict functor `F : C → D` into a strict Markov category sends the right-hand side
of (1.2) built from morphisms `d_a`, `d_b` of `C` that `F` sends to `δ_{F a}`, `δ_{F b}` to
`δ_{F(a ⊗ b)}`. -/
theorem StrictFunctor.map_copy_formula [StrictSMC C] [StrictMarkov D] (F : StrictFunctor C D)
    {a b : C} (da : a ⟶ a * a) (db : b ⟶ b * b)
    (ha : Arrow.mk (F.map da) = Arrow.mk (δ_ (F.obj a)))
    (hb : Arrow.mk (F.map db) = Arrow.mk (δ_ (F.obj b))) :
    Arrow.mk (F.map ((da ⊗ₛ db) ≫
      eqToHom (by simp only [mul_assoc] : a * a * (b * b) = a * (a * b) * b) ≫
      ((𝟙 a ⊗ₛ σ_ a b) ⊗ₛ 𝟙 b))) = Arrow.mk (δ_ (F.obj (a * b))) := by
  refine Eq.trans ?_ (StrictMarkov.mk_copy_congr (F.obj_mul a b)).symm
  refine Eq.trans ?_ (copy_tensor (F.obj a) (F.obj b)).symm
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map]
  refine Arrow.mk_comp_congr ((F.map_tensorHom _ _).trans (mk_tensorHom_congr ha hb)) ?_
  rw [Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_eqToHom_comp]
  refine (F.map_tensorHom _ _).trans (mk_tensorHom_congr ((F.map_tensorHom _ _).trans
    (mk_tensorHom_congr ?_ (F.map_braid a b))) ?_)
  · exact (congrArg Arrow.mk (F.map_id a))
  · exact (congrArg Arrow.mk (F.map_id b))

/-- A strict functor between strict Markov categories that matches the duplicates on `a`
and on `b` matches the duplicate on `a ⊗ b` (by (1.2) on both sides). -/
theorem StrictFunctor.map_copy_mul [StrictMarkov C] [StrictMarkov D] (F : StrictFunctor C D)
    {a b : C} (ha : Arrow.mk (F.map (δ_ a)) = Arrow.mk (δ_ (F.obj a)))
    (hb : Arrow.mk (F.map (δ_ b)) = Arrow.mk (δ_ (F.obj b))) :
    Arrow.mk (F.map (δ_ (a * b))) = Arrow.mk (δ_ (F.obj (a * b))) :=
  (F.toFunctor.mk_map_congr (copy_tensor a b)).trans (F.map_copy_formula _ _ ha hb)

/-- A strict functor between strict Markov categories matches the duplicate on `1`. -/
theorem StrictFunctor.map_copy_one [StrictMarkov C] [StrictMarkov D] (F : StrictFunctor C D) :
    Arrow.mk (F.map (δ_ (1 : C))) = Arrow.mk (δ_ (F.obj 1)) := by
  refine (F.toFunctor.mk_map_congr copy_one).trans ?_
  rw [F.map_id]
  refine (Arrow.mk_id_congr F.obj_one).trans ?_
  exact (copy_one.symm.trans (StrictMarkov.mk_copy_congr F.obj_one.symm))

end Strict

namespace JoyalStreet

variable {G : FreeDDGraphMonoid.{w, v} S} (J : JoyalStreet G.toFreeGraphMonoid)

/-! ### `i_s` and `i_m` -/

/-- `i_s : G → F_s(G)`, the obvious graph monoid homomorphism (Stage 1's `J.ι`). -/
noncomputable abbrev iS : G.toGraphMonoid.Hom (graphMonoid J.Fs) := J.ι

/-- `i_m = (- / S_M) ∘ i_s : G → F_s(G) / S_M`. -/
noncomputable def iM : G.toGraphMonoid.Hom (graphMonoid J.FsM) :=
  (J.quotProjStrict _ _).toGraphMonoidHom.comp J.iS

theorem iM_A (x : G.A) : J.iM.A x = Arrow.mk (J.projM.map (J.hom (DHom.gen x))) := rfl

theorem iM_V (a : FreeMonoid S) : J.iM.V a = J.wordM a := rfl

/-- "`i_m = (- / S_M) ∘ i_s` is a graph monoid homomorphism matching duplicates and
discards." -/
theorem iM_matches : G.MatchesDupDisc J.iM where
  dup x := by
    rw [iM_A, iM_V]
    change _ = Arrow.mk (J.copyM (J.wordM (FreeMonoid.of x)))
    rw [copyM_of]
    exact J.projM.mk_map_congr (J.arrow_eq_of_cls_eq rfl)
  disc x := by
    rw [iM_A, iM_V]
    change _ = Arrow.mk (J.discardM (J.wordM (FreeMonoid.of x)))
    rw [discardM_of]
    exact J.projM.mk_map_congr (J.arrow_eq_of_cls_eq rfl)

/-! ### `F_s` is constant on `S_M`-classes -/

section Lift

variable {D : Type u'} [Monoid D] [Category.{v'} D] [StrictMarkov D]
  (F : StrictFunctor J.Fs D)

/-- The pairs of classes on which a strict functor `F` out of `F_s(G)` takes the same value
(compared in `Arrow D`). -/
def kerRel (c d : DClass G.toFreeGraphMonoid) : Prop :=
  Arrow.mk (F.map (J.hom (DHom.ofClass c))) = Arrow.mk (F.map (J.hom (DHom.ofClass d)))

theorem kerRel_hom {a b : FreeMonoid S} (g : DHom G.toFreeGraphMonoid a b) :
    Arrow.mk (F.map (J.hom (DHom.ofClass g.1))) = Arrow.mk (F.map (J.hom g)) :=
  F.toFunctor.mk_map_congr (J.arrow_eq_of_cls_eq rfl)

theorem kerRel_tensor {c c' d d' : DClass G.toFreeGraphMonoid} (h₁ : J.kerRel F c c')
    (h₂ : J.kerRel F d d') : J.kerRel F (c.tensor d) (c'.tensor d') := by
  have e : ∀ c d : DClass G.toFreeGraphMonoid, Arrow.mk (F.map (J.hom (DHom.ofClass (c.tensor d)))) =
      Arrow.mk (F.map (J.hom (DHom.ofClass c)) ⊗ₛ F.map (J.hom (DHom.ofClass d))) := fun c d =>
    (F.toFunctor.mk_map_congr (J.arrow_eq_of_cls_eq (f := J.hom (DHom.ofClass (c.tensor d)))
      (g := J.hom (DHom.ofClass c) ⊗ₛ J.hom (DHom.ofClass d)) rfl)).trans (F.map_tensorHom _ _)
  exact (e c d).trans ((mk_tensorHom_congr h₁ h₂).trans (e c' d').symm)

theorem kerRel_comp {c c' d d' : DClass G.toFreeGraphMonoid} (h₁ : J.kerRel F c c')
    (h₂ : J.kerRel F d d') (h : c.cod = d.dom) (h' : c'.cod = d'.dom) :
    J.kerRel F (c.comp d) (c'.comp d') := by
  have e : ∀ (c d : DClass G.toFreeGraphMonoid) (h : c.cod = d.dom),
      Arrow.mk (F.map (J.hom (DHom.ofClass (c.comp d)))) =
        Arrow.mk (F.map (J.hom (DHom.ofClass c)) ≫
          F.map (J.hom ((DHom.ofClass d).cast h.symm rfl))) := fun c d h =>
    (F.toFunctor.mk_map_congr (J.arrow_eq_of_cls_eq
      (f := J.hom (DHom.ofClass (c.comp d)))
      (g := J.hom (DHom.ofClass c) ≫ J.hom ((DHom.ofClass d).cast h.symm rfl)) rfl)).trans
      (congrArg Arrow.mk (F.map_comp _ _))
  have e' : ∀ (d : DClass G.toFreeGraphMonoid) {a : FreeMonoid S} (h : d.dom = a),
      Arrow.mk (F.map (J.hom ((DHom.ofClass d).cast h rfl))) =
        Arrow.mk (F.map (J.hom (DHom.ofClass d))) := fun d a h =>
    F.toFunctor.mk_map_congr (J.arrow_eq_of_cls_eq rfl)
  refine (e c d h).trans ((Arrow.mk_comp_congr h₁ ?_).trans (e c' d' h').symm)
  exact (e' d h.symm).trans (h₂.trans (e' d' h'.symm).symm)

variable (f : G.toGraphMonoid.Hom (graphMonoid D)) (hf : G.MatchesDupDisc f)
  (hF : f = F.toGraphMonoidHom.comp J.iS)

include hF in
theorem liftS_gen (x : G.A) : Arrow.mk (F.map (J.hom (DHom.gen x))) = f.A x := by
  rw [hF]
  rfl

include hF in
theorem liftS_obj (a : FreeMonoid S) : F.obj (Fs.of J a) = f.V a := by
  rw [hF]
  rfl

include hf hF in
theorem liftS_dup (x : S) :
    Arrow.mk (F.map (J.hom (G.dupH x))) = Arrow.mk (δ_ (F.obj (Fs.of J (FreeMonoid.of x)))) :=
  ((J.kerRel_hom F (G.dupH x)).symm.trans ((J.kerRel_hom F (DHom.gen (G.dup x))).trans
    ((J.liftS_gen F f hF _).trans (hf.dup x)))).trans
    (StrictMarkov.mk_copy_congr (J.liftS_obj F f hF _).symm)

include hf hF in
theorem liftS_disc (x : S) :
    Arrow.mk (F.map (J.hom (G.discH x))) =
      Arrow.mk (ε_ (F.obj (Fs.of J (FreeMonoid.of x)))) := by
  refine ((J.kerRel_hom F (G.discH x)).symm.trans ((J.kerRel_hom F (DHom.gen (G.disc x))).trans
    ((J.liftS_gen F f hF _).trans (hf.disc x)))).trans ?_
  rw [J.liftS_obj F f hF]

theorem liftS_id (a : FreeMonoid S) :
    Arrow.mk (F.map (J.hom (DHom.id _ a))) = Arrow.mk (𝟙 (F.obj (Fs.of J a))) :=
  congrArg Arrow.mk (F.map_id _)

/-- Any two morphisms into the unit have the same image under a strict functor into a
strict Markov category (the unit is terminal). -/
theorem liftS_to_one {a : FreeMonoid S} (g g' : Fs.of J a ⟶ Fs.of J 1) :
    Arrow.mk (F.map g) = Arrow.mk (F.map g') := by
  rw [← Arrow.arrow_mk_comp_eqToHom (F.map g) F.obj_one,
    ← Arrow.arrow_mk_comp_eqToHom (F.map g') F.obj_one, eq_discard (F.map g ≫ _),
    eq_discard (F.map g' ≫ _)]

include hf hF in
/-- "`F_s` sends the two diagrams of each Markov template to the two sides of an instance
of one of the equalities (1.1), (1.3) in `D`; ... So `F_s` takes the same value on the two
diagrams." -/
theorem liftS_pair {c d : DClass G.toFreeGraphMonoid} (h : G.MarkovPair c d) :
    J.kerRel F c d := by
  have hd := J.liftS_dup F f hf hF
  have he := J.liftS_disc F f hf hF
  cases h with
  | coass x =>
    rw [G.mk_coassΩD, G.mk_coassΛD]
    refine (J.kerRel_hom F _).trans (Eq.trans ?_ (J.kerRel_hom F _).symm)
    refine (congrArg Arrow.mk (F.map_comp (J.hom (G.dupH x))
      (J.hom ((G.dupH x).tensor (DHom.id _ _))))).trans ?_
    refine Eq.trans ?_ (congrArg Arrow.mk (F.map_comp (J.hom (G.dupH x))
      (J.hom ((DHom.id _ _).tensor (G.dupH x))))).symm
    refine (Arrow.mk_comp_congr (hd x) ((F.map_tensorHom _ _).trans
      (mk_tensorHom_congr (hd x) (J.liftS_id F _)))).trans ?_
    refine Eq.trans ?_ (Arrow.mk_comp_congr (hd x) ((F.map_tensorHom _ _).trans
      (mk_tensorHom_congr (J.liftS_id F _) (hd x)))).symm
    exact copy_assoc _
  | counit x =>
    rw [G.mk_counitΩD]
    refine (J.kerRel_hom F _).trans (Eq.trans ?_
      (J.kerRel_hom F (DHom.id _ (FreeMonoid.of x))).symm)
    refine (congrArg Arrow.mk (F.map_comp (J.hom (G.dupH x))
      (J.hom ((DHom.id _ _).tensor (G.discH x))))).trans ?_
    refine (Arrow.mk_comp_congr (hd x) ((F.map_tensorHom _ _).trans
      (mk_tensorHom_congr (J.liftS_id F _) (he x)))).trans ?_
    exact (copy_discard _).trans (J.liftS_id F _).symm
  | counit' x =>
    rw [G.mk_counitΩ'D]
    refine (J.kerRel_hom F _).trans (Eq.trans ?_
      (J.kerRel_hom F (DHom.id _ (FreeMonoid.of x))).symm)
    refine (congrArg Arrow.mk (F.map_comp (J.hom (G.dupH x))
      (J.hom ((G.discH x).tensor (DHom.id _ _))))).trans ?_
    refine (Arrow.mk_comp_congr (hd x) ((F.map_tensorHom _ _).trans
      (mk_tensorHom_congr (he x) (J.liftS_id F _)))).trans ?_
    exact (discard_copy _).trans (J.liftS_id F _).symm
  | cocomm x =>
    rw [G.mk_cocommΩD]
    refine (J.kerRel_hom F _).trans (Eq.trans ?_ (J.kerRel_hom F (G.dupH x)).symm)
    refine (congrArg Arrow.mk (F.map_comp (J.hom (G.dupH x))
      (σ_ (Fs.of J (FreeMonoid.of x)) (Fs.of J (FreeMonoid.of x))))).trans ?_
    refine (Arrow.mk_comp_congr (hd x) (F.map_braid _ _)).trans ?_
    exact (congrArg Arrow.mk (copy_comm _)).trans (hd x).symm
  | nat x =>
    rw [G.mk_natΩD, G.mk_natΛD]
    exact (J.kerRel_hom F _).trans ((J.liftS_to_one F _ _).trans (J.kerRel_hom F _).symm)

include hf hF in
/-- "The pairs of morphisms on which `F_s` takes the same value form a monoidal congruence
relation on `F_s(G)`, and hence, by Corollary 3.5, we must have `F_s([Υ]) = F_s([Γ])` if
`[Υ] / S_M = [Γ] / S_M`." -/
theorem liftS_kernel {c d : DClass G.toFreeGraphMonoid} (h : SRel G.markovTemplates c d) :
    J.kerRel F c d :=
  (FreeDDGraphMonoid.sRelClosed_markov (K := J.kerRel F) (fun _ => rfl)
    (fun h h' => h.trans h') (J.kerRel_tensor F) (J.kerRel_comp F)
    (fun h => ⟨J.liftS_pair F f hf hF h, (J.liftS_pair F f hf hF h).symm⟩)).of_sRel h

include hf hF in
theorem liftS_map_eq {a b : FreeMonoid S} (g g' : DHom G.toFreeGraphMonoid a b)
    (h : SRel G.markovTemplates g.1 g'.1) : F.map (J.hom g) = F.map (J.hom g') :=
  Arrow.eq_of_mk_eq ((J.kerRel_hom F g).symm.trans
    ((J.liftS_kernel F f hf hF h).trans (J.kerRel_hom F g')))

/-- **`F_m`**: the strict symmetric monoidal functor `F_s(G) / S_M → D` induced by `F_s`. -/
noncomputable def liftM : StrictFunctor J.FsM D where
  obj a := F.obj a
  map {a b} φ := Quotient.lift (fun g => F.map (J.hom g)) (fun g g' h =>
    J.liftS_map_eq F f hf hF g g' h) φ
  map_id a := F.map_id _
  map_comp φ ψ := by
    induction φ using Quotient.ind
    induction ψ using Quotient.ind
    exact F.map_comp _ _
  obj_one := F.obj_one
  obj_mul a b := F.obj_mul a b
  map_tensorHom φ ψ := by
    induction φ using Quotient.ind
    induction ψ using Quotient.ind
    exact F.map_tensorHom _ _
  map_braid a b := F.map_braid a b

theorem liftM_projM {a b : J.Fs} (g : a ⟶ b) :
    (J.liftM F f hf hF).map (J.projM.map g) = F.map g := rfl

/-- `F_s = F_m ∘ (- / S_M)`. -/
theorem liftM_comp_proj :
    (J.liftM F f hf hF).comp (J.quotProjStrict _ _) = F :=
  StrictFunctor.ext fun _ => rfl

/-- `F_m` matches duplicates: "on the letters because `f` does, and then on all words because,
by (1.2), those on a word are expressed in the same way through those on its letters in
`F_s(G) / S_M` and in `D`." -/
theorem liftM_map_copy (a : J.FsM) :
    Arrow.mk ((J.liftM F f hf hF).map (δ_ a)) = Arrow.mk (δ_ ((J.liftM F f hf hF).obj a)) := by
  suffices h : ∀ l : List S, Arrow.mk ((J.liftM F f hf hF).map (δ_ (J.wordM
      (FreeMonoid.ofList l)))) = Arrow.mk (δ_ ((J.liftM F f hf hF).obj (J.wordM
      (FreeMonoid.ofList l)))) from h (FreeMonoid.toList (J.unword _ _ a))
  intro l
  induction l with
  | nil => exact (J.liftM F f hf hF).map_copy_one
  | cons x l ih =>
    refine (J.liftM F f hf hF).map_copy_mul (a := J.wordM (FreeMonoid.of x))
      (b := J.wordM (FreeMonoid.ofList l)) ?_ ih
    change Arrow.mk ((J.liftM F f hf hF).map (J.copyM (J.wordM (FreeMonoid.of x)))) = _
    rw [copyM_of]
    exact J.liftS_dup F f hf hF x

/-- `F_m` is a strict Markov functor. -/
noncomputable def liftMarkov : StrictMarkovFunctor J.FsM D :=
  StrictMarkovFunctor.ofMapCopy (J.liftM F f hf hF) (J.liftM_map_copy F f hf hF)

end Lift

/-! ### Theorem 4.1 -/

theorem toGraphMonoidHom_comp {D : Type u'} [Monoid D] [Category.{v'} D] [StrictSMC D]
    (F : StrictFunctor J.FsM D) :
    F.toGraphMonoidHom.comp J.iM = (F.comp (J.quotProjStrict _ _)).toGraphMonoidHom.comp J.iS :=
  rfl

/-- **Theorem 4.1.** "The quotient category `F_s(G) / S_M` is the free Markov category over
`G`": `i_m : G → F_s(G) / S_M` matches duplicates and discards, and for every strict Markov
category `D` and every graph monoid homomorphism `f : G → D` matching duplicates and
discards there is exactly one strict Markov functor `F_m : F_s(G) / S_M → D` with
`f = F_m ∘ i_m`.  The only cited result used is C1 (`JoyalStreet G`). -/
theorem theorem_4_1 : IsFreeMarkov.{w, v, max w v, w, v', u'} J.FsM G J.iM where
  matchesDupDisc := J.iM_matches
  existsUnique_lift D _ _ _ f hf := by
    obtain ⟨F, hF, huniq⟩ := J.isFreeSymmetric.existsUnique_lift D f
    refine ⟨J.liftMarkov F f hf hF, ?_, fun F' hF' => ?_⟩
    · change f = (J.liftM F f hf hF).toGraphMonoidHom.comp J.iM
      rw [toGraphMonoidHom_comp, liftM_comp_proj]
      exact hF
    · have h₁ : F'.toStrictFunctor.comp (J.quotProjStrict _ _) = F := by
        exact huniq _ hF'
      refine StrictMarkovFunctor.ext_toStrictFunctor (StrictFunctor.ext fun {a b} φ => ?_)
      induction φ using Quotient.ind with
      | _ g =>
      change Arrow.mk ((F'.toStrictFunctor.comp (J.quotProjStrict _ _)).map (J.hom g)) =
        Arrow.mk (F.map (J.hom g))
      rw [h₁]

end JoyalStreet

end FreeMarkov
