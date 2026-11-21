/-
Free Markov categories, Stage 8: Proposition 5.6 for Markov functors into arbitrary Markov
categories (item (e)).

For a family `K = (S_i)` (Stage 5's `EffSig`, e.g. the parents in an ordered DAG, Section 6), its
free Markov category `J.FsM` (`Cau(G)` in Section 6), a Markov category `M` with a strictification
`T : Strictification M Str` (C2), and a Markov functor `F : J.FsM → M`:

* `EffSig.markovData J T F`: the data of an effect in `M` (Stage 5's `Strictification.MData`) formed
  from the objects `F(i)` and the morphisms `F(κ_i)` read through the structure isomorphisms of `F`
  and of `eval`: `κ_i^M = ψ⁻¹ ∘ φ ∘ F(κ_i) : eval(w_{S_i}) → F(i)`.
* `EffSig.prop_5_6_markov`: **(e)** `F([w_T ‖ w_S]) = φ_T ∘ ψ_T⁻¹ ∘ [T ‖ S]^M ∘ ψ_S ∘ φ_S⁻¹`, where
  `[T ‖ S]^M` is the effect in `M` (end of Section 5, `MData.effect`), `φ_w : lp (F ∘ letter) w ≅ F(w)`
  the comparison isomorphism of `F` (built from its `μ`, `ε`) and `ψ_w` that of `eval`.
* `EffSig.prop_5_6_markov_arrow`: the same as an equation of arrows of `M` when `F` is the identity on
  the letters up to the structure isomorphisms.

The proof uses items (b) and (c): `F` is isomorphic, by a monoidal natural isomorphism whose
components on the letters are identities, to `eval ∘ F_I` for its restriction `I`, and for the
strict functor `F_I` this is Stage 5's Proposition 5.6 (through the uniqueness in Theorem 4.1).

The cited results used: C1 (`J`) and C2 (`T`).
-/
module

public import FreeMarkov.Stage8.Equivalence

@[expose] public section

universe u v'

namespace FreeMarkov

open CategoryTheory MonoidalCategory ComonObj Category StrictSMC StrictMarkov JoyalStreet

variable {M : Type u} [Category.{v'} M] [MonoidalCategory M] [MarkovCategory M]
  {Str : Type u} [Monoid Str] [Category.{v'} Str] [StrictMarkov Str]

/-! ### Components of a monoidal natural transformation that is the identity on letters -/

namespace JoyalStreet

variable {S : Type} {G : FreeDDGraphMonoid.{0, 0} S} (J : JoyalStreet G.toFreeGraphMonoid)

theorem app_of_eqToHom {F₁ F₂ : MarkovFun J.FsM M} (θ : F₁ ⟶ F₂)
    (h : ∀ a, F₁.obj (J.letterM a) = F₂.obj (J.letterM a))
    (hθ : ∀ a, θ.nat.app (J.letterM a) = eqToHom (h a)) (w : FreeMonoid S) :
    θ.nat.app (J.wordM w) = ((J.cmpW F₁ w).inv ≫
      eqToHom (congrArg (fun o => lp o w) (funext h))) ≫ (J.cmpW F₂ w).hom := by
  have hn := J.cmpW_naturality θ w
  have hf : (fun a => θ.nat.app (J.letterM a)) = fun a => eqToHom (congrFun (funext h) a) :=
    funext hθ
  rw [hf, lpMap_eqToHom (funext h), ← Iso.eq_inv_comp] at hn
  rw [hn, assoc]

theorem lift_congr {D : Type*} [Monoid D] [Category D] [StrictMarkov D]
    {f₁ f₂ : G.toGraphMonoid.Hom (graphMonoid D)} (h : f₁ = f₂) (hf₁ : G.MatchesDupDisc f₁)
    (hf₂ : G.MatchesDupDisc f₂) : J.lift f₁ hf₁ = J.lift f₂ hf₂ := by
  subst h; rfl

end JoyalStreet

namespace EffSig

variable {n : ℕ} (K : EffSig n) (J : JoyalStreet K.sig.G.toFreeGraphMonoid) (T : Strictification M Str)

/-- The data of an effect in `M` formed from a Markov functor `F : F_s(W(K))/S_M → M`: the objects
`F(i)` and the morphisms `κ_i^M = ψ_{S_i}⁻¹ ∘ φ_{S_i} ∘ F(κ_i) : eval(w_{S_i}) → F(i)`, i.e. `F(κ_i)`
read through the structure isomorphisms of `F` (`φ`) and of `eval` (`ψ`). -/
noncomputable def markovData (F : MarkovFun J.FsM M) : Strictification.MData T n where
  toEffSig := K
  a i := F.obj (J.letterM i)
  κ i := (T.psiW (fun j => F.obj (J.letterM j)) (finWord (K.pa i))).inv ≫
    (J.restrictObj F).ar (.mech i)

variable {K J T}

theorem markovData_κ (F : MarkovFun J.FsM M) (i : Fin n) :
    (K.markovData J T F).κ i = (T.psiW (fun j => F.obj (J.letterM j)) (finWord (K.pa i))).inv ≫
      (J.cmpW F (finWord (K.pa i))).hom ≫ F.map (J.genM (.mech i)) :=
  congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) (J.cmpW_of_inv F i)).trans
    (comp_id _))))

theorem psiW_of_hom (ob : Fin n → M) (i : Fin n) :
    (T.psiW ob (FreeMonoid.of i)).hom = eqToHom (T.eval_letter (ob i)).symm := by
  apply Arrow.eq_of_mk_eq
  rw [T.arrow_psiW_hom, show (FreeMonoid.toList (FreeMonoid.of i)).reverse = [i] from rfl,
    cmpR_single_hom]
  refine Eq.trans ?_ (Arrow.mk_eqToHom _).symm
  exact Arrow.mk_id_congr (T.eval_letter (ob i))

/-- The homomorphism `W(K) → str(M)` of the restriction of `F` is the one given by the data
`markovData` (Stage 5's `ProdSig.toHom`). -/
theorem toHom_eq (F : MarkovFun J.FsM M) :
    K.sig.toHom (K.markovData J T F).toEffData.w (K.markovData J T F).toEffData.κ =
      (J.restrictObj F).toStrHom T := by
  refine GraphMonoid.Hom.ext rfl (funext fun x => ?_)
  rcases x with i | i | i
  · exact (((J.restrictObj F).toStrHom_matches T).dup i).symm
  · exact (((J.restrictObj F).toStrHom_matches T).disc i).symm
  · have key : (K.markovData J T F).κ i ≫
        eqToHom (T.eval_letter ((K.markovData J T F).a i)).symm =
        (T.psiW (J.restrictObj F).ob (finWord (K.pa i))).inv ≫ (J.restrictObj F).ar (.mech i) ≫
          (T.psiW (J.restrictObj F).ob (FreeMonoid.of i)).hom := by
      rw [psiW_of_hom]
      exact assoc _ _ _
    exact congrArg (fun f => Arrow.mk (T.evalFun.toFunctor.preimage f)) key

theorem functor_eq (F : MarkovFun J.FsM M) :
    (K.markovData J T F).toEffData.functor J = J.liftStr T (J.restrictObj F) := by
  exact J.lift_congr (toHom_eq F) _ _

/-- **(e)** *Proposition 5.6 for Markov functors into an arbitrary Markov category.* For a Markov
functor `F : F_s(W(K))/S_M → M` (e.g. a model `F : Cau(G) → M`),
`F([w_T ‖ w_S])` is the effect `[T ‖ S]^M` in `M` (end of Section 5) formed from the objects `F(i)`
and the morphisms `F(κ_i)` read through `μ`, conjugated by the comparison isomorphisms
`φ_w : F(a_1) ⊗ … ⊗ F(a_n) ≅ F(a_1 … a_n)` of `F` and `ψ_w` of `eval`. -/
theorem prop_5_6_markov (F : MarkovFun J.FsM M) (S T' : Finset (Fin n)) :
    F.map (EffSig.freeEffect J S T') =
      (J.cmpW F (finWord S)).inv ≫ (T.psiW (fun j => F.obj (J.letterM j)) (finWord S)).hom ≫
        (K.markovData J T F).effect J S T' ≫
        (T.psiW (fun j => F.obj (J.letterM j)) (finWord T')).inv ≫ (J.cmpW F (finWord T')).hom := by
  set I := J.restrictObj F
  let e := J.restrict_realize T I
  let θ : J.realize T I ≅ F := J.restrict.preimageIso e
  have hθh : J.restrict.map θ.hom = e.hom := J.restrict.map_preimage _
  have hθi : J.restrict.map θ.inv = e.inv := J.restrict.map_preimage _
  -- the effect in `M` is `eval ∘ F_I` of the free effect
  have hA : Arrow.mk ((K.markovData J T F).effect J S T') =
      Arrow.mk ((J.realize T I).map (EffSig.freeEffect J S T')) := by
    unfold Strictification.MData.effect
    refine T.evalFun.toFunctor.mk_map_congr ?_
    refine (EffData.arrow_effect (K.markovData J T F).toEffData J S T').trans ?_
    rw [functor_eq]
    rfl
  -- the components of `θ` on words
  have hs : Arrow.mk (θ.inv.nat.app (J.wordM (finWord S))) =
      Arrow.mk ((J.cmpW F (finWord S)).inv ≫ (T.psiW I.ob (finWord S)).hom) := by
    rw [J.app_of_eqToHom θ.inv (fun a => (J.realize_letter T I a).symm) (fun a => ?_)]
    · exact Arrow.mk_comp_congr (Arrow.arrow_mk_comp_eqToHom _ _) (J.arrow_cmpW_realize T I _)
    · change (J.restrict.map θ.inv).app a = _
      rw [hθi]; rfl
  have ht : Arrow.mk (θ.hom.nat.app (J.wordM (finWord T'))) =
      Arrow.mk ((T.psiW I.ob (finWord T')).inv ≫ (J.cmpW F (finWord T')).hom) := by
    rw [J.app_of_eqToHom θ.hom (J.realize_letter T I) (fun a => ?_)]
    · exact Arrow.mk_comp_congr ((Arrow.arrow_mk_comp_eqToHom _ _).trans
        (arrow_inv_congr (J.arrow_cmpW_realize T I _))) rfl
    · change (J.restrict.map θ.hom).app a = _
      rw [hθh]; rfl
  have hF : F.map (EffSig.freeEffect J S T') = θ.inv.nat.app _ ≫
      (J.realize T I).map (EffSig.freeEffect J S T') ≫ θ.hom.nat.app _ := by
    have h1 := θ.inv.nat.naturality (EffSig.freeEffect J S T')
    have h2 := MarkovFun.inv_hom_app θ (J.projM.obj (Fs.of J (finWord T')))
    calc F.map (EffSig.freeEffect J S T')
        = F.map (EffSig.freeEffect J S T') ≫ θ.inv.nat.app _ ≫ θ.hom.nat.app _ := by
          rw [h2, comp_id]
      _ = _ := by
          rw [← assoc]
          erw [h1]
          rw [assoc]
  refine Arrow.eq_of_mk_eq ?_
  rw [hF]
  refine (arrow_comp_congr3 hs hA.symm ht).trans ?_
  simp only [assoc]
  rfl

end EffSig

end FreeMarkov
