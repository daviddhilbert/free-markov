/-
Free Markov categories, Stage 5: effects as values of diagrams in `C` (the literal form of
Definition 5.4 and of the first claim of Remark 5.7).

For a production signature `Q`, objects `obj x` of a strict Markov category `C` for the letters and
morphisms `κ p` for the producers, `ProdSig.relabelTo` relabels a diagram of `Q.G` into a diagram in
`C` (Definition 2.1, diagrams in `C`): an edge with the letter `x` gets the value `obj x`, a duplicate
or discard on `x` the duplicate or discard on `obj x`, a node of the producer `p` the morphism `κ p`.

* `ProdSig.value_relabel`: the value (Section 2, through C1 for `G_C`) of the relabelled diagram is
  the image of its class under the functor `F : F_s(Q.G)/S_M → C` of Theorem 4.1.
* `EffData.effect_eq_value`: **Definition 5.4, literally.** For every effect diagram `Γ` of `W(K)`,
  its image in `C` (the diagram `Γ_{[w_T ‖ w_S]}` of Definition 5.4 with the multipliers in binary
  form) represents the effect `[w_T ‖ w_S]_{(W,K)}`.
* `value_copy_diagram`: **Remark 5.7.** "A diagram from `w` to `w^m`, with `m` edges in its codomain,
  all of whose nodes are copies on `w` ... represents the `m`-fold copy on `w`, because it is the
  image under `F` of a diagram from `a` to `a^m`; this holds however the edges in its codomain are
  ordered" (in binary form).

The cited result C1 is used for `Q.G` and for `G_C`.
-/
module

public import FreeMarkov.Stage5.Strictification

@[expose] public section

universe v u

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov JoyalStreet FreeGraphMonoid

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C]

omit [Category.{v} C] [StrictMarkov C] in
theorem evalWord_map {X : Type*} (obj : X → C) (w : FreeMonoid X) :
    evalWord (FreeMonoid.map obj w) = FreeMonoid.lift obj w := by
  have : (FreeMonoid.lift (_root_.id : C → C)).comp (FreeMonoid.map obj) = FreeMonoid.lift obj :=
    FreeMonoid.hom_eq fun x => by simp
  exact DFunLike.congr_fun this w

namespace ProdSig

variable (Q : ProdSig) (obj : Q.X → C) (κ : ∀ p, FreeMonoid.lift obj (Q.src p) ⟶ obj (Q.out p))

/-- The relabelling of `Q.G` into `G_C` given by `obj` and `κ`. -/
noncomputable def relabelTo : Q.G.toFreeGraphMonoid.Relabel (graphOf C) where
  onS := obj
  onA x := ⟨FreeMonoid.map obj (Q.G.s x), FreeMonoid.map obj (Q.G.t x),
    eqToHom ((evalWord_map obj _).trans ((Q.toHom obj κ).s_A x).symm) ≫ ((Q.toHom obj κ).A x).hom ≫
      eqToHom (((Q.toHom obj κ).t_A x).trans (evalWord_map obj _).symm)⟩
  s_onA _ := rfl
  t_onA _ := rfl

variable {Q} (J : JoyalStreet Q.G.toFreeGraphMonoid) (JC : JoyalStreet (graphOf C))

/-- The value in `C` of a diagram of `Q.G` relabelled by `obj`, `κ` is the image of its class under
the strict Markov functor `F : F_s(Q.G)/S_M → C` given by Theorem 4.1. -/
theorem value_relabel {N E : Type*} [Finite N] [Finite E] (Γ : Diagram Q.G.toFreeGraphMonoid N E) :
    Arrow.mk (valueFree JC (Γ.relabel (Q.relabelTo obj κ))) =
      Arrow.mk ((J.lift (Q.toHom obj κ) (Q.toHom_matches obj κ)).map
        (J.projM.map (J.hom (DHom.mk Γ)))) := by
  set φ := Q.relabelTo obj κ
  set F := J.lift (Q.toHom obj κ) (Q.toHom_matches obj κ)
  set m := (J.equiv _ _).symm (DHom.mk Γ)
  -- the class of the relabelled diagram is the image of `m` under `Syn(φ)`
  have h₁ : Arrow.mk ((JC.equiv _ _).symm (DHom.mk (Γ.relabel φ))) = Arrow.mk (φ.synMap.map m) := by
    refine (JC.arrow_eq_of_val_eq (φ.synMap.map m) (DHom.mk (Γ.relabel φ)) ?_).symm
    rw [JoyalStreet.val_synMap J JC φ m, Equiv.apply_symm_apply]
    exact DClass.mk_relabel _ _
  -- the two strict functors `Syn_s(Q.G) → C` agree on generators
  have h₂ : (Syn.lift (evalHom C)).comp φ.synMap =
      F.toStrictFunctor.comp ((J.quotProjStrict _ _).comp J.toFsStrict) := by
    have e₁ : (Syn.lift (evalHom C)).comp φ.synMap = Syn.lift (Q.toHom obj κ) := by
      refine Syn.eq_lift _ ?_
      change (Syn.lift (evalHom C)).toGraphMonoidHom.comp (φ.synMap.toGraphMonoidHom.comp (Syn.ι _)) = _
      rw [FreeGraphMonoid.Relabel.synMap, Syn.lift_comp_ι]
      refine GraphMonoid.Hom.ext ?_ (funext fun x => ?_)
      · refine FreeMonoid.hom_eq fun x => ?_
        have h := congrArg (fun g => g.V (FreeMonoid.of (obj x))) (Syn.lift_comp_ι (evalHom C))
        refine h.trans ?_
        simp [evalHom, ProdSig.toHom]
      · change Arrow.mk ((Syn.lift (evalHom C)).map (Syn.gen _)) = _
        refine (Syn.arrow_interp_gen (evalHom C) _).trans ?_
        exact arrow_mk_cast _ _ _
    have e₂ : F.toStrictFunctor.comp ((J.quotProjStrict _ _).comp J.toFsStrict) =
        Syn.lift (Q.toHom obj κ) := by
      refine Syn.eq_lift _ ?_
      have hs := lift_spec (J := J) (Q.toHom obj κ) (Q.toHom_matches obj κ)
      conv_rhs => rw [hs]
      change F.toGraphMonoidHom.comp (((J.quotProjStrict _ _).comp J.toFsStrict).toGraphMonoidHom.comp
        (Syn.ι _)) = F.toGraphMonoidHom.comp J.iM
      congr 1
      change (J.quotProjStrict _ _).toGraphMonoidHom.comp (J.toFsStrict.toGraphMonoidHom.comp (Syn.ι _)) =
        (J.quotProjStrict _ _).toGraphMonoidHom.comp J.ι
      rw [J.toFsStrict_comp_ι]
    rw [e₁, e₂]
  have h₃ : J.toFsStrict.map m = J.hom (DHom.mk Γ) := by
    change J.equiv _ _ m = _
    exact Equiv.apply_symm_apply _ _
  unfold valueFree
  refine ((Syn.lift (evalHom C)).toFunctor.mk_map_congr h₁).trans ?_
  change Arrow.mk (((Syn.lift (evalHom C)).comp φ.synMap).map m) = _
  rw [h₂]
  change Arrow.mk (F.map ((J.quotProjStrict _ _).map (J.toFsStrict.map m))) = _
  rw [h₃]
  rfl

end ProdSig

/-! ### Definition 5.4 as the value of a diagram in `C` -/

namespace EffData

variable {n : ℕ} (D : EffData C n) (J : JoyalStreet D.sig.G.toFreeGraphMonoid)
  (JC : JoyalStreet (graphOf C))

/-- **Definition 5.4, literally.** "Construct a diagram in `M` ... [the morphism that it represents]
is referred to as the `(W, K)`-effect of `w_S` on `w_T`": the image in `C` of any effect diagram `Γ`
of `W(K)` (nodes `κ_i` valued `κ_i`, duplicates and discards on `i` valued those on `w_i`) has the
value `[w_T ‖ w_S]_{(W,K)}`. -/
theorem effect_eq_value {S T : Finset (Fin n)} {N E : Type*} [Finite N] [Finite E]
    {Γ : Diagram D.sig.G.toFreeGraphMonoid N E} (hΓ : EffSig.IsEffectDiagram S T Γ) :
    Arrow.mk (valueFree JC (Γ.relabel (D.sig.relabelTo D.w D.κ))) = Arrow.mk (D.effect J S T) := by
  refine (ProdSig.value_relabel D.w D.κ J JC Γ).trans ?_
  rw [arrow_effect]
  change Arrow.mk ((D.functor J).map (J.projM.map (J.hom (DHom.mk Γ)))) = _
  let f : Fs.of J (finWord S) ⟶ Fs.of J (finWord T) := J.hom ((DHom.mk Γ).cast hΓ.dom hΓ.cod)
  have hf : J.cls f = DClass.mk Γ := rfl
  have e : Arrow.mk (J.hom (DHom.mk Γ)) = Arrow.mk f := J.arrow_eq_of_cls_eq rfl
  rw [(D.functor J).toFunctor.mk_map_congr (J.projM.mk_map_congr e)]
  rw [EffSig.projM_eq_freeEffect ((EffSig.isEffectDiagram_iff hf).2 hΓ)]

end EffData

/-! ### Remark 5.7 for diagrams of copies -/

/-- **Remark 5.7.** A diagram of `G_a` from `a` to `a^m` (its nodes are duplicates and discards on
`a`, the binary form of a diagram of copies), relabelled along `a ↦ w`, has the value `copyN w m`,
however the edges in its codomain are ordered. -/
theorem value_copy_diagram (J : JoyalStreet (ProdSig.free Unit).G.toFreeGraphMonoid)
    (JC : JoyalStreet (graphOf C)) (w : C) (m : ℕ) {N E : Type*} [Finite N] [Finite E]
    (Γ : Diagram (ProdSig.free Unit).G.toFreeGraphMonoid N E) (hd : Γ.domWord = oneLetter)
    (hc : Γ.codWord = oneLetter ^ m) :
    Arrow.mk (valueFree JC (Γ.relabel ((ProdSig.free Unit).relabelTo (fun _ => w) fun p => p.elim))) =
      Arrow.mk (copyN w m) := by
  refine (ProdSig.value_relabel _ _ J JC Γ).trans ?_
  change Arrow.mk ((copyFunctor J w).map (J.projM.map (J.hom (DHom.mk Γ)))) = _
  have e : Arrow.mk (J.hom (DHom.mk Γ)) = Arrow.mk (J.hom ((DHom.mk Γ).cast hd hc)) :=
    J.arrow_eq_of_cls_eq rfl
  rw [(copyFunctor J w).toFunctor.mk_map_congr (J.projM.mk_map_congr e)]
  exact remark_5_7_copy J w m _

end FreeMarkov
