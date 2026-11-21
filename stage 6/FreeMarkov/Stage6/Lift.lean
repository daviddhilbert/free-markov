/-
Free Markov categories, Stage 6: the substitution of diagrams for nodes behind the proof of
Proposition 6.6 (PLAN.md, Section 6, row "Proposition 6.6": "substitution of diagrams for nodes is
the functor induced by C1").

For `φ : H → G` in `FinODAG`, `JG : G.JS`, `JH : H.JS`:

* `subst φ JG JH : F_s(W(G)) → F_s(W(H))`, the strict symmetric monoidal functor given by Theorem 2.3
  (C1) that sends the letter `y` to the word `φ⁻¹(y)`, the duplicate and the discard on `y` to the
  duplicates and the discards on the letters of `φ⁻¹(y)` (`copyW`, `discW` of Stage 5), and the
  causal mechanism `κ_y` to an effect diagram `B_y` of `[φ⁻¹(y) ‖ φ⁻¹(pa(y))]_{(V_H, K_H)}`.  On a
  diagram `Γ_G` this is the diagram `Γ_{φ^* G}` of the proof of Proposition 6.6: every edge with the
  value `y` is replaced by the edges of `φ⁻¹(y)`, the duplicates and discards on `y` by those on
  `φ⁻¹(y)`, and the node `κ_y` by the block `B_y`.
* `card_subst`: the number of nodes `κ_x` of `subst(f)` is the number of nodes `κ_{φ(x)}` of `f`
  ("the nodes of `B_y` are one node with the value `κ_x` for each `x ∈ φ⁻¹(y)`, duplicates, and
  discards").
* `refine_projM`: `φ^* ∘ [−]_M = [−]_M ∘ subst` ("so `Γ_{φ^* G}` represents `φ^*([w ‖ v])`").
* `projM_copyW`, `projM_discW`: the duplicates and discards on the letters of a word represent
  `δ_a`, `ε_a` in `F_s(G)/S_M`.

The cited result C1 enters through `JG` and `JH`.
-/
module

public import FreeMarkov.Stage6.Refinement

@[expose] public section

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov JoyalStreet Relation

/-! ### Words of duplicates and discards in `F_s(Q.G)/S_M` -/

theorem _root_.CategoryTheory.Functor.mk_map_eqToHom_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {a a' : C} {c : D} (h : a = a') (g : F.obj a' ⟶ c) :
    Arrow.mk (F.map (eqToHom h) ≫ g) = Arrow.mk g := by
  subst h; simp

theorem _root_.CategoryTheory.Functor.mk_map_cast5 {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {a a' b b' c c' : C} (h₁ : a = a') (T : a' ⟶ b) (h₂ : b = b') (U : b' ⟶ c)
    (h₃ : c = c') :
    Arrow.mk (F.map (eqToHom h₁ ≫ T ≫ eqToHom h₂ ≫ U ≫ eqToHom h₃)) =
      Arrow.mk (F.map T ≫ eqToHom (congrArg F.obj h₂) ≫ F.map U) := by
  subst h₁ h₂ h₃; simp

namespace ProdSig

variable {Q : ProdSig} (J : JoyalStreet Q.G.toFreeGraphMonoid)

theorem projM_dupF (x : Q.X) :
    Arrow.mk (J.projM.map (EffSig.dupF J x)) = Arrow.mk (δ_ (J.wordM (FreeMonoid.of x))) :=
  J.iM_matches.dup x

/-- The duplicates on the letters of a word, built as in `copyW`, represent `δ_a`. -/
theorem projM_copyW : ∀ l : List Q.X,
    Arrow.mk (J.projM.map (EffSig.copyW J l)) = Arrow.mk (δ_ (J.wordM (FreeMonoid.ofList l)))
  | [] => by
    rw [EffSig.copyW, EffSig.castF, eqToHom_map, Arrow.mk_eqToHom]
    exact copy_one.symm
  | x :: l => by
    have ih := projM_copyW l
    have hd := projM_dupF J x
    rw [EffSig.copyW]
    unfold EffSig.castF
    refine (Functor.mk_map_cast5 J.projM (EffSig.eCons J x l) (EffSig.dupF J x ⊗ₛ EffSig.copyW J l)
      (EffSig.eAssoc₁ J x l) _ (EffSig.eAssoc₂ J x l)).trans ?_
    change _ = Arrow.mk (δ_ (J.wordM (FreeMonoid.of x) * J.wordM (FreeMonoid.ofList l)))
    rw [copy_tensor]
    refine Arrow.mk_comp_congr ?_ ?_
    · change Arrow.mk (J.projM.map (EffSig.dupF J x) ⊗ₛ J.projM.map (EffSig.copyW J l)) = _
      exact mk_tensorHom_congr hd ih
    · rw [Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_eqToHom_comp]
      exact (tensorHom_assoc (𝟙 (J.wordM (FreeMonoid.of x)))
        (σ_ (J.wordM (FreeMonoid.of x)) (J.wordM (FreeMonoid.ofList l)))
        (𝟙 (J.wordM (FreeMonoid.ofList l)))).symm

/-- The discards on the letters of a word represent `ε_a`. -/
theorem projM_discW (l : List Q.X) :
    Arrow.mk (J.projM.map (EffSig.discW J l)) = Arrow.mk (ε_ (J.wordM (FreeMonoid.ofList l))) :=
  congrArg Arrow.mk (eq_discard _)

end ProdSig

namespace FinODAG

variable {H G : FinODAG} (φ : H ⟶ G) (JG : G.JS) (JH : H.JS)

/-! ### The graph monoid homomorphism `W(G) → F_s(W(H))` -/

/-- The word `φ⁻¹(y)` as an object of `F_s(W(H))`. -/
noncomputable abbrev objF (y : Fin G.n) : JH.Fs := Fs.of JH (finWord (fiber φ y))

/-- The list of the letters of `φ⁻¹(y)`. -/
noncomputable abbrev fibL (y : Fin G.n) : List (Fin H.n) := (fiber φ y).sort (· ≤ ·)

theorem lift_objF (v : FreeMonoid (Fin G.n)) :
    FreeMonoid.lift (objF φ JH) v = Fs.of JH (preimW φ v) := by
  induction v using FreeMonoid.inductionOn' with
  | one => rfl
  | of_mul y v ih =>
    rw [map_mul, ih, preimW_mul, FreeMonoid.lift_eval_of, preimW_of]
    rfl

/-- The block `B_y`: an effect diagram of `[φ⁻¹(y) ‖ φ⁻¹(pa(y))]_{(V_H, K_H)}` (Definition 5.4). -/
noncomputable def block (y : Fin G.n) :
    Fs.of JH (finWord (preimS φ (G.pa y))) ⟶ Fs.of JH (finWord (fiber φ y)) :=
  Classical.choose (EffSig.exists_effect JH (preimS φ (G.pa y)) (fiber φ y))

theorem block_isEffect (y : Fin G.n) : EffSig.IsEffect JH (block φ JH y) :=
  Classical.choose_spec (EffSig.exists_effect JH (preimS φ (G.pa y)) (fiber φ y))

/-- The values of the substitution on the generators of `W(G)`. -/
noncomputable def substGen : G.W.A → Arrow JH.Fs
  | .dup y => Arrow.mk (EffSig.copyW JH (fibL φ y))
  | .disc y => Arrow.mk (EffSig.discW JH (fibL φ y))
  | .mech y => Arrow.mk (block φ JH y)

/-- The graph monoid homomorphism `W(G) → F_s(W(H))`: `y ↦ φ⁻¹(y)`, the duplicate and the discard on
`y` to those on the letters of `φ⁻¹(y)`, `κ_y ↦ B_y`. -/
noncomputable def substHom : G.W.toGraphMonoid.Hom (graphMonoid JH.Fs) where
  V := FreeMonoid.lift (objF φ JH)
  A := substGen φ JH
  s_A := by
    rintro (y | y | y)
    · change _ = FreeMonoid.lift (objF φ JH) (FreeMonoid.of y)
      rw [FreeMonoid.lift_eval_of]; rfl
    · change _ = FreeMonoid.lift (objF φ JH) (FreeMonoid.of y)
      rw [FreeMonoid.lift_eval_of]; rfl
    · change _ = FreeMonoid.lift (objF φ JH) (finWord (G.pa y))
      rw [lift_objF, preimW_finWord]; rfl
  t_A := by
    rintro (y | y | y)
    · change _ = FreeMonoid.lift (objF φ JH) (FreeMonoid.of y * FreeMonoid.of y)
      rw [map_mul, FreeMonoid.lift_eval_of]; rfl
    · change _ = FreeMonoid.lift (objF φ JH) 1
      rw [map_one]; rfl
    · change _ = FreeMonoid.lift (objF φ JH) (FreeMonoid.of y)
      rw [FreeMonoid.lift_eval_of]; rfl

/-! ### The substitution functor -/

theorem exists_subst : ∃! F : StrictFunctor JG.Fs JH.Fs, substHom φ JH = F.toGraphMonoidHom.comp JG.ι :=
  JG.isFreeSymmetric.existsUnique_lift JH.Fs (substHom φ JH)

/-- The substitution `F_s(W(G)) → F_s(W(H))` of the blocks for the nodes (Theorem 2.3). -/
noncomputable def subst : StrictFunctor JG.Fs JH.Fs := Classical.choose (exists_subst φ JG JH)

theorem subst_spec : substHom φ JH = (subst φ JG JH).toGraphMonoidHom.comp JG.ι :=
  (Classical.choose_spec (exists_subst φ JG JH)).1

theorem subst_obj (v : FreeMonoid (Fin G.n)) :
    (subst φ JG JH).obj (Fs.of JG v) = Fs.of JH (preimW φ v) := by
  have h := congrArg (fun f => f.V v) (subst_spec φ JG JH)
  exact h.symm.trans (lift_objF φ JH v)

theorem subst_gen (x : G.W.A) :
    Arrow.mk ((subst φ JG JH).map (JG.hom (DHom.gen x))) = substGen φ JH x := by
  have h := congrArg (fun f => f.A x) (subst_spec φ JG JH)
  exact h.symm

/-! ### Counting nodes -/

variable {JH} in
theorem card_eq_of_arrow {Q : ProdSig} {J : JoyalStreet Q.G.toFreeGraphMonoid} (k : Q.G.A)
    {a b a' b' : J.Fs} {f : a ⟶ b} {g : a' ⟶ b'} (h : Arrow.mk f = Arrow.mk g) :
    J.card k f = J.card k g := by
  obtain ⟨rfl, rfl, rfl⟩ := (Arrow.mk_eq_mk_iff _ _).1 h
  simp

open Classical in
/-- The nodes `κ_x` of the substituted diagram: one for each node `κ_{φ(x)}` of the original one. -/
theorem card_subst (x : Fin H.n) {a b : JG.Fs} (f : a ⟶ b) :
    JH.card (.mech x) ((subst φ JG JH).map f) = JG.card (.mech (φ.onV x)) f := by
  refine JG.induction (P := fun {a b} f =>
    JH.card (.mech x) ((subst φ JG JH).map f) = JG.card (.mech (φ.onV x)) f) ?_ ?_ ?_ ?_ ?_ f
  · intro g
    rw [card_eq_of_arrow _ (subst_gen φ JG JH g), card_gen]
    rcases g with y | y | y
    · exact (EffSig.card_copyW _ _).trans (by simp)
    · exact (EffSig.card_discW _ _).trans (by simp)
    · change JH.card _ (block φ JH y) = _
      rw [block_isEffect φ JH y x]
      simp only [R_preimage_parents, ProdSig.Arr.mech.injEq]
      split_ifs <;> simp_all
  · intro a
    rw [CategoryTheory.Functor.map_id, card_id, card_id]
  · intro a b
    rw [card_eq_of_arrow _ ((subst φ JG JH).map_braid a b), card_braid, card_braid]
  · intro a b c f g hf hg
    rw [Functor.map_comp, card_comp, card_comp, hf, hg]
  · intro a b c d f g hf hg
    rw [card_eq_of_arrow _ ((subst φ JG JH).map_tensorHom f g), card_tensor, card_tensor, hf, hg]

theorem refine_obj_projM (a : JG.Fs) :
    (refine φ JH JG).obj (JG.projM.obj a) = JH.projM.obj ((subst φ JG JH).obj a) :=
  (refine_obj φ JH JG a).trans (congrArg JH.wordM (subst_obj φ JG JH a).symm)

/-! ### The square `φ^* ∘ [−]_M = [−]_M ∘ subst` -/

/-- "These are diagrams of the images under `φ^*` of the values of the nodes of `Γ_G`, by (6.1), and
`φ^*` is a strict symmetric monoidal functor; so `Γ_{φ^* G}` represents `φ^*([w ‖ v])`." -/
theorem refine_projM {a b : JG.Fs} (f : a ⟶ b) :
    Arrow.mk ((refine φ JH JG).map (JG.projM.map f)) =
      Arrow.mk (JH.projM.map ((subst φ JG JH).map f)) := by
  refine JG.induction (P := fun {a b} f => Arrow.mk ((refine φ JH JG).map (JG.projM.map f)) =
      Arrow.mk (JH.projM.map ((subst φ JG JH).map f))) ?_ ?_ ?_ ?_ ?_ f
  · intro g
    rw [refine_gen, JH.projM.mk_map_congr (subst_gen φ JG JH g)]
    rcases g with y | y | y
    · rw [fPhi_dup, preimW_of]
      exact (ProdSig.projM_copyW JH _).symm
    · rw [fPhi_disc, preimW_of]
      exact (ProdSig.projM_discW JH _).symm
    · rw [fPhi_mech]
      change _ = Arrow.mk (JH.projM.map (block φ JH y))
      rw [EffSig.projM_eq_freeEffect (block_isEffect φ JH y)]
  · intro a
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
    exact Arrow.mk_id_congr (refine_obj_projM φ JG JH a)
  · intro a b
    rw [JH.projM.mk_map_congr ((subst φ JG JH).map_braid a b)]
    change Arrow.mk ((refine φ JH JG).map (σ_ (JG.projM.obj a) (JG.projM.obj b))) = _
    rw [(refine φ JH JG).map_braid]
    change Arrow.mk (σ_ _ _) = Arrow.mk (σ_ (JH.projM.obj ((subst φ JG JH).obj a))
      (JH.projM.obj ((subst φ JG JH).obj b)))
    rw [refine_obj_projM, refine_obj_projM]
  · intro a b c f g hf hg
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
    exact Arrow.mk_comp_congr hf hg
  · intro a b c d f g hf hg
    rw [JH.projM.mk_map_congr ((subst φ JG JH).map_tensorHom f g)]
    change Arrow.mk ((refine φ JH JG).map (JG.projM.map f ⊗ₛ JG.projM.map g)) =
      Arrow.mk (JH.projM.map ((subst φ JG JH).map f) ⊗ₛ JH.projM.map ((subst φ JG JH).map g))
    rw [(refine φ JH JG).map_tensorHom]
    exact mk_tensorHom_congr hf hg

end FinODAG

end FreeMarkov
