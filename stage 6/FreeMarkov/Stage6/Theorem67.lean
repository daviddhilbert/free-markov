/-
Free Markov categories, Stage 6: **Theorem 6.7** (functoriality of refinement), in the form fixed by
D7: a functor `FinODAGᵒᵖ ⥤ StrictMarkovCat`, `G ↦ Cau(G)`, `φ ↦ φ^*`, followed by the inclusion into
`MarCat`.

The free Markov categories `Cau(G)` are built from the cited result C1 for each `W(G)`; the theorem
therefore takes a family `J : ∀ G : FinODAG, G.JS` of instances of C1 (one for each object), and
`Cau(G) = (J G).FsM`.

* `refine_id`: `1^* = 1` ("`f_φ(κ_v) = [v ‖ pa(v)] = κ_v` ... and hence `φ^*` is the identity
  functor, by the uniqueness in Definition 6.4").
* `refine_comp`: `(φ ∘ ψ)^* = ψ^* ∘ φ^*` (Proposition 6.6 and the uniqueness in Definition 6.4).
* `refinementStrict J : FinODAGᵒᵖ ⥤ StrictMarkovCat` and `refinement J : FinODAGᵒᵖ ⥤ MarCat`,
  the functors with `obj G = Cau(G)`, `map φ = φ^*`. The mathematical content of Theorem 6.7 is
  in their functor laws, i.e. in `refine_id` and `refine_comp`, restated in
  **`theorem_6_7_strict`**; `theorem_6_7` only records the values of `refinement J`.

The cited result C1 enters through `J`.
-/
module

public import FreeMarkov.Stage6.MarCat

@[expose] public section

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov JoyalStreet

namespace FinODAG

/-- Two graph monoid homomorphisms `W(G) → D` that match duplicates and discards, agree on words and
on the causal mechanisms, are equal. -/
theorem hom_ext_W {G : FinODAG} {D : Type*} [Monoid D] [Category D] [StrictMarkov D]
    {f g : G.W.toGraphMonoid.Hom (graphMonoid D)} (hf : G.W.MatchesDupDisc f)
    (hg : G.W.MatchesDupDisc g) (hV : ∀ y, f.V (FreeMonoid.of y) = g.V (FreeMonoid.of y))
    (hκ : ∀ y, f.A (.mech y) = g.A (.mech y)) : f = g := by
  have hV' : f.V = g.V := FreeMonoid.hom_eq hV
  refine GraphMonoid.Hom.ext hV' (funext fun x => ?_)
  rcases x with y | y | y
  · exact (hf.dup y).trans ((congrArg (fun a => Arrow.mk (δ_ a)) (hV y)).trans (hg.dup y).symm)
  · exact (hf.disc y).trans ((congrArg (fun a => Arrow.mk (ε_ a)) (hV y)).trans (hg.disc y).symm)
  · exact hκ y

theorem preimS_id {G : FinODAG} (S : Finset (Fin G.n)) : preimS (𝟙 G) S = S := by
  ext x; simp

theorem iM_mech {G : FinODAG} (J : G.JS) (y : Fin G.n) :
    J.iM.A (.mech y) = Arrow.mk (J.projM.map (EffSig.mechK J y)) :=
  (J.projM.mk_map_congr (EffSig.arrow_mechK y)).symm

theorem iM_mech' {G : FinODAG} (J : G.JS) (y : Fin G.n) :
    Arrow.mk (J.iM.A (.mech y)).hom = Arrow.mk (J.projM.map (EffSig.mechK J y)) :=
  iM_mech J y

theorem matches_comp {G : FinODAG} {D : Type*} [Monoid D] [Category D] [StrictMarkov D]
    (J : G.JS) (F : StrictMarkovFunctor J.FsM D) : G.W.MatchesDupDisc (F.toGraphMonoidHom.comp J.iM) := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · change Arrow.mk (F.map (J.iM.A (G.W.dup a)).hom) = _
    rw [J.iM_matches.dup a]
    exact F.map_copy _
  · change Arrow.mk (F.map (J.iM.A (G.W.disc a)).hom) = _
    rw [J.iM_matches.disc a]
    exact F.map_discard _

/-- *Theorem 6.7, identities.* `1_G^* = 1_{Cau(G)}`. -/
theorem refine_id {G : FinODAG} (J : G.JS) :
    refine (𝟙 G) J J = StrictMarkovFunctor.id J.FsM := by
  refine (eq_refine (𝟙 G) J J _ ?_).symm
  refine hom_ext_W (fPhi_matches _ _) (matches_comp J _) (fun y => ?_) (fun y => ?_)
  · rw [fPhi_V, preimW_id]; rfl
  · rw [fPhi_mech, preimS_id, fiber_id]
    change _ = Arrow.mk (J.iM.A (.mech y)).hom
    rw [iM_mech', ← EffSig.freeEffect_parents]

/-- *Theorem 6.7, composition.* For `ψ : G'' → G'`, `φ : G' → G`: `(φ ∘ ψ)^* = ψ^* ∘ φ^*`. -/
theorem refine_comp {L H G : FinODAG} (ψ : L ⟶ H) (φ : H ⟶ G) (JL : L.JS) (JH : H.JS) (JG : G.JS) :
    refine (ψ ≫ φ) JL JG = (refine ψ JL JH).comp (refine φ JH JG) := by
  refine (eq_refine (ψ ≫ φ) JL JG _ ?_).symm
  refine hom_ext_W (fPhi_matches _ _) (matches_comp JG _) (fun y => ?_) (fun y => ?_)
  · rw [fPhi_V, ← preimW_comp]
    change _ = (refine ψ JL JH).obj ((refine φ JH JG).obj (JG.wordM (FreeMonoid.of y)))
    rw [refine_obj, refine_obj]
  · rw [fPhi_mech]
    change _ = Arrow.mk ((refine ψ JL JH).map ((refine φ JH JG).map (JG.iM.A (.mech y)).hom))
    rw [(refine ψ JL JH).toFunctor.mk_map_congr ((refine φ JH JG).toFunctor.mk_map_congr
      (iM_mech' JG y))]
    rw [(refine ψ JL JH).toFunctor.mk_map_congr (refine_mechK φ JH JG y)]
    exact ((prop_6_6_sets ψ JH JL _ _).trans (by rw [preimS_comp, preimS_fiber]; rfl)).symm

variable (J : ∀ G : FinODAG, G.JS)

/-- The functor `G ↦ Cau(G)`, `φ ↦ φ^*` into strict Markov categories and strict Markov functors
(D7). -/
noncomputable def refinementStrict : FinODAGᵒᵖ ⥤ StrictMarkovCat.{0, 0} where
  obj G := StrictMarkovCat.of (J G.unop).FsM
  map φ := refine φ.unop (J _) (J _)
  map_id G := refine_id (J G.unop)
  map_comp φ ψ := refine_comp ψ.unop φ.unop (J _) (J _) (J _)

/-- **Theorem 6.7** (Functoriality of refinement). "The construction of `φ^*` is functorial, that is,
there is a contravariant functor `FinODAG → MarCat` sending each object `G` to `Cau(G)` and each
morphism `φ` to `φ^*`": the functor `refinementStrict J` into strict Markov categories and strict
Markov functors, followed by the inclusion into Markov categories and Markov functors (D7). -/
noncomputable def refinement : FinODAGᵒᵖ ⥤ MarCat.{0, 0} :=
  refinementStrict J ⋙ StrictMarkovCat.toMarCat

/-- **Theorem 6.7.** The functor `refinement J : FinODAGᵒᵖ ⥤ MarCat` sends each object `G` to
`Cau(G)` (with its Markov structure) and each morphism `φ : H → G` to the `φ`-refinement `φ^*`
(Definition 6.4), regarded as a Markov functor. -/
theorem theorem_6_7 :
    (∀ G : FinODAG, (refinement J).obj (Opposite.op G) = MarCat.of (J G).FsM) ∧
    (∀ {H G : FinODAG} (φ : H ⟶ G),
      (refinement J).map φ.op = StrictMarkovFunctor.toMarkovFunctor (refine φ (J H) (J G))) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- **Theorem 6.7**, strict form (D7): `G ↦ Cau(G)`, `φ ↦ φ^*` is a functor
`FinODAGᵒᵖ ⥤ StrictMarkovCat`, i.e. `1^* = 1` and `(φ ∘ ψ)^* = ψ^* ∘ φ^*` on the nose. -/
theorem theorem_6_7_strict :
    (∀ G : FinODAG, (refinementStrict J).obj (Opposite.op G) = StrictMarkovCat.of (J G).FsM) ∧
    (∀ {H G : FinODAG} (φ : H ⟶ G), (refinementStrict J).map φ.op = refine φ (J H) (J G)) ∧
    (∀ G : FinODAG, refine (𝟙 G) (J G) (J G) = StrictMarkovFunctor.id (J G).FsM) ∧
    (∀ {L H G : FinODAG} (ψ : L ⟶ H) (φ : H ⟶ G),
      refine (ψ ≫ φ) (J L) (J G) = (refine ψ (J L) (J H)).comp (refine φ (J H) (J G))) :=
  ⟨fun _ => rfl, fun _ => rfl, fun G => refine_id (J G), fun ψ φ => refine_comp ψ φ _ _ _⟩

end FinODAG

end FreeMarkov
