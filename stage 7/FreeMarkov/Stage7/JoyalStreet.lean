/-
Free Markov categories, Stage 7: the cited result C1 holds for the combinatorial diagrams, and the
main theorems of the paper without it.

`JoyalStreet.ofCombinatorial G : JoyalStreet G` is the comparison map `Syn_s(G) → F_s(G)` of
`FsCat.lean` (the strict functor given by the universal property of `Syn_s(G)`), which is
injective (`ValueOps.lean`: the value of a diagram is a left inverse) and surjective
(`Generation.lean`).  The structure `JoyalStreet` is the one of Stage 1, unchanged.

The unconditional forms of the main results live in the namespace `FreeMarkov.Combinatorial`;
each is the corresponding result of Stages 1–6 applied to `JoyalStreet.ofCombinatorial`.  The
cited result C2 (`Strictification`) is not touched: it remains a hypothesis where Section 5 uses
it.
-/
module

public import FreeMarkov.Stage7.ValueOps
public import FreeMarkov.Stage7.Generation
public import FreeMarkov.Stage6

@[expose] public section

universe w v u' v' u₃ u₄

namespace FreeMarkov

open CategoryTheory StrictSMC FreeGraphMonoid

/-- **The cited result C1 for the combinatorial diagrams** (Joyal–Street, Theorem 2.3, in the
comparison form of Stage 1): for every free graph monoid `G` and all words `a`, `b`, the comparison
map from the morphisms `a → b` of `Syn_s(G)` to the isomorphism classes of anchored diagrams from
`a` to `b` is a bijection compatible with generators, identities, symmetries, composition and
monoidal product.  No hypothesis. -/
noncomputable def JoyalStreet.ofCombinatorial {S : Type w} (G : FreeGraphMonoid.{w, v} S) :
    JoyalStreet G where
  equiv _ _ := Equiv.ofBijective FsC.toDHom ⟨FsC.toDHom_injective, FsC.toDHom_surjective⟩
  map_gen x := FsC.toDHom_gen x
  map_id a := FsC.toDHom_id a
  map_braid a b := FsC.toDHom_braid a b
  map_comp f g := FsC.toDHom_comp f g
  map_tensor f g := FsC.toDHom_tensor f g

/-- **C1 holds** for the combinatorial diagrams of every free graph monoid. -/
theorem joyalStreet {S : Type w} (G : FreeGraphMonoid.{w, v} S) : Nonempty (JoyalStreet G) :=
  ⟨JoyalStreet.ofCombinatorial G⟩

namespace Combinatorial

/-! ### Section 2 -/

section Section2

variable {S : Type w} (G : FreeGraphMonoid.{w, v} S)

/-- **Theorem 2.3**, unconditional: the isomorphism classes of anchored diagrams in `G` form the
free symmetric strict monoidal category `F_s(G)` over `G` (here `FsC G`, built in Stage 7 without
any cited result). -/
theorem theorem_2_3 : IsFreeSymmetric.{w, v, u', v'} (FsC G) G (FsC.ι G) :=
  (JoyalStreet.ofCombinatorial G).isFreeSymmetric

/-- **Generation principle** for `F_s(G)`, unconditional. -/
theorem induction {P : ∀ {a b : FsC G}, (a ⟶ b) → Prop}
    (h_gen : ∀ x : G.A, P (FsC.hom (DHom.gen x)))
    (h_id : ∀ a : FsC G, P (𝟙 a))
    (h_braid : ∀ a b : FsC G, P (σ_ a b))
    (h_comp : ∀ {a b c : FsC G} (f : a ⟶ b) (g : b ⟶ c), P f → P g → P (f ≫ g))
    (h_tensor : ∀ {a b c d : FsC G} (f : a ⟶ b) (g : c ⟶ d), P f → P g → P (f ⊗ₛ g))
    {a b : FsC G} (f : a ⟶ b) : P f :=
  (JoyalStreet.ofCombinatorial G).induction (P := P) h_gen h_id h_braid h_comp h_tensor f

end Section2

/-! ### Section 4 -/

section Section4

variable {S : Type w} (G : FreeDDGraphMonoid.{w, v} S)

/-- The free Markov category `F_s(G)/S_M` of a free DD-graph monoid, for the combinatorial
diagrams. -/
noncomputable abbrev FsM : Type w := (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).FsM

/-- **Theorem 4.1**, unconditional: `F_s(G)/S_M` is the free Markov category over `G`. -/
theorem theorem_4_1 :
    IsFreeMarkov.{w, v, max w v, w, v', u'} (FsM G) G
      (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).iM :=
  (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).theorem_4_1

variable {G}

/-- **Lemma 4.4** in the form used in `F_s(G)/S_M`, unconditional: two diagrams represent the same
morphism of the free Markov category if and only if they have the same skeleton. -/
theorem lemma_4_4 {N : Type u₃} {E : Type u₄} {N' : Type u₃} {E' : Type u₄} [Finite N] [Finite E]
    [Finite N'] [Finite E'] {a b : (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).Fs}
    (f g : a ⟶ b) {Γ : Diagram G.toFreeGraphMonoid N E} {Υ : Diagram G.toFreeGraphMonoid N' E'}
    (hf : (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).cls f = DClass.mk Γ)
    (hg : (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).cls g = DClass.mk Υ) :
    (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).projM.map f =
        (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).projM.map g ↔
      Diagram.SameSkeleton Γ Υ :=
  (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).projM_map_eq_iff f g hf hg

/-- **Lemma 4.5**, unconditional (dead inputs). -/
theorem lemma_4_5 {N : Type u₃} {E : Type u₄} [Finite N] [Finite E]
    {Γ : Diagram G.toFreeGraphMonoid N E} {a b : FreeMonoid S}
    (f : JoyalStreet.Fs.of (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid) a ⟶
      JoyalStreet.Fs.of (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid) b)
    (hf : (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).cls f = DClass.mk Γ) :
    (∀ j < Γ.dom.length, ¬ Γ.Dead j ↔ ∃ k : ℕ, Γ.toAGraph.HasPath (.edge j) (.edge k)) ∧
    (∀ {N' : Type u₃} {E' : Type u₄} [Finite N'] [Finite E'] (Υ : Diagram G.toFreeGraphMonoid N' E'),
      SRel G.markovTemplates (DClass.mk Γ) (DClass.mk Υ) → ∀ j, Γ.Dead j ↔ Υ.Dead j) ∧
    (∃! g, (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).IsFactor f Γ.Dead g) ∧
    (∀ g, (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).IsFactor f Γ.Dead g →
      ∀ {N' : Type u₃} {E' : Type u₄} [Finite N'] [Finite E']
      (Υ : Diagram G.toFreeGraphMonoid N' E')
      (h : JoyalStreet.Fs.of (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid) (liveW a Γ.Dead) ⟶
        JoyalStreet.Fs.of (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid) b),
      (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).cls h = DClass.mk Υ →
      (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).projM.map h = g →
      ∀ j < Υ.dom.length, ∃ k : ℕ, Υ.toAGraph.HasPath (.edge j) (.edge k)) :=
  (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).lemma_4_5 f hf

end Section4

/-! ### Section 6 -/

section Section6

open FinODAG

/-- The instance of C1 for `W(G)`. -/
noncomputable abbrev js (G : FinODAG) : G.JS := JoyalStreet.ofCombinatorial G.W.toFreeGraphMonoid

/-- **Proposition 6.6**, unconditional: `φ^*` sends causal effects of singular variables to causal
effects of their preimages. -/
theorem prop_6_6 {H G : FinODAG} (φ : H ⟶ G) (v w : FreeMonoid (Fin G.n)) (hv : Singular v)
    (hw : Singular w) :
    Arrow.mk ((refine φ (js H) (js G)).map (causalEffect (js G) v w hv hw)) =
      Arrow.mk (causalEffect (js H) (preimW φ v) (preimW φ w) (singular_preimW φ hv)
        (singular_preimW φ hw)) :=
  FinODAG.prop_6_6 φ (js G) (js H) v w hv hw

/-- **Proposition 6.6** for sets of variables, unconditional. -/
theorem prop_6_6_sets {H G : FinODAG} (φ : H ⟶ G) (S T : Finset (Fin G.n)) :
    Arrow.mk ((refine φ (js H) (js G)).map (causalEffectSets (js G) S T)) =
      Arrow.mk (causalEffectSets (js H) (preimS φ S) (preimS φ T)) :=
  FinODAG.prop_6_6_sets φ (js G) (js H) S T

/-- The refinement functor `FinODAGᵒᵖ ⥤ StrictMarkovCat`, `G ↦ Cau(G)`, `φ ↦ φ^*`. -/
noncomputable abbrev refinementStrict : FinODAGᵒᵖ ⥤ StrictMarkovCat.{0, 0} :=
  FinODAG.refinementStrict js

/-- The refinement functor `FinODAGᵒᵖ ⥤ MarCat`. -/
noncomputable abbrev refinement : FinODAGᵒᵖ ⥤ MarCat.{0, 0} := FinODAG.refinement js

/-- **Theorem 6.7**, unconditional. -/
theorem theorem_6_7 :
    (∀ G : FinODAG, refinement.obj (Opposite.op G) = MarCat.of (js G).FsM) ∧
    (∀ {H G : FinODAG} (φ : H ⟶ G),
      refinement.map φ.op = StrictMarkovFunctor.toMarkovFunctor (refine φ (js H) (js G))) :=
  FinODAG.theorem_6_7 js

/-- **Theorem 6.7**, strict form, unconditional. -/
theorem theorem_6_7_strict :
    (∀ G : FinODAG, refinementStrict.obj (Opposite.op G) = StrictMarkovCat.of (js G).FsM) ∧
    (∀ {H G : FinODAG} (φ : H ⟶ G), refinementStrict.map φ.op = refine φ (js H) (js G)) ∧
    (∀ G : FinODAG, refine (𝟙 G) (js G) (js G) = StrictMarkovFunctor.id (js G).FsM) ∧
    (∀ {L H G : FinODAG} (ψ : L ⟶ H) (φ : H ⟶ G),
      refine (ψ ≫ φ) (js L) (js G) = (refine ψ (js L) (js H)).comp (refine φ (js H) (js G))) :=
  FinODAG.theorem_6_7_strict js

end Section6

end Combinatorial

end FreeMarkov
