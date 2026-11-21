/-
Free Markov categories, Stage 7: the results of Sections 3–5 that Stages 2–5 state for an
arbitrary instance `J` of C1, without that hypothesis (final audit, 2026-11-21).

Each statement is the earlier one with `J := JoyalStreet.ofCombinatorial _` substituted.

* `Combinatorial.cor_3_5`: Corollary 3.5.
* `Combinatorial.remark_4_2`, `remark_4_2_surjective`: Remark 4.2.
* `Combinatorial.remark_5_2`, `remark_5_3`: Remarks 5.2 and 5.3.
* `Combinatorial.effect`, `lemma_5_5`, `prop_5_6`: Definition 5.4, Lemma 5.5, Proposition 5.6.
-/
module

public import FreeMarkov.Stage7.JoyalStreet

@[expose] public section

universe w v u u₁ v₁ u₂ v₂

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov FreeGraphMonoid

namespace Combinatorial

/-! ### Section 3 -/

/-- **Corollary 3.5**, unconditional: `S_T = E_T`. -/
theorem cor_3_5 {S : Type w} {G : FreeGraphMonoid.{w, v} S} {T : Set (Template.{u} G)}
    (hT : Template.IsSymmetric T) (c d : DClass G) : SRel T c d ↔ ERel T c d :=
  FreeMarkov.cor_3_5 (JoyalStreet.ofCombinatorial G) hT c d

/-! ### Section 4 -/

section Section4

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S}

/-- **Remark 4.2**, unconditional: two parallel morphisms of `Syn_s(G)` are congruent modulo the
axioms of Markov categories if and only if they have the same image in `F_s(G)/S_M`. -/
theorem remark_4_2 {a b : G.toFreeGraphMonoid.Syn} (f g : a ⟶ b) :
    G.MarkovCong (Arrow.mk f) (Arrow.mk g) ↔
      (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).synToM.map f =
        (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).synToM.map g :=
  (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).remark_4_2 f g

/-- **Remark 4.2**, unconditional: every morphism of `F_s(G)/S_M` is the image of a morphism of
`Syn_s(G)`. -/
theorem remark_4_2_surjective {a b : FsM G} (φ : a ⟶ b) :
    ∃ f : (Syn.of G.toFreeGraphMonoid a ⟶ Syn.of G.toFreeGraphMonoid b),
      (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).synToM.map f = φ :=
  (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).remark_4_2_surjective φ

end Section4

/-! ### Section 5 -/

section Section5

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C]

/-- **Remark 5.2**, unconditional: in a straight Markov category every multiplier `w → w^m` on
`(w)` is the `m`-fold copy. -/
theorem remark_5_2 (hS : Straight C) (w : C) (m : ℕ) (f : w ⟶ w ^ m)
    (hf : IsMult [w] (Arrow.mk f)) : f = copyN w m :=
  FreeMarkov.remark_5_2 (JoyalStreet.ofCombinatorial _) hS w m f hf

/-- **Remark 5.3**, unconditional: in a strict Markov category whose objects are the words over
`X`, there is exactly one multiplier on `(W, v)` for distinct letters `W` and a word `v` in them. -/
theorem remark_5_3 {X : Type} [Category.{v} (FreeMonoid X)] [StrictMarkov (FreeMonoid X)]
    (W : List X) (hW : W.Nodup) (v : FreeMonoid X) (hv : ∀ x ∈ FreeMonoid.toList v, x ∈ W) :
    ∃! f : (W.map FreeMonoid.of).prod ⟶ v, IsMultiplier (W.map FreeMonoid.of) v f :=
  FreeMarkov.remark_5_3 (JoyalStreet.ofCombinatorial _) W hW v hv

variable {n : ℕ} (D : EffData C n)

/-- **Definition 5.4**, unconditional: the `(W, K)`-effect `[w_T ‖ w_S]_{(W,K)} : w_S → w_T`. -/
noncomputable abbrev effect (S T : Finset (Fin n)) : D.wS S ⟶ D.wS T :=
  D.effect (JoyalStreet.ofCombinatorial _) S T

/-- **Lemma 5.5**, unconditional: `[T ‖ S] = [T ‖ T_i] ∘ [T_i ‖ S]` for `i ∈ V(G_{S → T}) ∖ S`. -/
theorem lemma_5_5 {S T : Finset (Fin n)} {i : Fin n} (hi : D.R S T i) :
    effect D S T = effect D S (D.Ti S T i) ≫ effect D (D.Ti S T i) T :=
  D.lemma_5_5 (JoyalStreet.ofCombinatorial _) hi

/-- **Proposition 5.6**, unconditional: a strict Markov functor sends the `(W, K)`-effect to the
`(F(W), F(K))`-effect. -/
theorem prop_5_6 {D' : Type u₂} [Monoid D'] [Category.{v₂} D'] [StrictMarkov D']
    (F : StrictMarkovFunctor C D') (S T : Finset (Fin n)) :
    Arrow.mk (F.map (effect D S T)) = Arrow.mk (effect (D.map F) S T) :=
  D.prop_5_6 (JoyalStreet.ofCombinatorial _) F S T

end Section5

end Combinatorial

end FreeMarkov
