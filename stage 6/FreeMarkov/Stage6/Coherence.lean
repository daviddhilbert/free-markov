/-
Free Markov categories, Stage 6: label coherence with dead nodes.

Stage 5's `ProdSig.sameSkeleton_of_labels` compares two diagrams in which the same producers occur.
In the proof of Proposition 6.6 the diagram `Γ_{φ^* G}` may contain nodes `κ_x` that are not live
(for `x ∈ φ⁻¹(D ∖ S) ∖ (D' ∖ S')`), while `Γ_H` contains only live ones; the proof compares the
*live* nodes: "the live nodes of `Γ_{φ^* G}` are the nodes `k_x`, `x ∈ D' ∖ S'`, and so are those of
`Γ_H`, with the same values".  This file states label coherence in that form:

* `ProdSig.sameSkeleton_of_live`: two diagrams with the same domain (without repeated letters) and the
  same codomain, satisfying the label conditions, whose live producers are the same, have the same
  skeleton.
* `ProdSig.projM_eq_of_live`: the corresponding statement for morphisms of `F_s(Q.G)`, with the
  occurring producers counted on classes, giving equality in `F_s(Q.G)/S_M` (Lemma 4.4).
* `ProdSig.arrow_projM_eq_of_card_zero`: two morphisms of `F_s(Q.G)` from the same word without
  repeated letters to the same word, without nodes of producers, have the same image in
  `F_s(Q.G)/S_M`, compared as arrows.

The proofs follow Stage 5's `sameSkeleton_of_labels`, with the occurring producers replaced by the
live ones.  The cited result C1 enters only through the free Markov category `J.FsM`.
-/
module

public import FreeMarkov.Stage6.Lift

@[expose] public section

universe u₁ u₂ u₃ u₄

namespace FreeMarkov

open CategoryTheory StrictSMC JoyalStreet Relation

namespace ProdSig

variable {Q : ProdSig} {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}

/-- The producers that occur in `Γ` and whose output letter is connected to the codomain letters
through producers that occur: by `live_iff_liveLab`, these are the values of the live nodes. -/
def LiveProd (Γ : Diagram Q.G.toFreeGraphMonoid N E) (p : Q.P) : Prop :=
  Occurs Γ p ∧ Q.LiveLab (Occurs Γ) (Q.letters Γ.codWord) (Q.out p)

/-- **Label coherence with dead nodes.** Two diagrams in `Q.G` with the same domain, whose letters
are pairwise distinct, and the same codomain, satisfying the label conditions, whose live producers
are the same, have the same skeleton. -/
theorem sameSkeleton_of_live {Γ : Diagram Q.G.toFreeGraphMonoid N E}
    {Υ : Diagram Q.G.toFreeGraphMonoid N' E'} [Finite E] [Finite E']
    (hdom : Γ.domWord = Υ.domWord)
    (hnd : (Q.letters Γ.domWord).Nodup) (hcod : Γ.codWord = Υ.codWord) (hΓ : LabelCond Γ)
    (hΥ : LabelCond Υ) (hlive : ∀ p, LiveProd Γ p ↔ LiveProd Υ p) : Γ.SameSkeleton Υ := by
  have hnd' : (Q.letters Υ.domWord).Nodup := hdom ▸ hnd
  let e₁ := liveEquiv hΓ
  let e₂ := liveEquiv hΥ
  let c : {p // Occurs Γ p ∧ Q.LiveLab (Occurs Γ) (Q.letters Γ.codWord) (Q.out p)} ≃
      {p // Occurs Υ p ∧ Q.LiveLab (Occurs Υ) (Q.letters Υ.codWord) (Q.out p)} :=
    Equiv.subtypeEquivRight hlive
  let π := (e₁.trans c).trans e₂.symm
  have hπ : ∀ x, Υ.val.v₁ (π x).1 = Γ.val.v₁ x.1 := by
    intro x
    exact (liveEquiv_symm_spec hΥ _).trans (liveEquiv_spec hΓ x).symm
  have OM : ∀ (e : E) (e' : E'), Γ.val.v₀ e = Υ.val.v₀ e' → Diagram.OriginsMatch π e e' := by
    intro e e' hl
    refine ⟨fun j => ?_, fun y j => ?_⟩
    · rw [originAt_dom_iff hΓ hnd, originAt_dom_iff hΥ hnd', hdom, hl]
    · rw [originAt_out_iff hΓ, originAt_out_iff hΥ, hπ, hl]
  refine ⟨hdom, hcod, π, ⟨hπ, ?_, ?_⟩⟩
  · intro i e e' he he'
    refine OM e e' ?_
    have h₁ : (Γ.cod.map Γ.val.v₀)[i]? = (Υ.cod.map Υ.val.v₀)[i]? :=
      congrArg (fun a => (FreeMonoid.toList a)[i]?) hcod
    rw [List.getElem?_map, List.getElem?_map, he, he'] at h₁
    exact Option.some.inj h₁
  · intro x i e e' he he'
    refine OM e e' ?_
    have h₁ := ins_of_mech (liveEquiv_spec hΓ x)
    have h₂ := ins_of_mech (show Υ.val.v₁ (π x).1 = .mech (liveEquiv hΓ x).1 by
      rw [hπ, liveEquiv_spec hΓ x])
    have h₃ : ((Γ.ins x.1).map Γ.val.v₀)[i]? = ((Υ.ins (π x).1).map Υ.val.v₀)[i]? := by
      rw [h₁, h₂]
    rw [List.getElem?_map, List.getElem?_map, he, he'] at h₃
    exact Option.some.inj h₃

variable {J : JoyalStreet Q.G.toFreeGraphMonoid}

theorem occurs_iff_card {a b : J.Fs} {f : a ⟶ b} {n m : ℕ}
    {Γ : Diagram Q.G.toFreeGraphMonoid (Fin n) (Fin m)} (hΓ : J.cls f = DClass.mk Γ) (p : Q.P) :
    Occurs Γ p ↔ J.card (.mech p) f ≠ 0 := by
  have h : J.card (.mech p) f = Nat.card {x // Γ.val.v₁ x = .mech p} := by
    simp only [JoyalStreet.card, hΓ, DClass.card_mk, Diagram.card]
  rw [h, Nat.card_ne_zero]
  constructor
  · rintro ⟨x, hx⟩; exact ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
  · rintro ⟨⟨⟨x, hx⟩⟩, -⟩; exact ⟨x, hx⟩

/-- Morphism form: two morphisms of `F_s(Q.G)` from a word without repeated letters, satisfying the
label conditions, whose producers `p` that occur with `out p` connected to the codomain through
occurring producers are the same, have the same image in `F_s(Q.G)/S_M`. -/
theorem projM_eq_of_live {a b : FreeMonoid Q.X} (hnd : (Q.letters a).Nodup)
    {f g : Fs.of J a ⟶ Fs.of J b} (hf : LabelOK J f) (hg : LabelOK J g)
    (hlive : ∀ p, (J.card (.mech p) f ≠ 0 ∧
        Q.LiveLab (fun q => J.card (.mech q) f ≠ 0) (Q.letters b) (Q.out p)) ↔
      (J.card (.mech p) g ≠ 0 ∧
        Q.LiveLab (fun q => J.card (.mech q) g ≠ 0) (Q.letters b) (Q.out p))) :
    J.projM.map f = J.projM.map g := by
  obtain ⟨n, m, Γ, hΓ⟩ := DClass.exists_eq_mk (J.cls f)
  obtain ⟨n', m', Υ, hΥ⟩ := DClass.exists_eq_mk (J.cls g)
  rw [J.projM_map_eq_iff f g hΓ hΥ]
  have hdΓ : Γ.domWord = a := by rw [← DClass.dom_mk, ← hΓ]; exact J.cls_dom f
  have hdΥ : Υ.domWord = a := by rw [← DClass.dom_mk, ← hΥ]; exact J.cls_dom g
  have hcΓ : Γ.codWord = b := by rw [← DClass.cod_mk, ← hΓ]; exact J.cls_cod f
  have hcΥ : Υ.codWord = b := by rw [← DClass.cod_mk, ← hΥ]; exact J.cls_cod g
  have hoΓ : Occurs Γ = fun q => J.card (.mech q) f ≠ 0 :=
    funext fun q => propext (occurs_iff_card hΓ q)
  have hoΥ : Occurs Υ = fun q => J.card (.mech q) g ≠ 0 :=
    funext fun q => propext (occurs_iff_card hΥ q)
  refine sameSkeleton_of_live (hdΓ.trans hdΥ.symm) (by rw [hdΓ]; exact hnd)
    (hcΓ.trans hcΥ.symm) (labelCond_of_labelOK hf hΓ) (labelCond_of_labelOK hg hΥ) fun p => ?_
  unfold LiveProd
  rw [hoΓ, hoΥ, hcΓ, hcΥ]
  exact hlive p

/-- Two morphisms of `F_s(Q.G)` from a word without repeated letters, with no node of a producer,
between the same words up to identification, have the same image in `F_s(Q.G)/S_M`. -/
theorem arrow_projM_eq_of_card_zero {a b a' b' : FreeMonoid Q.X} (hnd : (Q.letters a).Nodup)
    (ha : a = a') (hb : b = b') {f : Fs.of J a ⟶ Fs.of J b} {g : Fs.of J a' ⟶ Fs.of J b'}
    (hf : ∀ p, J.card (.mech p) f = 0) (hg : ∀ p, J.card (.mech p) g = 0) :
    Arrow.mk (J.projM.map f) = Arrow.mk (J.projM.map g) := by
  subst ha hb
  refine congrArg Arrow.mk (projM_eq_of_card hnd (fun p => ?_) (fun p => ?_) fun p => ?_)
  · rw [hf p]; simp
  · rw [hg p]; simp
  · rw [hf p, hg p]

end ProdSig

end FreeMarkov
