/-
Free Markov categories, Stage 4: two Markov minimal sorted combs with the same skeleton, sorted by
ranks that agree on corresponding consumers, are isomorphic (`iso_of_sorted`).

"This shows that `Γ` is determined, up to isomorphisms, by its skeleton and the shapes of these
trees."  The isomorphism is given by the comparison principle of Stage 2: the nodes and edges of
both diagrams are mapped to their codes, read in terms of the live nodes, ports and consumers of the
first diagram.
-/
module

public import FreeMarkov.Stage4.CodingD

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

namespace Diagram

open scoped Classical

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄} [Fintype N] [Fintype E] [Fintype N'] [Fintype E']
  {X : Diagram G.toFreeGraphMonoid N E} {Y : Diagram G.toFreeGraphMonoid N' E'}
  {π : {x // X.Live x} ≃ {y // Y.Live y}}

section Transport

variable (π) in
/-- The consumer of `X` corresponding to an edge of `Y`, if any. -/
noncomputable def kappa (e' : E') : Option E :=
  if h : ∃ c, ConsCorr π c e' then some h.choose else none

omit [Fintype N] [Fintype N'] [Fintype E'] in
theorem kappa_eq {c : E} {c' : E'} (h : ConsCorr π c c') : kappa π c' = some c := by
  have h' : ∃ c, ConsCorr π c c' := ⟨c, h⟩
  simp only [kappa, dite_eq_left h', Option.some.injEq]
  exact consCorr_unique' h'.choose_spec h

omit [Fintype N] [Fintype N'] [Fintype E'] in
theorem consCorr_of_kappa {c : E} {c' : E'} (h : kappa π c' = some c) : ConsCorr π c c' := by
  unfold kappa at h
  split_ifs at h with h'
  · rw [Option.some.injEq] at h
    exact h ▸ h'.choose_spec

omit [Fintype N] [Fintype E] [Fintype N'] [Fintype E'] in
theorem exists_consCorr_of_consumer (hc : X.codWord = Y.codWord) (hS : SkeletonIso X Y π) {c' : E'}
    (h : Y.Consumer c') : ∃ c, ConsCorr π c c' := by
  obtain ⟨c, hc⟩ := consCorr_exists hc.symm hS.symm h
  exact ⟨c, consCorr_symm_iff.1 hc⟩

variable (hd : X.domWord = Y.domWord) (hS : SkeletonIso X Y π)

/-- Transport of the codes of `Y`. -/
noncomputable def trE : E' ⊕ E' ⊕ Y.PortT → Option (E ⊕ E ⊕ X.PortT)
  | .inl c' => (kappa π c').map .inl
  | .inr (.inl ℓ') => (kappa π ℓ').map fun ℓ => .inr (.inl ℓ)
  | .inr (.inr p') => some (.inr (.inr ((portEquiv hd hS).symm p')))

/-- Transport of the node codes of `Y`. -/
noncomputable def trN : {y // Y.Live y} ⊕ E' ⊕ Y.PortT → Option ({x // X.Live x} ⊕ E ⊕ X.PortT)
  | .inl y => some (.inl (π.symm y))
  | .inr (.inl ℓ') => (kappa π ℓ').map fun ℓ => .inr (.inl ℓ)
  | .inr (.inr p') => some (.inr (.inr ((portEquiv hd hS).symm p')))

/-- The edge codes of `Y`, read in `X`. -/
noncomputable def qE (e' : E') : Option (E ⊕ E ⊕ X.PortT) := (Y.codeE e').bind (trE hd hS)

/-- The node codes of `Y`, read in `X`. -/
noncomputable def qN (y : N') : Option ({x // X.Live x} ⊕ E ⊕ X.PortT) := (Y.codeN y).bind (trN hd hS)

omit [Fintype N] [Fintype E] [Fintype N'] [Fintype E'] in
theorem portEdge_portEquiv_inr (x : {x // X.Live x}) (j : Fin (X.outs x.1).length) :
    Y.portEdge (portEquiv hd hS (.inr ⟨x, j⟩)) = (Y.outs (π x).1)[j.1]'(by
      rw [outs_length_eq_of_val (hS.val_eq x)]; exact j.2) := rfl

omit [Fintype N] [Fintype E] [Fintype N'] [Fintype E'] in
theorem portEdge_portEquiv_inl (j : ULift (Fin X.dom.length)) :
    Y.portEdge (portEquiv hd hS (.inl j)) = Y.dom[j.down.1]'(by
      rw [← dom_length_eq_of_domWord hd]; exact j.down.2) := rfl

omit [Fintype N] [Fintype N'] in
/-- Corresponding leaves of corresponding ports. -/
theorem leafSet_corr (p : X.PortT) {c : E} {c' : E'} (h : ConsCorr π c c') :
    c ∈ X.leafSet (X.portEdge p) ↔ c' ∈ Y.leafSet (Y.portEdge (portEquiv hd hS p)) := by
  rw [mem_leafSet, mem_leafSet]
  have h₁ := consCorr_origin hd hS h p
  constructor
  · rintro ⟨h₂, -⟩
    exact ⟨(h₁.1 ⟨h₂, isRoot_portEdge p⟩).1, h.consumer.2⟩
  · rintro ⟨h₂, -⟩
    exact ⟨(h₁.2 ⟨h₂, isRoot_portEdge _⟩).1, h.consumer.1⟩

variable (hc : X.codWord = Y.codWord) {rkX : E → ℕ} {rkY : E' → ℕ}
  (hrk : ∀ c c', ConsCorr π c c' → rkY c' = rkX c)
include hS hc hrk

omit [Fintype N] [Fintype E] [Fintype N'] [Fintype E'] in
/-- Transport of sets of corresponding leaves: the minimum and the cardinality correspond. -/
theorem transport_leaves (hrkX : Function.Injective rkX) {LX : Finset E} {LY : Finset E'}
    (hX : ∀ c ∈ LX, X.Consumer c) (hY : ∀ c' ∈ LY, Y.Consumer c')
    (hLL : ∀ c c', ConsCorr π c c' → (c ∈ LX ↔ c' ∈ LY)) :
    (LX.Nonempty ↔ LY.Nonempty) ∧ LX.card = LY.card ∧
      ∀ (hX' : LX.Nonempty) (hY' : LY.Nonempty), ConsCorr π (minR rkX LX hX') (minR rkY LY hY') := by
  refine ⟨⟨fun ⟨c, hcm⟩ => ?_, fun ⟨c', hcm⟩ => ?_⟩, ?_, fun hX' hY' => ?_⟩
  · obtain ⟨c', hcc⟩ := consCorr_exists hc hS (hX c hcm)
    exact ⟨c', (hLL c c' hcc).1 hcm⟩
  · obtain ⟨c, hcc⟩ := exists_consCorr_of_consumer hc hS (hY c' hcm)
    exact ⟨c, (hLL c c' hcc).2 hcm⟩
  · refine Finset.card_bij (fun c hcm => (consCorr_exists hc hS (hX c hcm)).choose) (fun c hcm => ?_)
      (fun c₁ h₁ c₂ h₂ h => ?_) (fun c' hcm => ?_)
    · exact (hLL c _ (consCorr_exists hc hS (hX c hcm)).choose_spec).1 hcm
    · exact consCorr_unique' (consCorr_exists hc hS (hX c₁ h₁)).choose_spec
        (h ▸ (consCorr_exists hc hS (hX c₂ h₂)).choose_spec)
    · obtain ⟨c, hcc⟩ := exists_consCorr_of_consumer hc hS (hY c' hcm)
      exact ⟨c, (hLL c c' hcc).2 hcm,
        consCorr_unique (consCorr_exists hc hS (hX c ((hLL c c' hcc).2 hcm))).choose_spec hcc⟩
  · obtain ⟨m, hm⟩ := exists_consCorr_of_consumer hc hS (hY _ (minR_mem rkY LY hY'))
    have hmX : m ∈ LX := (hLL _ _ hm).2 (minR_mem rkY LY hY')
    rw [minR_eq hrkX hX' hmX fun c hcm => by
      obtain ⟨c', hcc⟩ := consCorr_exists hc hS (hX c hcm)
      rw [← hrk m _ hm, ← hrk c c' hcc]
      exact minR_le rkY LY hY' ((hLL c c' hcc).1 hcm)]
    exact hm

omit [Fintype N] [Fintype N'] [Fintype E'] in
theorem ofLeaves_transport (hrkX : Function.Injective rkX) {LX : Finset E} {LY : Finset E'}
    (hX : ∀ c ∈ LX, X.Consumer c) (hY : ∀ c' ∈ LY, Y.Consumer c')
    (hLL : ∀ c c', ConsCorr π c c' → (c ∈ LX ↔ c' ∈ LY)) (p : X.PortT) :
    (Y.ofLeaves rkY LY (portEquiv hd hS p)).bind (trE hd hS) = X.ofLeaves rkX LX p := by
  obtain ⟨hne, hcard, hmin⟩ := transport_leaves hS hc hrk hrkX hX hY hLL
  by_cases hX' : LX.Nonempty
  · have hY' := hne.1 hX'
    simp only [ofLeaves, dite_eq_left hX', dite_eq_left hY', hcard]
    split_ifs <;> simp [trE, kappa_eq (hmin hX' hY')]
  · have hY' : ¬ LY.Nonempty := fun h => hX' (hne.2 h)
    simp [ofLeaves, hX', hY', trE]

omit [Fintype N] [Fintype N'] [Fintype E'] in
theorem nextOf_transport (hrkX : Function.Injective rkX) {LX : Finset E} {LY : Finset E'}
    (hX : ∀ c ∈ LX, X.Consumer c) (hY : ∀ c' ∈ LY, Y.Consumer c')
    (hLL : ∀ c c', ConsCorr π c c' → (c ∈ LX ↔ c' ∈ LY)) :
    (Y.nextOf rkY LY).bind (trE hd hS) = X.nextOf rkX LX := by
  obtain ⟨hne, hcard, hmin⟩ := transport_leaves hS hc hrk hrkX hX hY hLL
  by_cases hX' : LX.Nonempty
  · have hY' := hne.1 hX'
    simp only [nextOf, dite_eq_left hX', dite_eq_left hY', hcard]
    split_ifs <;> simp [trE, kappa_eq (hmin hX' hY')]
  · have hY' : ¬ LY.Nonempty := fun h => hX' (hne.2 h)
    simp [nextOf, hX', hY']

end Transport

end Diagram

end FreeMarkov
