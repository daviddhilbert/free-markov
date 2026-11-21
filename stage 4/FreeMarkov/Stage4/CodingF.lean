/-
Free Markov categories, Stage 4: the isomorphism of two Markov minimal sorted combs with the same
skeleton (`iso_of_sorted`).
-/
module

public import FreeMarkov.Stage4.CodingE

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
  (hd : X.domWord = Y.domWord) (hc : X.codWord = Y.codWord) (hS : SkeletonIso X Y π)
  {rkX : E → ℕ} {rkY : E' → ℕ} (hrk : ∀ c c', ConsCorr π c c' → rkY c' = rkX c)
  (hXm : X.MarkovMinimal) (hXc : X.IsComb) (hXs : Sorted rkX X) (hrkX : Function.Injective rkX)
  (hYm : Y.MarkovMinimal) (hYc : Y.IsComb) (hYs : Sorted rkY Y) (hrkY : Function.Injective rkY)

/-! ### Decoding -/

include hYm in
omit [Fintype N] [Fintype N'] [Fintype E'] in
theorem qE_cases {e' : E'} {t : E ⊕ E ⊕ X.PortT} (h : qE hd hS e' = some t) :
    (∃ c, t = .inl c ∧ ConsCorr π c e') ∨
    (∃ ℓ ℓ', t = .inr (.inl ℓ) ∧ ConsCorr π ℓ ℓ' ∧
      ∃ d a o, Y.tgt e' = some d ∧ Y.val.v₁ d = G.dup a ∧ Y.outs d = [ℓ', o]) ∨
    (∃ p, t = .inr (.inr p) ∧ Y.portEdge (portEquiv hd hS p) = e' ∧
      ∃ x, Y.tgt e' = some x ∧ Y.val.IsDisc x) := by
  obtain ⟨t', ht', htr⟩ := Option.bind_eq_some_iff.1 h
  rcases codeE_cases hYm ht' with ⟨c', rfl, rfl, -⟩ | ⟨ℓ', rfl, d, a, o, hte, ha, ho⟩ |
      ⟨p', rfl, hp', x, hte, hx⟩
  · obtain ⟨c, hc', rfl⟩ := Option.map_eq_some_iff.1 htr
    exact Or.inl ⟨c, rfl, consCorr_of_kappa hc'⟩
  · obtain ⟨ℓ, hℓ, rfl⟩ := Option.map_eq_some_iff.1 htr
    exact Or.inr (Or.inl ⟨ℓ, ℓ', rfl, consCorr_of_kappa hℓ, d, a, o, hte, ha, ho⟩)
  · simp only [trE, Option.some.injEq] at htr
    subst htr
    exact Or.inr (Or.inr ⟨_, rfl, by rw [Equiv.apply_symm_apply, hp'], x, hte, hx⟩)

include hYm in
omit [Fintype N] [Fintype N'] [Fintype E'] in
theorem qN_cases {y : N'} {t : {x // X.Live x} ⊕ E ⊕ X.PortT} (h : qN hd hS y = some t) :
    (∃ x, ∃ hy : Y.Live y, t = .inl x ∧ π x = ⟨y, hy⟩) ∨
    (∃ ℓ ℓ', t = .inr (.inl ℓ) ∧ ConsCorr π ℓ ℓ' ∧ ∃ a o, Y.val.v₁ y = G.dup a ∧ Y.outs y = [ℓ', o]) ∨
    (∃ p, t = .inr (.inr p) ∧ Y.val.IsDisc y ∧ Y.ins y = [Y.portEdge (portEquiv hd hS p)]) := by
  obtain ⟨t', ht', htr⟩ := Option.bind_eq_some_iff.1 h
  rcases codeN_cases hYm ht' with ⟨hl, rfl⟩ | ⟨ℓ', rfl, a, o, ha, ho⟩ | ⟨p', rfl, hdisc, hi⟩
  · simp only [trN, Option.some.injEq] at htr
    subst htr
    exact Or.inl ⟨_, hl, rfl, Equiv.apply_symm_apply _ _⟩
  · obtain ⟨ℓ, hℓ, rfl⟩ := Option.map_eq_some_iff.1 htr
    exact Or.inr (Or.inl ⟨ℓ, ℓ', rfl, consCorr_of_kappa hℓ, a, o, ha, ho⟩)
  · simp only [trN, Option.some.injEq] at htr
    subst htr
    exact Or.inr (Or.inr ⟨_, rfl, hdisc, by rw [Equiv.apply_symm_apply, hi]⟩)

/-! ### Values -/

omit [Fintype N] [Fintype N'] [Fintype E'] in
theorem qE_consumer {c : E} {c' : E'} (h : ConsCorr π c c') : qE hd hS c' = some (.inl c) := by
  simp [qE, codeE_consumer h.consumer.2, trE, kappa_eq h]

omit [Fintype N] [Fintype N'] [Fintype E'] in
theorem qE_dupIn {e' : E'} {d : N'} {a : S} (hte : Y.tgt e' = some d) (hda : Y.val.v₁ d = G.dup a)
    {ℓ' o : E'} (ho : Y.outs d = [ℓ', o]) {ℓ : E} (h : ConsCorr π ℓ ℓ') :
    qE hd hS e' = some (.inr (.inl ℓ)) := by
  simp [qE, codeE_dupIn hte hda ho, trE, kappa_eq h]

omit [Fintype N] [Fintype N'] [Fintype E'] in
theorem qE_discIn {e' : E'} {x : N'} (hte : Y.tgt e' = some x) (hx : Y.val.IsDisc x) (p : X.PortT)
    (hp : Y.portEdge (portEquiv hd hS p) = e') : qE hd hS e' = some (.inr (.inr p)) := by
  simp [qE, codeE_discIn hte hx _ hp, trE]

include hc hrk hXm hXc hXs hrkX hYm hYc hYs hrkY in
theorem qE_port (p : X.PortT) :
    qE hd hS (Y.portEdge (portEquiv hd hS p)) = X.codeE (X.portEdge p) := by
  rw [codeE_port hXm hXc hXs hrkX, qE, codeE_port hYm hYc hYs hrkY]
  exact ofLeaves_transport hd hS hc hrk hrkX (fun c h => (mem_leafSet.1 h).2)
    (fun c h => (mem_leafSet.1 h).2) (fun c c' h => leafSet_corr hd hS p h) p

/-! ### First leaves and discards correspond -/

include hd hS hc hrk hXm hXc hXs hYm hYc hYs in
theorem firstLeaf_corr {ℓ : E} {ℓ' : E'} (h : ConsCorr π ℓ ℓ') :
    (∃ d a o, X.val.v₁ d = G.dup a ∧ X.outs d = [ℓ, o]) ↔
      ∃ d a o, Y.val.v₁ d = G.dup a ∧ Y.outs d = [ℓ', o] := by
  rw [firstLeaf_iff hXm hXc hXs, firstLeaf_iff hYm hYc hYs]
  obtain ⟨hℓ, hℓ'⟩ := h.consumer
  obtain ⟨q, hq⟩ := PGraph.exists_isOrigin X.dupCond ℓ
  obtain ⟨p, rfl⟩ := origin_port_of_reachCod hq hℓ.reachCod
  have hq' : Y.IsOrigin (Y.portEdge (portEquiv hd hS p)) ℓ' := (consCorr_origin hd hS h p).1 hq
  have hu : ∀ q₁, X.IsOrigin q₁ ℓ → q₁ = X.portEdge p := fun q₁ h₁ =>
    PGraph.isOrigin_unique X.dupCond h₁ hq
  have hu' : ∀ q₁, Y.IsOrigin q₁ ℓ' → q₁ = Y.portEdge (portEquiv hd hS p) := fun q₁ h₁ =>
    PGraph.isOrigin_unique Y.dupCond h₁ hq'
  constructor
  · rintro ⟨-, q₁, hq₁, c, hcm, hlt⟩
    rw [hu q₁ hq₁] at hcm
    obtain ⟨c', hcc⟩ := consCorr_exists hc hS (mem_leafSet.1 hcm).2
    exact ⟨hℓ', _, hq', c', (leafSet_corr hd hS p hcc).1 hcm, by rw [hrk _ _ h, hrk _ _ hcc]; exact hlt⟩
  · rintro ⟨-, q₁, hq₁, c', hcm, hlt⟩
    rw [hu' q₁ hq₁] at hcm
    obtain ⟨c, hcc⟩ := exists_consCorr_of_consumer hc hS (mem_leafSet.1 hcm).2
    exact ⟨hℓ, _, hq, c, (leafSet_corr hd hS p hcc).2 hcm, by rw [← hrk _ _ h, ← hrk _ _ hcc]; exact hlt⟩

include hc in
omit [Fintype N] [Fintype N'] in
theorem disc_corr (p : X.PortT) :
    X.leafSet (X.portEdge p) = ∅ ↔ Y.leafSet (Y.portEdge (portEquiv hd hS p)) = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨c', hcm⟩ := Finset.nonempty_iff_ne_empty.2 hne
    obtain ⟨c, hcc⟩ := exists_consCorr_of_consumer hc hS (mem_leafSet.1 hcm).2
    have := (leafSet_corr hd hS p hcc).2 hcm
    rw [h] at this
    exact Finset.notMem_empty c this
  · intro h
    by_contra hne
    obtain ⟨c, hcm⟩ := Finset.nonempty_iff_ne_empty.2 hne
    obtain ⟨c', hcc⟩ := consCorr_exists hc hS (mem_leafSet.1 hcm).2
    have := (leafSet_corr hd hS p hcc).1 hcm
    rw [h] at this
    exact Finset.notMem_empty c' this

/-! ### The isomorphism -/

include hc hYm hYc in
omit [Fintype N] [Fintype N'] [Fintype E'] in
theorem qN_ne_none (y : N') : qN hd hS y ≠ none := by
  obtain ⟨t', ht'⟩ := Option.ne_none_iff_exists'.1 (codeN_ne_none hYm y)
  simp only [qN, ht', Option.bind_some]
  rcases codeN_cases hYm ht' with ⟨hl, rfl⟩ | ⟨ℓ', rfl, a, o, ha, ho⟩ | ⟨p', rfl, -, -⟩
  · simp [trN]
  · obtain ⟨ℓ, hℓ⟩ := exists_consCorr_of_consumer hc hS (hYc y a ha ℓ' o ho)
    simp [trN, kappa_eq hℓ]
  · simp [trN]

include hc hYm hYc in
omit [Fintype N] [Fintype N'] [Fintype E'] in
theorem qE_ne_none (e' : E') : qE hd hS e' ≠ none := by
  obtain ⟨t', ht'⟩ := Option.ne_none_iff_exists'.1 (codeE_ne_none hYm e')
  simp only [qE, ht', Option.bind_some]
  rcases codeE_cases hYm ht' with ⟨c', rfl, rfl, hc'⟩ | ⟨ℓ', rfl, d, a, o, -, ha, ho⟩ |
      ⟨p', rfl, -, -⟩
  · obtain ⟨c, hcc⟩ := exists_consCorr_of_consumer hc hS hc'
    simp [trE, kappa_eq hcc]
  · obtain ⟨ℓ, hℓ⟩ := exists_consCorr_of_consumer hc hS (hYc d a ha ℓ' o ho)
    simp [trE, kappa_eq hℓ]
  · simp [trE]

include hd hc hS hrk hXm hXc hXs hrkX hYm hYc hYs hrkY in
/-- **Markov minimal sorted combs with the same skeleton are isomorphic** (proof of Lemma 4.4,
second claim: "`Γ` is determined, up to isomorphisms, by its skeleton and the shapes of these
trees"). -/
theorem iso_of_sorted : Nonempty (X.Iso Y) := by
  -- the codes of the edges at corresponding positions
  have hlive_ins : ∀ (x : {x // X.Live x}) (i : ℕ) (h₁ : i < (X.ins x.1).length)
      (h₂ : i < (Y.ins (π x).1).length),
      X.codeE (X.ins x.1)[i] = qE hd hS (Y.ins (π x).1)[i] := by
    intro x i h₁ h₂
    have hcc : ConsCorr π (X.ins x.1)[i] (Y.ins (π x).1)[i] :=
      Or.inr ⟨x, i, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂⟩
    rw [codeE_consumer hcc.consumer.1, qE_consumer hd hS hcc]
  refine ⟨Iso.ofProj X.codeN X.codeE (qN hd hS) (qE hd hS) (fun _ _ h => codeN_injective hXm h)
    ?_ (fun _ _ h => codeE_injective hXm h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · -- `qN` is injective
    intro y₁ y₂ h
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 (qN_ne_none hd hc hS hYm hYc y₁)
    rw [ht] at h
    rcases qN_cases hd hS hYm ht with ⟨x, hy, rfl, hx⟩ | ⟨ℓ, ℓ', rfl, hℓ, a, o, ha, ho⟩ |
        ⟨p, rfl, hdisc, hi⟩ <;>
      rcases qN_cases hd hS hYm h.symm with ⟨x₂, hy₂, h₁, hx₂⟩ | ⟨ℓ₂, ℓ₂', h₁, hℓ₂, a₂, o₂, ha₂, ho₂⟩ |
        ⟨p₂, h₁, hdisc₂, hi₂⟩ <;> simp only [reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h₁
    · subst h₁
      have := hx.symm.trans hx₂
      exact congrArg Subtype.val this
    · subst h₁
      have hℓℓ := consCorr_unique hℓ hℓ₂
      subst hℓℓ
      have h₃ : Y.src ℓ' = some y₁ := (Y.mem_outs y₁ ℓ').1 (by rw [ho]; simp)
      have h₄ : Y.src ℓ' = some y₂ := (Y.mem_outs y₂ ℓ').1 (by rw [ho₂]; simp)
      rw [h₃, Option.some.injEq] at h₄
      exact h₄
    · subst h₁
      have h₃ : Y.tgt (Y.portEdge (portEquiv hd hS p)) = some y₁ := (Y.mem_ins y₁ _).1 (by rw [hi]; simp)
      have h₄ : Y.tgt (Y.portEdge (portEquiv hd hS p)) = some y₂ := (Y.mem_ins y₂ _).1 (by rw [hi₂]; simp)
      rw [h₃, Option.some.injEq] at h₄
      exact h₄
  · -- `qE` is injective
    intro e₁ e₂ h
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 (qE_ne_none hd hc hS hYm hYc e₁)
    rw [ht] at h
    rcases qE_cases hd hS hYm ht with ⟨c, rfl, hcc⟩ | ⟨ℓ, ℓ', rfl, hℓ, d, a, o, hte, ha, ho⟩ |
        ⟨p, rfl, hp, x, hte, hx⟩ <;>
      rcases qE_cases hd hS hYm h.symm with ⟨c₂, h₁, hcc₂⟩ |
        ⟨ℓ₂, ℓ₂', h₁, hℓ₂, d₂, a₂, o₂, hte₂, ha₂, ho₂⟩ | ⟨p₂, h₁, hp₂, x₂, hte₂, hx₂⟩ <;>
      simp only [reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h₁
    · subst h₁
      exact consCorr_unique hcc hcc₂
    · subst h₁
      have hℓℓ := consCorr_unique hℓ hℓ₂
      subst hℓℓ
      have h₃ : Y.src ℓ' = some d := (Y.mem_outs d ℓ').1 (by rw [ho]; simp)
      have h₄ : Y.src ℓ' = some d₂ := (Y.mem_outs d₂ ℓ').1 (by rw [ho₂]; simp)
      rw [h₃, Option.some.injEq] at h₄
      subst h₄
      obtain ⟨f, hf, -⟩ := Y.val.ins_eq_of_dup ha
      have h₅ : e₁ ∈ Y.ins d := (Y.mem_ins d e₁).2 hte
      have h₆ : e₂ ∈ Y.ins d := (Y.mem_ins d e₂).2 hte₂
      rw [hf, List.mem_singleton] at h₅ h₆
      rw [h₅, h₆]
    · subst h₁
      rw [← hp, ← hp₂]
  · -- the nodes have the same codes
    rintro (_ | t)
    · constructor
      · rintro ⟨x, hx⟩; exact (codeN_ne_none hXm x hx).elim
      · rintro ⟨y, hy⟩; exact (qN_ne_none hd hc hS hYm hYc y hy).elim
    constructor
    · rintro ⟨x, hx⟩
      rcases codeN_cases hXm hx with ⟨hl, rfl⟩ | ⟨ℓ, rfl, a, o, ha, ho⟩ | ⟨p, rfl, hdisc, hi⟩
      · refine ⟨(π ⟨x, hl⟩).1, ?_⟩
        simp [qN, codeN_live (π ⟨x, hl⟩).2, trN]
      · obtain ⟨ℓ', hℓ⟩ := consCorr_exists hc hS (hXc x a ha ℓ o ho)
        obtain ⟨d', a', o', ha', ho'⟩ :=
          (firstLeaf_corr hd hc hS hrk hXm hXc hXs hYm hYc hYs hℓ).1 ⟨x, a, o, ha, ho⟩
        exact ⟨d', by simp [qN, codeN_dup ha' ho', trN, kappa_eq hℓ]⟩
      · have hL := (disc_iff hXm p).1 ⟨x, hdisc, hi⟩
        obtain ⟨y, hy, hyi⟩ := (disc_iff hYm (portEquiv hd hS p)).2 ((disc_corr hd hc hS p).1 hL)
        exact ⟨y, by simp [qN, codeN_disc hy hyi _ rfl, trN]⟩
    · rintro ⟨y, hy⟩
      rcases qN_cases hd hS hYm hy with ⟨x, hy', rfl, -⟩ | ⟨ℓ, ℓ', rfl, hℓ, a, o, ha, ho⟩ |
          ⟨p, rfl, hdisc, hi⟩
      · exact ⟨x.1, codeN_live x.2⟩
      · obtain ⟨d, a', o', ha', ho'⟩ :=
          (firstLeaf_corr hd hc hS hrk hXm hXc hXs hYm hYc hYs hℓ).2 ⟨y, a, o, ha, ho⟩
        exact ⟨d, codeN_dup ha' ho'⟩
      · have hL := (disc_iff hYm _).1 ⟨y, hdisc, hi⟩
        obtain ⟨x, hx, hxi⟩ := (disc_iff hXm p).2 ((disc_corr hd hc hS p).2 hL)
        exact ⟨x, codeN_disc hx hxi p rfl⟩
  · -- the edges have the same codes
    rintro (_ | t)
    · constructor
      · rintro ⟨e, he⟩; exact (codeE_ne_none hXm e he).elim
      · rintro ⟨e', he'⟩; exact (qE_ne_none hd hc hS hYm hYc e' he').elim
    constructor
    · rintro ⟨e, he⟩
      rcases codeE_cases hXm he with ⟨c, rfl, rfl, hcc⟩ | ⟨ℓ, rfl, d, a, o, hte, ha, ho⟩ |
          ⟨p, rfl, hp, x, hte, hx⟩
      · obtain ⟨c', hc'⟩ := consCorr_exists hc hS hcc
        exact ⟨c', qE_consumer hd hS hc'⟩
      · obtain ⟨ℓ', hℓ⟩ := consCorr_exists hc hS (hXc d a ha ℓ o ho)
        obtain ⟨d', a', o', ha', ho'⟩ :=
          (firstLeaf_corr hd hc hS hrk hXm hXc hXs hYm hYc hYs hℓ).1 ⟨d, a, o, ha, ho⟩
        obtain ⟨f', -, hf'⟩ := input_of_dup Y ha'
        exact ⟨f', qE_dupIn hd hS hf' ha' ho' hℓ⟩
      · have hL : X.leafSet (X.portEdge p) = ∅ := by rw [hp]; exact leafSet_disc hte hx
        obtain ⟨y, hy, hyi⟩ := (disc_iff hYm (portEquiv hd hS p)).2 ((disc_corr hd hc hS p).1 hL)
        exact ⟨_, qE_discIn hd hS ((Y.mem_ins y _).1 (by rw [hyi]; simp)) hy p rfl⟩
    · rintro ⟨e', he'⟩
      rcases qE_cases hd hS hYm he' with ⟨c, rfl, hcc⟩ | ⟨ℓ, ℓ', rfl, hℓ, d, a, o, -, ha, ho⟩ |
          ⟨p, rfl, hp, x, hte, hx⟩
      · exact ⟨c, codeE_consumer hcc.consumer.1⟩
      · obtain ⟨d₀, a₀, o₀, ha₀, ho₀⟩ :=
          (firstLeaf_corr hd hc hS hrk hXm hXc hXs hYm hYc hYs hℓ).2 ⟨d, a, o, ha, ho⟩
        obtain ⟨f, -, hf⟩ := input_of_dup X ha₀
        exact ⟨f, codeE_dupIn hf ha₀ ho₀⟩
      · have hL : Y.leafSet (Y.portEdge (portEquiv hd hS p)) = ∅ := by rw [hp]; exact leafSet_disc hte hx
        obtain ⟨x₀, hx₀, hxi⟩ := (disc_iff hXm p).2 ((disc_corr hd hc hS p).2 hL)
        exact ⟨_, codeE_discIn ((X.mem_ins x₀ _).1 (by rw [hxi]; simp)) hx₀ p rfl⟩
  · -- inputs
    intro x y hxy
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 (codeN_ne_none hXm x)
    rw [ht] at hxy
    rcases codeN_cases hXm ht with ⟨hl, rfl⟩ | ⟨ℓ, rfl, a, o, ha, ho⟩ | ⟨p, rfl, hdisc, hi⟩
    · rcases qN_cases hd hS hYm hxy.symm with ⟨x', hy, h₁, hx'⟩ | ⟨_, _, h₁, -⟩ | ⟨_, h₁, -⟩ <;>
        simp only [reduceCtorEq, Sum.inl.injEq] at h₁
      subst h₁
      have hπ : (π ⟨x, hl⟩).1 = y := congrArg Subtype.val hx'
      subst hπ
      refine List.ext_getElem (by rw [List.length_map, List.length_map,
        ins_length_eq_of_val (hS.val_eq _)]) fun i h₁ h₂ => ?_
      simp only [List.getElem_map]
      exact hlive_ins ⟨x, hl⟩ i (by simpa using h₁) (by simpa using h₂)
    · rcases qN_cases hd hS hYm hxy.symm with ⟨_, _, h₁, -⟩ | ⟨ℓ₂, ℓ', h₁, hℓ, a', o', ha', ho'⟩ |
          ⟨_, h₁, -⟩ <;> simp only [reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h₁
      subst h₁
      obtain ⟨f, hf, hfx⟩ := input_of_dup X ha
      obtain ⟨f', hf', hfy⟩ := input_of_dup Y ha'
      rw [hf, hf', List.map_singleton, List.map_singleton, codeE_dupIn hfx ha ho,
        qE_dupIn hd hS hfy ha' ho' hℓ]
    · rcases qN_cases hd hS hYm hxy.symm with ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩ |
          ⟨p₂, h₁, hdisc₂, hi₂⟩ <;> simp only [reduceCtorEq, Sum.inr.injEq] at h₁
      subst h₁
      rw [hi, hi₂, List.map_singleton, List.map_singleton,
        codeE_discIn ((X.mem_ins x _).1 (by rw [hi]; simp)) hdisc p rfl,
        qE_discIn hd hS ((Y.mem_ins y _).1 (by rw [hi₂]; simp)) hdisc₂ p rfl]
  · -- outputs
    intro x y hxy
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 (codeN_ne_none hXm x)
    rw [ht] at hxy
    rcases codeN_cases hXm ht with ⟨hl, rfl⟩ | ⟨ℓ, rfl, a, o, ha, ho⟩ | ⟨p, rfl, hdisc, hi⟩
    · rcases qN_cases hd hS hYm hxy.symm with ⟨x', hy, h₁, hx'⟩ | ⟨_, _, h₁, -⟩ | ⟨_, h₁, -⟩ <;>
        simp only [reduceCtorEq, Sum.inl.injEq] at h₁
      subst h₁
      have hπ : (π ⟨x, hl⟩).1 = y := congrArg Subtype.val hx'
      subst hπ
      refine List.ext_getElem (by rw [List.length_map, List.length_map,
        outs_length_eq_of_val (hS.val_eq _)]) fun j h₁ h₂ => ?_
      simp only [List.getElem_map]
      have hj : j < (X.outs x).length := by simpa using h₁
      have e₁ : (X.outs x)[j] = X.portEdge (.inr ⟨⟨x, hl⟩, ⟨j, hj⟩⟩) := rfl
      have e₂ : (Y.outs (π ⟨x, hl⟩).1)[j]'(by simpa using h₂) =
          Y.portEdge (portEquiv hd hS (.inr ⟨⟨x, hl⟩, ⟨j, hj⟩⟩)) := rfl
      rw [e₁, e₂, qE_port hd hc hS hrk hXm hXc hXs hrkX hYm hYc hYs hrkY]
    · rcases qN_cases hd hS hYm hxy.symm with ⟨_, _, h₁, -⟩ | ⟨ℓ₂, ℓ', h₁, hℓ, a', o', ha', ho'⟩ |
          ⟨_, h₁, -⟩ <;> simp only [reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h₁
      subst h₁
      obtain ⟨f, hf, hfx⟩ := input_of_dup X ha
      obtain ⟨f', hf', hfy⟩ := input_of_dup Y ha'
      -- the origins of the inputs are corresponding ports
      obtain ⟨q, hq⟩ := PGraph.exists_isOrigin X.dupCond f
      have hqℓ : X.IsOrigin q ℓ :=
        ⟨hq.1.tail ⟨x, ⟨a, ha⟩, hfx, (X.mem_outs x ℓ).1 (by rw [ho]; simp)⟩, hq.2⟩
      obtain ⟨p, rfl⟩ := origin_port_of_reachCod hqℓ (hXc x a ha ℓ o ho).reachCod
      obtain ⟨q', hq'⟩ := PGraph.exists_isOrigin Y.dupCond f'
      have hq'ℓ : Y.IsOrigin q' ℓ' :=
        ⟨hq'.1.tail ⟨y, ⟨a', ha'⟩, hfy, (Y.mem_outs y ℓ').1 (by rw [ho']; simp)⟩, hq'.2⟩
      have hq'p : q' = Y.portEdge (portEquiv hd hS p) :=
        PGraph.isOrigin_unique Y.dupCond hq'ℓ ((consCorr_origin hd hS hℓ p).1 hqℓ)
      subst hq'p
      rw [ho, ho']
      simp only [List.map_cons, List.map_nil]
      rw [codeE_consumer (hXc x a ha ℓ o ho), qE_consumer hd hS hℓ,
        codeE_second hXm hXc hXs hrkX ha hf ho hq, qE, codeE_second hYm hYc hYs hrkY ha' hf' ho' hq',
        nextOf_transport hd hS hc hrk hrkX (fun c h => (mem_leafSet.1 (Finset.mem_filter.1 h).1).2)
          (fun c h => (mem_leafSet.1 (Finset.mem_filter.1 h).1).2) (fun c c' hcc => by
            simp only [Finset.mem_filter]
            rw [leafSet_corr hd hS p hcc, hrk _ _ hcc, hrk _ _ hℓ])]
    · rcases qN_cases hd hS hYm hxy.symm with ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩ |
          ⟨p₂, h₁, hdisc₂, hi₂⟩ <;> simp only [reduceCtorEq, Sum.inr.injEq] at h₁
      subst h₁
      obtain ⟨b, hb⟩ := hdisc
      obtain ⟨b₂, hb₂⟩ := hdisc₂
      rw [X.val.outs_eq_nil_of_disc hb, Y.val.outs_eq_nil_of_disc hb₂]
      rfl
  · -- domains
    refine List.ext_getElem (by rw [List.length_map, List.length_map, dom_length_eq_of_domWord hd])
      fun j h₁ h₂ => ?_
    simp only [List.getElem_map]
    have hj : j < X.dom.length := by simpa using h₁
    have e₁ : X.dom[j] = X.portEdge (.inl ⟨⟨j, hj⟩⟩) := rfl
    have e₂ : Y.dom[j]'(by simpa using h₂) = Y.portEdge (portEquiv hd hS (.inl ⟨⟨j, hj⟩⟩)) := rfl
    rw [e₁, e₂, qE_port hd hc hS hrk hXm hXc hXs hrkX hYm hYc hYs hrkY]
  · -- codomains
    refine List.ext_getElem (by rw [List.length_map, List.length_map, cod_length_eq_of_codWord hc])
      fun i h₁ h₂ => ?_
    simp only [List.getElem_map]
    have hcc : ConsCorr π (X.cod[i]'(by simpa using h₁)) (Y.cod[i]'(by simpa using h₂)) :=
      Or.inl ⟨i, List.getElem?_eq_getElem _, List.getElem?_eq_getElem _⟩
    rw [codeE_consumer hcc.consumer.1, qE_consumer hd hS hcc]
  · -- labels of edges
    intro e e' hee
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 (codeE_ne_none hXm e)
    rw [ht] at hee
    rcases codeE_cases hXm ht with ⟨c, rfl, rfl, -⟩ | ⟨ℓ, rfl, d, a, o, hte, ha, ho⟩ |
        ⟨p, rfl, hp, x, hte, hx⟩
    · rcases qE_cases hd hS hYm hee.symm with ⟨c₂, h₁, hcc⟩ | ⟨_, _, h₁, -⟩ | ⟨_, h₁, -⟩ <;>
        simp only [reduceCtorEq, Sum.inl.injEq] at h₁
      subst h₁
      exact (hcc.v₀ hc hS).symm
    · rcases qE_cases hd hS hYm hee.symm with ⟨_, h₁, -⟩ | ⟨ℓ₂, ℓ', h₁, hℓ, d', a', o', hte', ha', ho'⟩ |
          ⟨_, h₁, -⟩ <;> simp only [reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h₁
      subst h₁
      have lab : ∀ {M : Type u₁} {F : Type u₂} (Z : Diagram G.toFreeGraphMonoid M F) {g : F} {z : M}
          {b : S} {l₀ l₁ : F}, Z.tgt g = some z → Z.val.v₁ z = G.dup b → Z.outs z = [l₀, l₁] →
          Z.val.v₀ g = Z.val.v₀ l₀ := by
        intro M F Z g z b l₀ l₁ hg hz hzo
        obtain ⟨g', hg', hgb⟩ := Z.val.ins_eq_of_dup hz
        obtain ⟨m₀, m₁, hm, hm₀, -⟩ := Z.val.outs_eq_of_t_dup hz
        have : g ∈ Z.ins z := (Z.mem_ins z g).2 hg
        rw [hg', List.mem_singleton] at this
        rw [hzo, List.cons.injEq] at hm
        rw [this, hgb, hm.1, hm₀]
      have lab' : ∀ {M : Type u₃} {F : Type u₄} (Z : Diagram G.toFreeGraphMonoid M F) {g : F} {z : M}
          {b : S} {l₀ l₁ : F}, Z.tgt g = some z → Z.val.v₁ z = G.dup b → Z.outs z = [l₀, l₁] →
          Z.val.v₀ g = Z.val.v₀ l₀ := by
        intro M F Z g z b l₀ l₁ hg hz hzo
        obtain ⟨g', hg', hgb⟩ := Z.val.ins_eq_of_dup hz
        obtain ⟨m₀, m₁, hm, hm₀, -⟩ := Z.val.outs_eq_of_t_dup hz
        have : g ∈ Z.ins z := (Z.mem_ins z g).2 hg
        rw [hg', List.mem_singleton] at this
        rw [hzo, List.cons.injEq] at hm
        rw [this, hgb, hm.1, hm₀]
      rw [lab X hte ha ho, lab' Y hte' ha' ho', hℓ.v₀ hc hS]
    · rcases qE_cases hd hS hYm hee.symm with ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨p₂, h₁, hp₂, -⟩ <;>
        simp only [reduceCtorEq, Sum.inr.injEq] at h₁
      subst h₁
      rw [← hp, ← hp₂, v₀_portEdge hd hS]
  · -- labels of nodes
    intro x y hxy
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 (codeN_ne_none hXm x)
    rw [ht] at hxy
    rcases codeN_cases hXm ht with ⟨hl, rfl⟩ | ⟨ℓ, rfl, a, o, ha, ho⟩ | ⟨p, rfl, hdisc, hi⟩
    · rcases qN_cases hd hS hYm hxy.symm with ⟨x', hy, h₁, hx'⟩ | ⟨_, _, h₁, -⟩ | ⟨_, h₁, -⟩ <;>
        simp only [reduceCtorEq, Sum.inl.injEq] at h₁
      subst h₁
      have := hS.val_eq ⟨x, hl⟩
      rw [hx'] at this
      exact this.symm
    · rcases qN_cases hd hS hYm hxy.symm with ⟨_, _, h₁, -⟩ | ⟨ℓ₂, ℓ', h₁, hℓ, a', o', ha', ho'⟩ |
          ⟨_, h₁, -⟩ <;> simp only [reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h₁
      subst h₁
      obtain ⟨m₀, m₁, hm, hm₀, -⟩ := X.val.outs_eq_of_t_dup ha
      obtain ⟨m₀', m₁', hm', hm₀', -⟩ := Y.val.outs_eq_of_t_dup ha'
      rw [ho, List.cons.injEq] at hm
      rw [ho', List.cons.injEq] at hm'
      rw [ha, ha', ← hm₀, ← hm₀', ← hm.1, ← hm'.1, hℓ.v₀ hc hS]
    · rcases qN_cases hd hS hYm hxy.symm with ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩ |
          ⟨p₂, h₁, hdisc₂, hi₂⟩ <;> simp only [reduceCtorEq, Sum.inr.injEq] at h₁
      subst h₁
      obtain ⟨b, hb⟩ := hdisc
      obtain ⟨b₂, hb₂⟩ := hdisc₂
      obtain ⟨g, hg, hgb⟩ := X.val.ins_eq_of_disc hb
      obtain ⟨g₂, hg₂, hgb₂⟩ := Y.val.ins_eq_of_disc hb₂
      rw [hi, List.cons.injEq] at hg
      rw [hi₂, List.cons.injEq] at hg₂
      rw [hb, hb₂, ← hgb, ← hgb₂, ← hg.1, ← hg₂.1, v₀_portEdge hd hS]

end Diagram

end FreeMarkov
