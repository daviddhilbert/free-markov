/-
Free Markov categories, Stage 4: the swap and the rotation keep the live nodes, the consumers and
their origins literally (on the same nodes and edges), and keep Markov minimality.
-/
module

public import FreeMarkov.Stage4.MoveSteps

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

theorem TStep.mono {T T' : Set (Template.{0} G.toFreeGraphMonoid)} {N' : Type u₃} {E' : Type u₄}
    {X : Diagram G.toFreeGraphMonoid N E} {Y : Diagram G.toFreeGraphMonoid N' E'} (h : TStep T X Y)
    (hT : T ⊆ T') : TStep T' X Y := by
  obtain ⟨τ, hτ, rest⟩ := h
  exact ⟨τ, hT hτ, rest⟩

section Generic

variable {X Y : Diagram G.toFreeGraphMonoid N E} {NΩ : Type u₃} {EΩ : Type u₄} {NΛ : Type u₅}
  {EΛ : Type u₆} {Ω : PDiagram G.toFreeGraphMonoid NΩ EΩ} {Λ : PDiagram G.toFreeGraphMonoid NΛ EΛ}
  {ιN : NΩ → N} {ιE : EΩ → E}
  {α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}} {β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}}
  (hE : Emb X Ω ιN ιE) (hC : StepCond Ω Λ α β) (P : CanonProj X Ω ιN ιE α β Y)
  (hpN : ∀ x, (∀ z, ιN z ≠ x) → P.pN x = .inl x)
include hE hC P hpN

theorem live_forward_same [Finite E] {x : N} (hx : X.Live x) : Y.Live x :=
  live_forward hE P hC hx (hpN x (live_outside hE hC hx))

theorem live_iff_of_card [Finite N] [Finite E]
    (hcard : Nat.card {y // Y.Live y} ≤ Nat.card {x // X.Live x}) (x : N) : X.Live x ↔ Y.Live x := by
  refine ⟨live_forward_same hE hC P hpN, fun hy => ?_⟩
  let f : {x // X.Live x} → {y // Y.Live y} := fun x => ⟨x.1, live_forward_same hE hC P hpN x.2⟩
  have hf : Function.Injective f := fun x x' h => Subtype.ext (by simpa [f] using congrArg Subtype.val h)
  obtain ⟨x', hx'⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨x, hy⟩
  have : x'.1 = x := congrArg Subtype.val hx'
  exact this ▸ x'.2

omit hpN in
theorem origin_same [Finite E] (hpE : ∀ e, (∀ z, X.src e ≠ some (ιN z)) → P.pE e = .inl e)
    (hpF : ∀ g, (∀ z, X.tgt g ≠ some (ιN z)) → P.pE g = canonF ιE α β g) {q g : E}
    (hq : X.IsOrigin q g) (hg : X.Consumer g) : Y.IsOrigin q g := by
  have hgo : ∀ z, X.tgt g ≠ some (ιN z) := by
    rcases hg with h | ⟨x, hx, hl⟩
    · intro z hz; rw [h] at hz; cases hz
    · intro z hz
      rw [hx, Option.some.injEq] at hz
      exact live_outside hE hC hl z hz.symm
  exact origin_forward hE P hC hq hg.reachCod hgo (hpE q (origin_outside hE hC hq hg.reachCod))
    (hpF g hgo)

end Generic

/-! ### Moves -/

/-- A move: a surgery with (4.1) or (4.3) on the same nodes and edges which keeps the inputs,
targets, domain, codomain and labels, the live nodes, the consumers and their origins. -/
structure MoveRel (X Y : Diagram G.toFreeGraphMonoid N E) : Prop where
  tstep : TStep G.congTemplates X Y
  live : ∀ x, X.Live x ↔ Y.Live x
  origin : ∀ q g, X.Consumer g → X.IsOrigin q g → Y.IsOrigin q g
  ins : Y.ins = X.ins
  tgt : Y.tgt = X.tgt
  dom : Y.dom = X.dom
  cod : Y.cod = X.cod
  v₀ : Y.val.v₀ = X.val.v₀
  v₁ : Y.val.v₁ = X.val.v₁
  outs_nondup : ∀ x, ¬ X.val.IsDup x → Y.outs x = X.outs x

theorem MoveRel.consumer_iff {X Y : Diagram G.toFreeGraphMonoid N E} (h : MoveRel X Y) (g : E) :
    X.Consumer g ↔ Y.Consumer g := by
  unfold Consumer PGraph.Consumer
  rw [show Y.toPGraph.tgt = X.toPGraph.tgt from h.tgt]
  simp only [show ∀ x, Y.toPGraph.Live Y.val.IsDup x ↔ X.toPGraph.Live X.val.IsDup x from
    fun x => (h.live x).symm]

theorem moveRel_swap [Finite N] [Finite E] {X : Diagram G.toFreeGraphMonoid N E} {d : N}
    (D : SwapData X d) : MoveRel X (X.swap D) := by
  have hst := tStep_swap D (G.cocommT_mem_cong D.a)
  have hC := G.markovTemplates_stepCond _ (G.cocommT_mem D.a)
  have hcard := (TStep.symm G.congTemplates_isSymmetric.symm_mem hst).card_live_le
    (fun τ hτ => G.markovTemplates_stepCond τ (G.congTemplates_subset hτ))
  have hpN : ∀ x, (∀ z, D.embΩ.ιN z ≠ x) → D.canon.pN x = .inl x :=
    rwPN_inl D.hN
  have hpE : ∀ e, (∀ z, X.src e ≠ some (D.embΩ.ιN z)) → D.canon.pE e = .inl e :=
    rwPE_inl D.embΩ.toEmb D.hinner
  have hpF : ∀ g, (∀ z, X.tgt g ≠ some (D.embΩ.ιN z)) →
      D.canon.pE g = canonF D.embΩ.ιE (G.cocommT D.a).α (G.cocommT D.a).β g :=
    rwPE_canonF D.embΩ.toEmb D.embΛ.toEmb D.hinner
      (matching_emb _ (by rw [D.embΛ_dom, D.embΩ_dom])) (matching_emb' _ (by rw [D.embΛ_cod, D.embΩ_cod]))
  exact ⟨hst, live_iff_of_card D.embΩ.toEmb hC D.canon hpN hcard,
    fun _ _ hg hq => origin_same D.embΩ.toEmb hC D.canon hpE hpF hq hg,
    rfl, rfl, rfl, rfl, rfl, rfl, fun x hx => swap.outs_of_ne D fun h => hx (h ▸ ⟨D.a, D.hd⟩)⟩

theorem moveRel_rotate [Finite N] [Finite E] {X : Diagram G.toFreeGraphMonoid N E} {p d : N}
    (R : RotData X p d) : MoveRel X (X.rotate R) := by
  have hst := tStep_rotate R (G.coassT_mem_cong R.a)
  have hC := G.markovTemplates_stepCond _ (G.coassT_mem R.a)
  have hcard := (TStep.symm G.congTemplates_isSymmetric.symm_mem hst).card_live_le
    (fun τ hτ => G.markovTemplates_stepCond τ (G.congTemplates_subset hτ))
  have hpN : ∀ x, (∀ z, R.embΩ.ιN z ≠ x) → R.canon.pN x = .inl x :=
    rwPN_inl R.hN
  have hpE : ∀ e, (∀ z, X.src e ≠ some (R.embΩ.ιN z)) → R.canon.pE e = .inl e :=
    rwPE_inl R.embΩ.toEmb R.hinner
  have hpF : ∀ g, (∀ z, X.tgt g ≠ some (R.embΩ.ιN z)) →
      R.canon.pE g = canonF R.embΩ.ιE (G.coassT R.a).α (G.coassT R.a).β g :=
    rwPE_canonF R.embΩ.toEmb R.embΛ.toEmb R.hinner
      (matching_emb _ (by rw [R.embΛ_dom, R.embΩ_dom])) (matching_emb' _ (by rw [R.embΛ_cod, R.embΩ_cod]))
  exact ⟨hst, live_iff_of_card R.embΩ.toEmb hC R.canon hpN hcard,
    fun _ _ hg hq => origin_same R.embΩ.toEmb hC R.canon hpE hpF hq hg,
    rfl, rfl, rfl, rfl, rfl, rfl, fun x hx => rotOuts_of_ne R (fun h => hx (h ▸ ⟨R.a, R.hp⟩))
      (fun h => hx (h ▸ ⟨R.a, R.hd⟩))⟩

/-! ### Minimality is kept -/

/-- A diagram with the same skeleton and the same labels on the same nodes as a Markov minimal
diagram is Markov minimal. -/
theorem minimal_of_sameSkeleton [Finite N] [Finite E] {X Y : Diagram G.toFreeGraphMonoid N E}
    (hX : X.MarkovMinimal) (hS : SameSkeleton X Y) (hv : Y.val.v₁ = X.val.v₁) : Y.MarkovMinimal := by
  obtain ⟨hd, hc, π, hπ⟩ := hS
  obtain ⟨⟨π', hπ', -⟩, -⟩ := skeletonIso_items hd hc hπ
  intro y hy
  by_contra hyd
  set f := Y.val.v₁ y with hf
  have hfd : ∀ x, X.val.v₁ x = f → ¬ X.QuasiTerminal x := by
    intro x hx hq
    obtain ⟨b, hb⟩ := hX x hq
    exact hyd ⟨b, by rw [← hf, ← hx, hb]⟩
  -- the nodes labelled `f` are all outside `Δ_X`
  have e₁ : {x : {x // ¬ X.QuasiTerminal x} // X.val.v₁ x.1 = f} ≃ {x // X.val.v₁ x = f} :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, hfd x.1 x.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e₂ : {x : {x // ¬ X.QuasiTerminal x} // X.val.v₁ x.1 = f} ≃
      {y : {y // ¬ Y.QuasiTerminal y} // Y.val.v₁ y.1 = f} :=
    π'.subtypeEquiv fun x => by rw [hπ' x]
  have e₃ : {x // X.val.v₁ x = f} ≃ {y // Y.val.v₁ y = f} :=
    Equiv.subtypeEquivRight fun x => by rw [hv]
  let g : {y : {y // ¬ Y.QuasiTerminal y} // Y.val.v₁ y.1 = f} → {y // Y.val.v₁ y = f} :=
    fun y => ⟨y.1.1, y.2⟩
  have hg : Function.Injective g := fun a b h => Subtype.ext (Subtype.ext (by simpa [g] using congrArg Subtype.val h))
  have hcard : Nat.card {y // Y.val.v₁ y = f} ≤ Nat.card {y : {y // ¬ Y.QuasiTerminal y} // Y.val.v₁ y.1 = f} := by
    rw [← Nat.card_congr e₂, Nat.card_congr e₁, Nat.card_congr e₃]
  obtain ⟨y', hy'⟩ := (hg.bijective_of_nat_card_le hcard).2 ⟨y, rfl⟩
  have : y'.1.1 = y := congrArg Subtype.val hy'
  exact y'.1.2 (this ▸ hy)

theorem MoveRel.minimal [Finite N] [Finite E] {X Y : Diagram G.toFreeGraphMonoid N E}
    (h : MoveRel X Y) (hX : X.MarkovMinimal) : Y.MarkovMinimal :=
  minimal_of_sameSkeleton hX
    (TStep.sameSkeleton_markov (h.tstep.mono G.congTemplates_subset)) h.v₁

end Diagram

end FreeMarkov
