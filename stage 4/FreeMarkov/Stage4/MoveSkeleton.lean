/-
Free Markov categories, Stage 4: chains of moves keep everything a skeleton bijection refers to,
so a skeleton bijection between two diagrams is also one between the diagrams reached from them by
moves (`SkeletonIso.of_moves`).
-/
module

public import FreeMarkov.Stage4.Normalize2

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

namespace MoveRel

variable {X Y : Diagram G.toFreeGraphMonoid N E}

/-- What a chain of moves keeps. -/
structure Chain (X Y : Diagram G.toFreeGraphMonoid N E) : Prop where
  live : ∀ x, X.Live x ↔ Y.Live x
  origin : ∀ q g, X.Consumer g → X.IsOrigin q g → Y.IsOrigin q g
  ins : Y.ins = X.ins
  tgt : Y.tgt = X.tgt
  dom : Y.dom = X.dom
  cod : Y.cod = X.cod
  v₀ : Y.val.v₀ = X.val.v₀
  v₁ : Y.val.v₁ = X.val.v₁
  outs_nondup : ∀ x, ¬ X.val.IsDup x → Y.outs x = X.outs x

theorem chain (h : ReflTransGen MoveRel X Y) : Chain X Y := by
  induction h with
  | refl => exact ⟨fun _ => Iff.rfl, fun _ _ _ h => h, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | @tail Y Z _ h ih =>
    refine ⟨fun x => (ih.live x).trans (h.live x), fun q g hg hq => h.origin q g ?_ (ih.origin q g hg hq),
      h.ins.trans ih.ins, h.tgt.trans ih.tgt, h.dom.trans ih.dom, h.cod.trans ih.cod,
      h.v₀.trans ih.v₀, h.v₁.trans ih.v₁, fun x hx => ?_⟩
    · unfold Consumer PGraph.Consumer at hg ⊢
      rw [show Y.toPGraph.tgt = X.toPGraph.tgt from ih.tgt]
      simp only [show ∀ x, Y.toPGraph.Live Y.val.IsDup x ↔ X.toPGraph.Live X.val.IsDup x from
        fun x => (ih.live x).symm]
      exact hg
    · have hx' : ¬ Y.val.IsDup x := by
        unfold Valuation.IsDup at hx ⊢
        rw [show Y.val.v₁ = X.val.v₁ from ih.v₁]
        exact hx
      rw [h.outs_nondup x hx', ih.outs_nondup x hx]

theorem Chain.consumer_iff (h : Chain X Y) (g : E) : X.Consumer g ↔ Y.Consumer g := by
  unfold Consumer PGraph.Consumer
  rw [show Y.toPGraph.tgt = X.toPGraph.tgt from h.tgt]
  simp only [show ∀ x, Y.toPGraph.Live Y.val.IsDup x ↔ X.toPGraph.Live X.val.IsDup x from
    fun x => (h.live x).symm]

theorem Chain.origin_iff [Finite E] (h : Chain X Y) {q g : E} (hg : X.Consumer g) :
    X.IsOrigin q g ↔ Y.IsOrigin q g := by
  refine ⟨h.origin q g hg, fun hq => ?_⟩
  obtain ⟨q₀, hq₀⟩ := PGraph.exists_isOrigin X.dupCond g
  rw [PGraph.isOrigin_unique Y.dupCond hq (h.origin q₀ g hg hq₀)]
  exact hq₀

theorem Chain.originAt_iff [Finite E] (h : Chain X Y) {g : E} (hg : X.Consumer g) (P : Port N)
    (hP : ∀ y j, P = .out y j → X.Live y) : X.OriginAt g P ↔ Y.OriginAt g P := by
  cases P with
  | dom j =>
    simp only [OriginAt]
    rw [h.dom]
    exact exists_congr fun q => and_congr Iff.rfl (h.origin_iff hg)
  | out y j =>
    simp only [OriginAt]
    rw [h.outs_nondup y (hP y j rfl).1]
    exact exists_congr fun q => and_congr Iff.rfl (h.origin_iff hg)

end MoveRel

variable {N' : Type u₃} {E' : Type u₄}

/-- **Skeleton bijections survive moves.** -/
theorem SkeletonIso.of_moves [Finite E] [Finite E'] {X X' : Diagram G.toFreeGraphMonoid N E}
    {Y Y' : Diagram G.toFreeGraphMonoid N' E'} {π : {x // X.Live x} ≃ {y // Y.Live y}}
    (h : SkeletonIso X Y π) (hX : ReflTransGen MoveRel X X') (hY : ReflTransGen MoveRel Y Y') :
    SkeletonIso X' Y' ((Equiv.subtypeEquivRight (MoveRel.chain hX).live).symm.trans
      (π.trans (Equiv.subtypeEquivRight (MoveRel.chain hY).live))) := by
  have cX := MoveRel.chain hX
  have cY := MoveRel.chain hY
  have hm : ∀ e e', X.Consumer e → Y.Consumer e' → OriginsMatch π e e' →
      OriginsMatch ((Equiv.subtypeEquivRight cX.live).symm.trans
        (π.trans (Equiv.subtypeEquivRight cY.live))) e e' := by
    intro e e' he he' hmm
    refine ⟨fun j => ?_, fun y j => ?_⟩
    · rw [← cX.originAt_iff he _ (fun _ _ h => by cases h),
        ← cY.originAt_iff he' _ (fun _ _ h => by cases h)]
      exact hmm.1 j
    · have hy : X.Live y.1 := (cX.live y.1).2 y.2
      rw [← cX.originAt_iff he _ (fun _ _ h => by cases h; exact hy),
        ← cY.originAt_iff he' _ (fun _ _ h => by cases h; exact (π ⟨y.1, hy⟩).2)]
      exact hmm.2 ⟨y.1, hy⟩ j
  refine ⟨fun x => ?_, fun i e e' he he' => ?_, fun x i e e' he he' => ?_⟩
  · show Y'.val.v₁ (π ⟨x.1, _⟩).1 = X'.val.v₁ x.1
    rw [show Y'.val.v₁ = Y.val.v₁ from cY.v₁, show X'.val.v₁ = X.val.v₁ from cX.v₁]
    exact h.val_eq _
  · rw [show X'.cod = X.cod from cX.cod] at he
    rw [show Y'.cod = Y.cod from cY.cod] at he'
    exact hm e e' (Or.inl ((X.mem_cod e).1 (List.mem_of_getElem? he)))
      (Or.inl ((Y.mem_cod e').1 (List.mem_of_getElem? he'))) (h.cod_match i e e' he he')
  · have hx : X.Live x.1 := (cX.live x.1).2 x.2
    rw [show X'.ins = X.ins from cX.ins] at he
    rw [show Y'.ins = Y.ins from cY.ins] at he'
    exact hm e e' (Or.inr ⟨x.1, (X.mem_ins _ e).1 (List.mem_of_getElem? he), hx⟩)
      (Or.inr ⟨_, (Y.mem_ins _ e').1 (List.mem_of_getElem? he'), (π ⟨x.1, hx⟩).2⟩)
      (h.ins_match ⟨x.1, hx⟩ i e e' he he')

end Diagram

end FreeMarkov
