/-
Free Markov categories, Stage 4: the correspondence of consumers given by a skeleton bijection.

`ConsCorr π c c'`: the consumer `c` of `X` and the consumer `c'` of `Y` sit in corresponding slots
(the same position in the codomains, or the same input of corresponding live nodes).  It is a
bijection between the consumers (`consCorr_exists`, `consCorr_unique`), it matches the origins at
corresponding ports (`consCorr_origin`), and it is unchanged by moves.
-/
module

public import FreeMarkov.Stage4.CodingA

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}
  {X : Diagram G.toFreeGraphMonoid N E} {Y : Diagram G.toFreeGraphMonoid N' E'}

theorem _root_.FreeMarkov.nodup_idx_eq {α : Type*} {l : List α} (h : l.Nodup) {i j : ℕ} {a : α}
    (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hi
  obtain ⟨hj', hj''⟩ := List.getElem?_eq_some_iff.1 hj
  exact (h.getElem_inj_iff).1 hj''.symm

/-- Corresponding consumers. -/
def ConsCorr (π : {x // X.Live x} ≃ {y // Y.Live y}) (c : E) (c' : E') : Prop :=
  (∃ i : ℕ, X.cod[i]? = some c ∧ Y.cod[i]? = some c') ∨
    ∃ (x : {x // X.Live x}) (i : ℕ), (X.ins x.1)[i]? = some c ∧ (Y.ins (π x).1)[i]? = some c'

variable {π : {x // X.Live x} ≃ {y // Y.Live y}}

theorem ConsCorr.consumer {c : E} {c' : E'} (h : ConsCorr π c c') : X.Consumer c ∧ Y.Consumer c' := by
  rcases h with ⟨i, h₁, h₂⟩ | ⟨x, i, h₁, h₂⟩
  · exact ⟨Or.inl ((X.mem_cod c).1 (List.mem_of_getElem? h₁)),
      Or.inl ((Y.mem_cod c').1 (List.mem_of_getElem? h₂))⟩
  · exact ⟨Or.inr ⟨x.1, (X.mem_ins _ c).1 (List.mem_of_getElem? h₁), x.2⟩,
      Or.inr ⟨_, (Y.mem_ins _ c').1 (List.mem_of_getElem? h₂), (π x).2⟩⟩

theorem ConsCorr.symm {c : E} {c' : E'} (h : ConsCorr π c c') : ConsCorr π.symm c' c := by
  rcases h with ⟨i, h₁, h₂⟩ | ⟨x, i, h₁, h₂⟩
  · exact Or.inl ⟨i, h₂, h₁⟩
  · refine Or.inr ⟨π x, i, h₂, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact h₁

theorem consCorr_symm_iff {c : E} {c' : E'} : ConsCorr π.symm c' c ↔ ConsCorr π c c' := by
  refine ⟨fun h => ?_, ConsCorr.symm⟩
  have := h.symm
  rwa [Equiv.symm_symm] at this

theorem ConsCorr.originsMatch (hS : SkeletonIso X Y π) {c : E} {c' : E'} (h : ConsCorr π c c') :
    OriginsMatch π c c' := by
  rcases h with ⟨i, h₁, h₂⟩ | ⟨x, i, h₁, h₂⟩
  · exact hS.cod_match i c c' h₁ h₂
  · exact hS.ins_match x i c c' h₁ h₂

theorem consCorr_exists (hc : X.codWord = Y.codWord) (hS : SkeletonIso X Y π) {c : E}
    (h : X.Consumer c) : ∃ c', ConsCorr π c c' := by
  rcases h with h | ⟨x, hx, hl⟩
  · obtain ⟨i, hi⟩ := exists_getElem?_of_mem ((X.mem_cod c).2 h)
    obtain ⟨c', hc'⟩ := exists_getElem?_of_length_eq (cod_length_eq_of_codWord hc) hi
    exact ⟨c', Or.inl ⟨i, hi, hc'⟩⟩
  · obtain ⟨i, hi⟩ := exists_getElem?_of_mem ((X.mem_ins x c).2 hx)
    obtain ⟨c', hc'⟩ := exists_getElem?_of_length_eq
      (ins_length_eq_of_val (hS.val_eq ⟨x, hl⟩)).symm hi
    exact ⟨c', Or.inr ⟨⟨x, hl⟩, i, hi, hc'⟩⟩

theorem consCorr_unique {c : E} {c' c'' : E'} (h₁ : ConsCorr π c c') (h₂ : ConsCorr π c c'') :
    c' = c'' := by
  rcases h₁ with ⟨i, hi, hi'⟩ | ⟨x, i, hi, hi'⟩ <;> rcases h₂ with ⟨j, hj, hj'⟩ | ⟨y, j, hj, hj'⟩
  · have : i = j := nodup_idx_eq X.cod_nodup hi hj
    subst this
    rw [hi'] at hj'
    exact Option.some.inj hj'
  · have h₁ : X.tgt c = none := (X.mem_cod c).1 (List.mem_of_getElem? hi)
    have h₂ : X.tgt c = some y.1 := (X.mem_ins _ c).1 (List.mem_of_getElem? hj)
    rw [h₁] at h₂; cases h₂
  · have h₁ : X.tgt c = none := (X.mem_cod c).1 (List.mem_of_getElem? hj)
    have h₂ : X.tgt c = some x.1 := (X.mem_ins _ c).1 (List.mem_of_getElem? hi)
    rw [h₁] at h₂; cases h₂
  · have hxy : x = y := by
      have h₁ : X.tgt c = some x.1 := (X.mem_ins _ c).1 (List.mem_of_getElem? hi)
      have h₂ : X.tgt c = some y.1 := (X.mem_ins _ c).1 (List.mem_of_getElem? hj)
      rw [h₁, Option.some.injEq] at h₂
      exact Subtype.ext h₂
    subst hxy
    have : i = j := nodup_idx_eq (X.ins_nodup _) hi hj
    subst this
    rw [hi'] at hj'
    exact Option.some.inj hj'

theorem consCorr_unique' {c c'' : E} {c' : E'} (h₁ : ConsCorr π c c') (h₂ : ConsCorr π c'' c') :
    c = c'' :=
  consCorr_unique h₁.symm h₂.symm

/-- Corresponding consumers have their origins at corresponding ports. -/
theorem consCorr_origin (hd : X.domWord = Y.domWord) (hS : SkeletonIso X Y π) {c : E} {c' : E'}
    (h : ConsCorr π c c') (p : X.PortT) :
    X.IsOrigin (X.portEdge p) c ↔ Y.IsOrigin (Y.portEdge (portEquiv hd hS p)) c' := by
  rw [← originAt_portPos_iff, ← originAt_portPos_iff]
  have hm := h.originsMatch hS
  rcases p with ⟨j⟩ | ⟨y, j⟩
  · exact hm.1 j.down.1
  · exact hm.2 y j.1

theorem ConsCorr.v₀ (hc : X.codWord = Y.codWord) (hS : SkeletonIso X Y π) {c : E} {c' : E'}
    (h : ConsCorr π c c') : Y.val.v₀ c' = X.val.v₀ c := by
  rcases h with ⟨i, hi, hi'⟩ | ⟨x, i, hi, hi'⟩
  · have h' : X.cod.map X.val.v₀ = Y.cod.map Y.val.v₀ := FreeMonoid.ofList.injective hc
    have := congrArg (fun l => l[i]?) h'
    simp only [List.getElem?_map, hi, hi', Option.map_some, Option.some.injEq] at this
    exact this.symm
  · have h₁ := X.val.s_v₁ x.1
    have h₂ := Y.val.s_v₁ (π x).1
    rw [hS.val_eq x, h₁] at h₂
    have h' : (X.ins x.1).map X.val.v₀ = (Y.ins (π x).1).map Y.val.v₀ := FreeMonoid.ofList.injective h₂
    have := congrArg (fun l => l[i]?) h'
    simp only [List.getElem?_map, hi, hi', Option.map_some, Option.some.injEq] at this
    exact this.symm

/-- Moves do not change the correspondence of consumers. -/
theorem consCorr_of_moves [Finite E] [Finite E'] {X' : Diagram G.toFreeGraphMonoid N E}
    {Y' : Diagram G.toFreeGraphMonoid N' E'} (hX : ReflTransGen MoveRel X X')
    (hY : ReflTransGen MoveRel Y Y') {c : E} {c' : E'} :
    ConsCorr ((Equiv.subtypeEquivRight (MoveRel.chain hX).live).symm.trans
      (π.trans (Equiv.subtypeEquivRight (MoveRel.chain hY).live))) c c' ↔ ConsCorr π c c' := by
  have cX := MoveRel.chain hX
  have cY := MoveRel.chain hY
  unfold ConsCorr
  rw [show X'.cod = X.cod from cX.cod, show Y'.cod = Y.cod from cY.cod,
    show X'.ins = X.ins from cX.ins, show Y'.ins = Y.ins from cY.ins]
  refine or_congr Iff.rfl ⟨fun ⟨x, i, h₁, h₂⟩ => ⟨⟨x.1, (cX.live x.1).2 x.2⟩, i, h₁, h₂⟩,
    fun ⟨x, i, h₁, h₂⟩ => ⟨⟨x.1, (cX.live x.1).1 x.2⟩, i, h₁, h₂⟩⟩

end Diagram

end FreeMarkov
