/-
Free Markov categories, Stage 4: the skeleton of a disjoint union with a diagram without live
nodes (used for the uniqueness in the third item of Lemma 4.5).

* The notions of Section 4 in `Υ ⊗ Ω` restricted to the edges and nodes of `Υ`.
* `SameSkeleton.of_tensor`: if `Ω`, `Ω'` have no live node, then `Υ ⊗ Ω` and `Υ' ⊗ Ω'` have the
  same skeleton only if `Υ` and `Υ'` do (given the same domain and codomain).
-/
module

public import FreeMarkov.Stage4.Reanchor

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace FreeMarkov

open Relation

theorem List.getElem?_append_map_inl {α : Type*} {β : Type*} (l₁ : List α) (l₂ : List β) (j : ℕ)
    (x : α) : (l₁.map Sum.inl ++ l₂.map Sum.inr)[j]? = some (Sum.inl x) ↔ l₁[j]? = some x := by
  by_cases hj : j < l₁.length
  · rw [List.getElem?_append_left (by simpa using hj), List.getElem?_map]
    cases l₁[j]? <;> simp
  · rw [List.getElem?_append_right (by simpa using hj), List.getElem?_map,
      List.getElem?_eq_none (not_lt.1 hj)]
    cases l₂[j - (l₁.map Sum.inl).length]? <;> simp

theorem List.getElem?_append_map_inl' {α : Type*} {β : Type*} (l₁ : List α) (l₂ : List β) (j : ℕ)
    (x : α) (h : l₁[j]? = some x) : (l₁.map Sum.inl ++ l₂.map Sum.inr)[j]? = some (Sum.inl x) :=
  (List.getElem?_append_map_inl l₁ l₂ j x).2 h

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

section Tensor

variable {Υ : Diagram G.toFreeGraphMonoid N E} {Ω : Diagram G.toFreeGraphMonoid N' E'}

theorem tensor_tgt_inl_eq {d : E ⊕ E'} {x : N} (h : (Υ.tensor Ω).tgt d = some (.inl x)) :
    ∃ d', d = .inl d' ∧ Υ.tgt d' = some x := by
  rcases d with d | d
  · refine ⟨d, rfl, ?_⟩
    change (Υ.tgt d).map Sum.inl = _ at h
    cases hd : Υ.tgt d <;> rw [hd] at h <;> simp_all
  · change (Ω.tgt d).map Sum.inr = _ at h
    cases hd : Ω.tgt d <;> rw [hd] at h <;> simp at h

theorem tensor_src_inl_eq {d : E ⊕ E'} {x : N} (h : (Υ.tensor Ω).src d = some (.inl x)) :
    ∃ d', d = .inl d' ∧ Υ.src d' = some x := by
  rcases d with d | d
  · refine ⟨d, rfl, ?_⟩
    change (Υ.src d).map Sum.inl = _ at h
    cases hd : Υ.src d <;> rw [hd] at h <;> simp_all
  · change (Ω.src d).map Sum.inr = _ at h
    cases hd : Ω.src d <;> rw [hd] at h <;> simp at h

theorem tensor_tgt_inl (e : E) : (Υ.tensor Ω).tgt (.inl e) = (Υ.tgt e).map .inl := rfl
theorem tensor_src_inl (e : E) : (Υ.tensor Ω).src (.inl e) = (Υ.src e).map .inl := rfl
theorem tensor_tgt_inr (e : E') : (Υ.tensor Ω).tgt (.inr e) = (Ω.tgt e).map .inr := rfl
theorem tensor_src_inr (e : E') : (Υ.tensor Ω).src (.inr e) = (Ω.src e).map .inr := rfl

theorem tensor_step_inl {e : E} {d : E ⊕ E'} (h : (Υ.tensor Ω).toPGraph.Step (.inl e) d) :
    ∃ e', d = .inl e' ∧ Υ.toPGraph.Step e e' := by
  obtain ⟨z, hz, hz'⟩ := h
  rw [tensor_tgt_inl] at hz
  cases hx : Υ.tgt e with
  | none => rw [hx] at hz; cases hz
  | some x =>
    rw [hx] at hz
    cases hz
    obtain ⟨d', rfl, hd'⟩ := tensor_src_inl_eq hz'
    exact ⟨d', rfl, x, hx, hd'⟩

theorem tensor_step_inl_inl {e e' : E} :
    (Υ.tensor Ω).toPGraph.Step (.inl e) (.inl e') ↔ Υ.toPGraph.Step e e' := by
  constructor
  · intro h
    obtain ⟨d, hd, h'⟩ := tensor_step_inl h
    cases hd
    exact h'
  · rintro ⟨x, hx, hx'⟩
    exact ⟨.inl x, by rw [tensor_tgt_inl, hx]; rfl, by rw [tensor_src_inl, hx']; rfl⟩

theorem tensor_reflTransGen_inl {e : E} {d : E ⊕ E'}
    (h : ReflTransGen (Υ.tensor Ω).toPGraph.Step (.inl e) d) :
    ∃ e', d = .inl e' ∧ ReflTransGen Υ.toPGraph.Step e e' := by
  induction h with
  | refl => exact ⟨e, rfl, ReflTransGen.refl⟩
  | tail _ hst ih =>
    obtain ⟨e₁, rfl, h₁⟩ := ih
    obtain ⟨e₂, rfl, h₂⟩ := tensor_step_inl hst
    exact ⟨e₂, rfl, h₁.tail h₂⟩

theorem tensor_reflTransGen_inl_inl {e e' : E} (h : ReflTransGen Υ.toPGraph.Step e e') :
    ReflTransGen (Υ.tensor Ω).toPGraph.Step (.inl e) (.inl e') := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hst ih => exact ih.tail (tensor_step_inl_inl.2 hst)

theorem tensor_reachCod_inl (e : E) :
    (Υ.tensor Ω).toPGraph.ReachCod (.inl e) ↔ Υ.toPGraph.ReachCod e := by
  constructor
  · rintro ⟨c, hc, hc'⟩
    obtain ⟨c', rfl, h⟩ := tensor_reflTransGen_inl hc
    refine ⟨c', h, ?_⟩
    rw [tensor_tgt_inl] at hc'
    cases hx : Υ.tgt c' with
    | none => rfl
    | some x => rw [hx] at hc'; cases hc'
  · rintro ⟨c, hc, hc'⟩
    exact ⟨.inl c, tensor_reflTransGen_inl_inl hc, by rw [tensor_tgt_inl, hc']; rfl⟩

theorem tensor_isDup_inl (x : N) : (Υ.tensor Ω).val.IsDup (.inl x) ↔ Υ.val.IsDup x := Iff.rfl
theorem tensor_isDup_inr (y : N') : (Υ.tensor Ω).val.IsDup (.inr y) ↔ Ω.val.IsDup y := Iff.rfl

theorem tensor_live_inl (x : N) : (Υ.tensor Ω).Live (.inl x) ↔ Υ.Live x := by
  change ¬ _ ∧ (∃ e ∈ (Υ.outs x).map Sum.inl, _) ↔ ¬ _ ∧ ∃ e ∈ Υ.outs x, _
  simp only [List.mem_map]
  constructor
  · rintro ⟨h₁, _, ⟨e, he, rfl⟩, h₂⟩
    exact ⟨h₁, e, he, (tensor_reachCod_inl e).1 h₂⟩
  · rintro ⟨h₁, e, he, h₂⟩
    exact ⟨h₁, _, ⟨e, he, rfl⟩, (tensor_reachCod_inl e).2 h₂⟩

theorem tensor_not_live_inr (hΩ : ∀ y, Ω.val.IsDisc y) (y : N') : ¬ (Υ.tensor Ω).Live (.inr y) := by
  rintro ⟨-, e, he, -⟩
  obtain ⟨a, ha⟩ := hΩ y
  change e ∈ (Ω.outs y).map Sum.inr at he
  rw [Ω.val.outs_eq_nil_of_disc ha] at he
  cases he

theorem tensor_dupStep_inl {d : E ⊕ E'} {e : E}
    (h : (Υ.tensor Ω).toPGraph.DupStep (Υ.tensor Ω).val.IsDup d (.inl e)) :
    ∃ d', d = .inl d' ∧ Υ.toPGraph.DupStep Υ.val.IsDup d' e := by
  obtain ⟨z, hz, hz₁, hz₂⟩ := h
  rw [tensor_src_inl] at hz₂
  cases hx : Υ.src e with
  | none => rw [hx] at hz₂; cases hz₂
  | some x =>
    rw [hx] at hz₂
    cases hz₂
    obtain ⟨d', rfl, hd'⟩ := tensor_tgt_inl_eq hz₁
    exact ⟨d', rfl, x, hz, hd', hx⟩

theorem tensor_dupStep_inl_inl {d e : E} (h : Υ.toPGraph.DupStep Υ.val.IsDup d e) :
    (Υ.tensor Ω).toPGraph.DupStep (Υ.tensor Ω).val.IsDup (.inl d) (.inl e) := by
  obtain ⟨x, hx, h₁, h₂⟩ := h
  exact ⟨.inl x, hx, by rw [tensor_tgt_inl, h₁]; rfl, by rw [tensor_src_inl, h₂]; rfl⟩

theorem tensor_isOrigin_inl {q : E ⊕ E'} {e : E} :
    (Υ.tensor Ω).IsOrigin q (.inl e) ↔ ∃ q', q = .inl q' ∧ Υ.IsOrigin q' e := by
  constructor
  · rintro ⟨h, hr⟩
    have key : ∀ d, ReflTransGen ((Υ.tensor Ω).toPGraph.DupStep (Υ.tensor Ω).val.IsDup) q d →
        ∀ e, d = .inl e → ∃ q', q = .inl q' ∧ ReflTransGen (Υ.toPGraph.DupStep Υ.val.IsDup) q' e := by
      intro d hd
      induction hd with
      | refl => rintro e rfl; exact ⟨e, rfl, ReflTransGen.refl⟩
      | tail _ hst ih =>
        rintro e rfl
        obtain ⟨d', rfl, hd'⟩ := tensor_dupStep_inl hst
        obtain ⟨q', rfl, h'⟩ := ih d' rfl
        exact ⟨q', rfl, h'.tail hd'⟩
    obtain ⟨q', rfl, h'⟩ := key _ h e rfl
    refine ⟨q', rfl, h', fun x hx => ?_⟩
    exact hr (.inl x) (by rw [tensor_src_inl, hx]; rfl)
  · rintro ⟨q', rfl, h, hr⟩
    refine ⟨?_, fun z hz => ?_⟩
    · clear hr
      induction h with
      | refl => exact ReflTransGen.refl
      | tail _ hst ih => exact ih.tail (tensor_dupStep_inl_inl hst)
    · rw [tensor_src_inl] at hz
      cases hx : Υ.src q' with
      | none => rw [hx] at hz; cases hz
      | some x => rw [hx] at hz; cases hz; exact hr x hx

theorem tensor_originAt_dom (e : E) (j : ℕ) :
    (Υ.tensor Ω).OriginAt (.inl e) (.dom j) ↔ Υ.OriginAt e (.dom j) := by
  simp only [OriginAt]
  constructor
  · rintro ⟨q, hq, ho⟩
    obtain ⟨q', rfl, ho'⟩ := tensor_isOrigin_inl.1 ho
    exact ⟨q', (List.getElem?_append_map_inl _ _ j q').1 hq, ho'⟩
  · rintro ⟨q, hq, ho⟩
    exact ⟨.inl q, List.getElem?_append_map_inl' _ _ j q hq, tensor_isOrigin_inl.2 ⟨q, rfl, ho⟩⟩

theorem tensor_originAt_out (e : E) (y : N) (j : ℕ) :
    (Υ.tensor Ω).OriginAt (.inl e) (.out (.inl y) j) ↔ Υ.OriginAt e (.out y j) := by
  simp only [OriginAt]
  change (∃ q, ((Υ.outs y).map Sum.inl)[j]? = some q ∧ _) ↔ _
  simp only [List.getElem?_map]
  constructor
  · rintro ⟨q, hq, ho⟩
    obtain ⟨q', rfl, ho'⟩ := tensor_isOrigin_inl.1 ho
    refine ⟨q', ?_, ho'⟩
    cases h : (Υ.outs y)[j]? <;> rw [h] at hq <;> simp_all
  · rintro ⟨q, hq, ho⟩
    exact ⟨.inl q, by rw [hq]; rfl, tensor_isOrigin_inl.2 ⟨q, rfl, ho⟩⟩

variable (Υ Ω) in
/-- The live nodes of `Υ ⊗ Ω` are those of `Υ` when `Ω` consists of discards. -/
noncomputable def tensorLiveEquiv (hΩ : ∀ y, Ω.val.IsDisc y) :
    {x // Υ.Live x} ≃ {z // (Υ.tensor Ω).Live z} :=
  Equiv.ofBijective (fun x => ⟨.inl x.1, (tensor_live_inl x.1).2 x.2⟩)
    ⟨fun x x' h => Subtype.ext (Sum.inl_injective (congrArg Subtype.val h)), fun z => by
      rcases z with ⟨z | z, hz⟩
      · exact ⟨⟨z, (tensor_live_inl z).1 hz⟩, rfl⟩
      · exact (tensor_not_live_inr hΩ z hz).elim⟩

end Tensor

section OfTensor

variable {Υ : Diagram G.toFreeGraphMonoid N E} {Ω : Diagram G.toFreeGraphMonoid N' E'}
  {N₂ : Type u₅} {E₂ : Type u₆} {N₂' : Type u₇} {E₂' : Type u₈}
  {Υ' : Diagram G.toFreeGraphMonoid N₂ E₂} {Ω' : Diagram G.toFreeGraphMonoid N₂' E₂'}
  (hΩ : ∀ y, Ω.val.IsDisc y) (hΩ' : ∀ y, Ω'.val.IsDisc y)
  (π : {z // (Υ.tensor Ω).Live z} ≃ {z // (Υ'.tensor Ω').Live z})

/-- The bijection of live nodes of `Υ`, `Υ'` induced by one of `Υ ⊗ Ω`, `Υ' ⊗ Ω'`. -/
noncomputable def tensorPi : {x // Υ.Live x} ≃ {x // Υ'.Live x} :=
  (tensorLiveEquiv Υ Ω hΩ).trans (π.trans (tensorLiveEquiv Υ' Ω' hΩ').symm)

theorem tensorPi_spec (x : {x // Υ.Live x}) :
    (π (tensorLiveEquiv Υ Ω hΩ x)).1 = .inl (tensorPi hΩ hΩ' π x).1 := by
  change _ = (tensorLiveEquiv Υ' Ω' hΩ' ((tensorLiveEquiv Υ' Ω' hΩ').symm _)).1
  rw [Equiv.apply_symm_apply]

include hΩ hΩ' in
theorem OriginsMatch.of_tensor {e : E} {e' : E₂}
    (h : OriginsMatch π (.inl e) (.inl e')) : OriginsMatch (tensorPi hΩ hΩ' π) e e' := by
  refine ⟨fun j => ?_, fun y j => ?_⟩
  · exact ((tensor_originAt_dom (Ω := Ω) e j).symm.trans (h.1 j)).trans
      (tensor_originAt_dom (Ω := Ω') e' j)
  · have := h.2 (tensorLiveEquiv Υ Ω hΩ y) j
    rw [tensorPi_spec hΩ hΩ'] at this
    exact ((tensor_originAt_out (Ω := Ω) e y.1 j).symm.trans this).trans
      (tensor_originAt_out (Ω := Ω') e' _ j)

include hΩ hΩ' in
theorem SkeletonIso.of_tensor (h : SkeletonIso (Υ.tensor Ω) (Υ'.tensor Ω') π) :
    SkeletonIso Υ Υ' (tensorPi hΩ hΩ' π) where
  val_eq x := by
    have := h.val_eq (tensorLiveEquiv Υ Ω hΩ x)
    rw [tensorPi_spec hΩ hΩ'] at this
    exact this
  cod_match i e e' he he' :=
    (h.cod_match i (.inl e) (.inl e') (List.getElem?_append_map_inl' _ _ i e he)
      (List.getElem?_append_map_inl' _ _ i e' he')).of_tensor hΩ hΩ' π
  ins_match x i e e' he he' := by
    refine (h.ins_match (tensorLiveEquiv Υ Ω hΩ x) i (.inl e) (.inl e') ?_ ?_).of_tensor hΩ hΩ' π
    · change ((Υ.ins x.1).map Sum.inl)[i]? = _
      rw [List.getElem?_map, he]
      rfl
    · rw [tensorPi_spec hΩ hΩ']
      change ((Υ'.ins _).map Sum.inl)[i]? = _
      rw [List.getElem?_map, he']
      rfl

include hΩ hΩ' in
/-- **Cancelling discards.** If `Ω`, `Ω'` consist of discards and `Υ ⊗ Ω`, `Υ' ⊗ Ω'` have the
same skeleton, then so have `Υ`, `Υ'` (given that they have the same domain and codomain). -/
theorem SameSkeleton.of_tensor (h : SameSkeleton (Υ.tensor Ω) (Υ'.tensor Ω'))
    (hd : Υ.domWord = Υ'.domWord) (hc : Υ.codWord = Υ'.codWord) : SameSkeleton Υ Υ' := by
  obtain ⟨-, -, π, hπ⟩ := h
  exact ⟨hd, hc, _, hπ.of_tensor hΩ hΩ' π⟩

end OfTensor

end Diagram

end FreeMarkov
