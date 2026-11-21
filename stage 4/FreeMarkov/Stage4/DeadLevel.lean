/-
Free Markov categories, Stage 4: dead inputs of a Markov minimal diagram (the proof of the third
item of Lemma 4.5).

"We may assume that `Γ` is Markov minimal. Let `j ∈ J` and `e` be as above. Then `e ∉ cod(Γ)` and,
by the first item, no directed path that starts at the node `e(1)` ends in `cod(Γ)`. So
`e(1) ∈ Δ_Γ` and hence its value is a discard. Removing these edges and discards for all `j ∈ J`,
we obtain an anchored diagram `Γ''` from `a''` to `b` ..."

* `deadL`: the discards at the dead edges of the domain; it is a level, its cut is the list of the
  edges of the domain that are not dead (`deadEnum`).
* The lower layer `Γ[∅, deadL]` has the same skeleton as `(1_{a''} ⊗ ε_{a'}) ∘ τ`
  (`sameSkeleton_lower`); the upper layer `Γ'' = Γ[deadL, Γ̇]` has no dead edge in its domain
  (`not_dead_upper`).
-/
module

public import FreeMarkov.Stage4.Lemma45c

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

open scoped Classical

namespace PGraph

variable {N : Type u₁} {E : Type u₂} {Γ : PGraph N E} {D : N → Prop}

theorem isOrigin_iff_of_src_none {q e : E} (h : Γ.src e = none) : Γ.IsOrigin D q e ↔ q = e := by
  constructor
  · rintro ⟨h₁, -⟩
    rcases h₁.cases_tail with rfl | ⟨c, -, x, -, -, hx⟩
    · rfl
    · rw [h] at hx; cases hx
  · rintro rfl
    exact ⟨ReflTransGen.refl, isRoot_of_src_none h⟩

end PGraph

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

/-- The edge `e` is not the origin of a consumer. -/
def DeadE (Γ : Diagram G.toFreeGraphMonoid N E) (e : E) : Prop :=
  ∀ c, Γ.Consumer c → ¬ Γ.IsOrigin e c

theorem dead_iff (Γ : Diagram G.toFreeGraphMonoid N E) {j : ℕ} (hj : j < Γ.dom.length) :
    Γ.Dead j ↔ Γ.DeadE Γ.dom[j] := by
  simp [Dead, DeadE, List.getElem?_eq_getElem hj]

theorem deadE_iff_not_reachCod [Finite E] (Γ : Diagram G.toFreeGraphMonoid N E) {e : E}
    (he : Γ.src e = none) : Γ.DeadE e ↔ ¬ Γ.toPGraph.ReachCod e := by
  constructor
  · intro hd hr
    obtain ⟨c, hc, hcc⟩ := PGraph.exists_consumer_of_reachCod (D := Γ.val.IsDup) (Γ := Γ.toPGraph) hr
    exact hd c hcc ⟨hc, PGraph.isRoot_of_src_none he⟩
  · intro hr c hc ho
    exact hr (hc.reachCod.of_reflTransGen (PGraph.reflTransGen_step_of_dup ho.1))

/-- Two diagrams without live nodes, in which every edge of the codomain begins at an outer node,
have the same skeleton when the `i`-th edges of the codomains are at the same positions in the
domains. -/
theorem sameSkeleton_of_noLive {Λ : Diagram G.toFreeGraphMonoid N E}
    {Λ' : Diagram G.toFreeGraphMonoid N' E'} (h₁ : ∀ x, ¬ Λ.Live x) (h₁' : ∀ x, ¬ Λ'.Live x)
    (hs : ∀ e ∈ Λ.cod, Λ.src e = none) (hs' : ∀ e ∈ Λ'.cod, Λ'.src e = none)
    (hd : Λ.domWord = Λ'.domWord) (hc : Λ.codWord = Λ'.codWord)
    (hpos : ∀ (i : ℕ) (e : E) (e' : E'), Λ.cod[i]? = some e → Λ'.cod[i]? = some e' →
      ∀ j : ℕ, Λ.dom[j]? = some e ↔ Λ'.dom[j]? = some e') :
    SameSkeleton Λ Λ' := by
  have : IsEmpty {x // Λ.Live x} := ⟨fun x => h₁ x.1 x.2⟩
  have : IsEmpty {x // Λ'.Live x} := ⟨fun x => h₁' x.1 x.2⟩
  refine ⟨hd, hc, Equiv.equivOfIsEmpty _ _, ⟨fun x => isEmptyElim x,
    fun i e e' he he' => ⟨fun j => ?_, fun y => isEmptyElim y⟩, fun x => isEmptyElim x⟩⟩
  simp only [OriginAt]
  have h₂ := hs e (List.mem_of_getElem? he)
  have h₂' := hs' e' (List.mem_of_getElem? he')
  simp only [IsOrigin, PGraph.isOrigin_iff_of_src_none h₂, PGraph.isOrigin_iff_of_src_none h₂',
    exists_eq_right]
  exact hpos i e e' he he' j

theorem getElem?_map_val_iff {α : Type*} {p : α → Prop} (l : List {x // p x}) (j : ℕ)
    (e : {x // p x}) : l[j]? = some e ↔ (l.map Subtype.val)[j]? = some e.1 := by
  rw [List.getElem?_map]
  cases l[j]? with
  | none => simp
  | some e' => simp [Subtype.ext_iff]

theorem dead_iff_not (Γ : Diagram G.toFreeGraphMonoid N E) (j : ℕ) (hj : j < Γ.dom.length) :
    ¬ Γ.Dead j ↔ ¬ Γ.DeadE Γ.dom[j] := by
  rw [dead_iff Γ hj]

theorem wlen_domWord (Γ : Diagram G.toFreeGraphMonoid N E) : wlen Γ.domWord = Γ.dom.length := by
  simp [wlen, domWord]

section DeadLevel

variable {Γ : Diagram G.toFreeGraphMonoid N E} [Finite E] (hΓ : Γ.MarkovMinimal)
include hΓ

/-- In a Markov minimal diagram a dead edge of the domain ends at a discard. -/
theorem disc_of_deadE {e : E} (he : Γ.src e = none) (hd : Γ.DeadE e) :
    ∃ x, Γ.tgt e = some x ∧ Γ.val.IsDisc x := by
  rw [deadE_iff_not_reachCod Γ he] at hd
  cases hx : Γ.tgt e with
  | none => exact absurd ⟨e, ReflTransGen.refl, hx⟩ hd
  | some x =>
    refine ⟨x, rfl, hΓ x (Or.inl fun e' he' hr => hd (hr.of_step ⟨x, hx, ?_⟩))⟩
    exact (Γ.mem_outs x e').1 he'

omit hΓ in
variable (Γ) in
/-- The nodes at the ends of the dead edges of the domain. -/
def deadL : Set N := {x | ∃ e ∈ Γ.dom, Γ.DeadE e ∧ Γ.tgt e = some x}

theorem deadL_disc {x : N} (hx : x ∈ Γ.deadL) : Γ.val.IsDisc x := by
  obtain ⟨e, he, hd, hx⟩ := hx
  obtain ⟨x', hx', h⟩ := disc_of_deadE hΓ ((Γ.mem_dom e).1 he) hd
  rw [hx] at hx'
  cases hx'
  exact h

theorem deadL_outs {x : N} (hx : x ∈ Γ.deadL) : Γ.outs x = [] := by
  obtain ⟨a, ha⟩ := deadL_disc hΓ hx
  exact Γ.val.outs_eq_nil_of_disc ha

theorem deadL_ins {x : N} (hx : x ∈ Γ.deadL) {e : E} (he : Γ.tgt e = some x) :
    e ∈ Γ.dom ∧ Γ.DeadE e := by
  obtain ⟨a, ha⟩ := deadL_disc hΓ hx
  obtain ⟨e₀, he₀, hd₀, hx₀⟩ := hx
  obtain ⟨e', hins, -⟩ := Γ.val.ins_eq_of_disc ha
  have h₁ : e ∈ Γ.ins x := (Γ.mem_ins x e).2 he
  have h₂ : e₀ ∈ Γ.ins x := (Γ.mem_ins x e₀).2 hx₀
  rw [hins, List.mem_singleton] at h₁ h₂
  rw [h₁, ← h₂]
  exact ⟨he₀, hd₀⟩

theorem isLevel_deadL : Γ.IsLevel Γ.deadL := by
  intro x y hxy hy
  obtain ⟨z, -, d, hd₁, hd₂⟩ := TransGen.tail'_iff.1 hxy
  have := ((Γ.mem_dom d).1 (deadL_ins hΓ hy hd₂).1)
  rw [this] at hd₁
  cases hd₁

theorem src_eq_none_of_srcIn {e : E} (h : Γ.SrcIn Γ.deadL e) : Γ.src e = none := by
  cases hx : Γ.src e with
  | none => rfl
  | some x =>
    have h₁ := deadL_outs hΓ (h x hx)
    have h₂ : e ∈ Γ.outs x := (Γ.mem_outs x e).2 hx
    rw [h₁] at h₂
    cases h₂

theorem cut_deadL_iff (e : E) : Γ.Cut Γ.deadL e ↔ e ∈ Γ.dom ∧ ¬ Γ.DeadE e := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have he : Γ.src e = none := src_eq_none_of_srcIn hΓ h₁
    refine ⟨(Γ.mem_dom e).2 he, fun hd => ?_⟩
    obtain ⟨x, hx, -⟩ := disc_of_deadE hΓ he hd
    exact h₂ x hx ⟨e, (Γ.mem_dom e).2 he, hd, hx⟩
  · rintro ⟨he, hd⟩
    refine ⟨fun x hx => ?_, fun x hx hL => hd (deadL_ins hΓ hL hx).2⟩
    rw [(Γ.mem_dom e).1 he] at hx
    cases hx

/-- The edges of the domain that are not dead, in the order of the domain: an ordering of the cut of
`deadL`. -/
noncomputable def deadEnum : Enumeration (Γ.Cut Γ.deadL) where
  list := Γ.dom.filter fun e => @decide (¬ Γ.DeadE e) (Classical.propDecidable _)
  nodup := Γ.dom_nodup.filter _
  mem_iff e := by
    rw [cut_deadL_iff hΓ]
    simp only [List.mem_filter, decide_eq_true_eq]

/-! #### The lower layer -/

theorem lowerD_dom_map_val :
    (Γ.lowerD (isLevel_deadL hΓ) (deadEnum hΓ)).dom.map Subtype.val = Γ.dom :=
  Γ.layerD_dom_map_val _ _ _ _ _

theorem lowerD_cod_map_val :
    (Γ.lowerD (isLevel_deadL hΓ) (deadEnum hΓ)).cod.map Subtype.val =
      Γ.dom.filter fun e => @decide (¬ Γ.DeadE e) (Classical.propDecidable _) :=
  Γ.layerD_cod_map_val _ _ _ _ _

theorem lowerD_not_live (x) : ¬ (Γ.lowerD (isLevel_deadL hΓ) (deadEnum hΓ)).Live x := by
  rintro ⟨-, e, he, -⟩
  obtain ⟨a, ha⟩ := deadL_disc hΓ x.2.1
  rw [(Γ.lowerD (isLevel_deadL hΓ) (deadEnum hΓ)).val.outs_eq_nil_of_disc (x := x) (a := a) ha]
    at he
  cases he

theorem lowerD_src (e) : (Γ.lowerD (isLevel_deadL hΓ) (deadEnum hΓ)).src e = none := by
  have h : Γ.src e.1 = none := src_eq_none_of_srcIn hΓ e.2.1
  change (Γ.src e.1).bind _ = none
  rw [h]
  rfl

theorem lowerD_domWord : (Γ.lowerD (isLevel_deadL hΓ) (deadEnum hΓ)).domWord = Γ.domWord := by
  rw [layerD_domWord]
  rfl

theorem lowerD_codWord :
    (Γ.lowerD (isLevel_deadL hΓ) (deadEnum hΓ)).codWord = liveW Γ.domWord Γ.Dead := by
  rw [layerD_codWord]
  exact (liveW_eq_ofList_filter Γ.dom Γ.val.v₀ (fun e => ¬ Γ.DeadE e) Γ.Dead
    (dead_iff_not Γ)).symm

/-- **The lower layer is `(1_{a''} ⊗ ε_{a'}) ∘ τ`, up to the skeleton.** -/
theorem sameSkeleton_lower :
    SameSkeleton (Γ.lowerD (isLevel_deadL hΓ) (deadEnum hΓ)) (tauRe (G := G) Γ.domWord Γ.Dead) := by
  refine sameSkeleton_of_noLive (lowerD_not_live hΓ) (fun x => ?_) (fun e _ => lowerD_src hΓ e)
    (fun e he => ?_) ?_ ?_ ?_
  · rcases x with x | x
    · exact x.elim
    · exact tensor_not_live_inr (FreeDDGraphMonoidAux.discListD_isDisc _) x
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    obtain ⟨_, h⟩ := tauTarget_cod_getElem? (G := G) Γ.domWord Γ.Dead (List.getElem?_eq_getElem hi)
    rw [h]
    rfl
  · rw [lowerD_domWord, tauRe, show ((tauTarget (G := G) Γ.domWord Γ.Dead).reanchor _ _).domWord =
      ((permNF (G := G) Γ.domWord _ _ _).glue (tauTarget Γ.domWord Γ.Dead) (tauHΘ _ _)).domWord from
      (glueNodeFreeIso (tauHΘ (G := G) Γ.domWord Γ.Dead)).domWord_eq, glue_domWord,
      permNF_domWord]
  · rw [lowerD_codWord]
    exact (tauTarget_codWord _ _).symm
  · intro i e e' he he' j
    have hx : (Γ.dom.filter fun e => @decide (¬ Γ.DeadE e) (Classical.propDecidable _))[i]? = some e.1 := by
      rw [← lowerD_cod_map_val hΓ, ← getElem?_map_val_iff]
      exact he
    rw [getElem?_map_val_iff, lowerD_dom_map_val hΓ,
      getElem?_filter_iff Γ.dom_nodup (fun e => ¬ Γ.DeadE e) Γ.Dead (dead_iff_not Γ) hx j,
      tauRe_pos _ _ he' j, livePos_congr (wlen_domWord Γ).symm]

/-! #### The upper layer -/

theorem tgtIn_of_reachCod {d : E} (h : Γ.toPGraph.ReachCod d) : Γ.TgtIn Γ.deadLᶜ d := by
  intro y hy hL
  obtain ⟨c, hc, hc'⟩ := h
  rcases hc.cases_head with rfl | ⟨d', ⟨y', hy', hd'⟩, -⟩
  · rw [hy] at hc'; cases hc'
  · rw [hy] at hy'
    cases hy'
    have h₂ : d' ∈ Γ.outs y := (Γ.mem_outs y d').2 hd'
    rw [deadL_outs hΓ hL] at h₂
    cases h₂

theorem upperD_reachCod {d c : E} (h : ReflTransGen Γ.toPGraph.Step d c) (hc : Γ.tgt c = none)
    (hd : Γ.LayerEdge Γ.deadL Set.univ d) :
    (Γ.upperD (isLevel_deadL hΓ) (deadEnum hΓ)).toPGraph.ReachCod ⟨d, hd⟩ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨⟨c, hd⟩, ReflTransGen.refl, ?_⟩
    change (Γ.tgt c).bind _ = none
    rw [hc]
    rfl
  | head hst hrest ih =>
    rename_i d d'
    have hd' : Γ.LayerEdge Γ.deadL Set.univ d' :=
      ⟨fun _ _ => trivial, tgtIn_of_reachCod hΓ ⟨c, hrest, hc⟩⟩
    refine (ih hd').of_step ?_
    obtain ⟨x, hx, hx'⟩ := hst
    refine ⟨⟨x, trivial, hd.2 x hx⟩, ?_, ?_⟩
    · exact (PGraph.sub_tgt_eq_some_iff (Γ := Γ.toPGraph) ⟨d, hd⟩ ⟨x, trivial, hd.2 x hx⟩).2 hx
    · exact (PGraph.sub_src_eq_some_iff (Γ := Γ.toPGraph) ⟨d', hd'⟩ ⟨x, trivial, hd.2 x hx⟩).2 hx'

theorem upperD_domWord :
    (Γ.upperD (isLevel_deadL hΓ) (deadEnum hΓ)).domWord = liveW Γ.domWord Γ.Dead := by
  rw [layerD_domWord]
  exact (liveW_eq_ofList_filter Γ.dom Γ.val.v₀ (fun e => ¬ Γ.DeadE e) Γ.Dead
    (dead_iff_not Γ)).symm

theorem upperD_codWord : (Γ.upperD (isLevel_deadL hΓ) (deadEnum hΓ)).codWord = Γ.codWord := by
  rw [layerD_codWord]
  rfl

/-- **No edge of the domain of `Γ''` is dead**: "the live nodes and the consumers of `Γ''` are those
of `Γ`, so every edge in `dom(Γ'')` is the origin of a consumer". -/
theorem not_dead_upper (j : ℕ) : ¬ (Γ.upperD (isLevel_deadL hΓ) (deadEnum hΓ)).Dead j := by
  rintro ⟨e, he, hd⟩
  have h₁ : (deadEnum hΓ).list[j]? = some e.1 := by
    rw [← Γ.layerD_dom_map_val (isLevel_deadL hΓ) Γ.isLevel_univ (Set.subset_univ _)
      (deadEnum hΓ) Γ.cutUnivEnum, ← getElem?_map_val_iff]
    exact he
  have h₂ := ((deadEnum hΓ).mem_iff e.1).1 (List.mem_of_getElem? h₁)
  rw [cut_deadL_iff hΓ] at h₂
  have hsrc : Γ.src e.1 = none := (Γ.mem_dom _).1 h₂.1
  rw [deadE_iff_not_reachCod Γ hsrc, not_not] at h₂
  obtain ⟨c, hc, hc'⟩ := h₂.2
  have hsrc' : (Γ.upperD (isLevel_deadL hΓ) (deadEnum hΓ)).src e = none :=
    ((Γ.upperD (isLevel_deadL hΓ) (deadEnum hΓ)).mem_dom e).1 (List.mem_of_getElem? he)
  exact (deadE_iff_not_reachCod _ hsrc').1 hd (upperD_reachCod hΓ hc hc' e.2)

end DeadLevel

end Diagram

end FreeMarkov
