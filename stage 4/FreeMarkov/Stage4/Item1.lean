/-
Free Markov categories, Stage 4: the first item of Lemma 4.3 from a skeleton bijection.

"For the first item, a node in `Δ̃_Γ` whose value is not a duplicate is live. ... So, if `n ≥ 1`
is the number of the consumers with the origin `q`, then exactly `n - 1` duplicates in this tree
belong to `Δ̃_Γ`, and their value is the duplicate on `v(q)`. Since `n` is determined by the
skeleton, `π` may be extended as required."

The origins of consumers are at *ports*: edges of the domain and outputs of live nodes
(`PortT`); consumers are the edges of the codomain and the inputs of live nodes (`SlotT`).
-/
module

public import FreeMarkov.Stage4.Items
public import FreeMarkov.Stage4.Count

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

section Ports

variable (Γ : Diagram G.toFreeGraphMonoid N E)

/-- The ports of `Γ`: the positions in `dom(Γ)` and the outputs of the live nodes. -/
abbrev PortT : Type (max u₁ u₂) :=
  ULift.{max u₁ u₂} (Fin Γ.dom.length) ⊕ Σ y : {x // Γ.Live x}, Fin (Γ.outs y.1).length

/-- The edge at a port. -/
def portEdge : Γ.PortT → E
  | .inl j => Γ.dom[j.down.1]
  | .inr ⟨y, j⟩ => (Γ.outs y.1)[j.1]

/-- The consumer slots of `Γ`: the positions in `cod(Γ)` and the inputs of the live nodes. -/
abbrev SlotT : Type (max u₁ u₂) :=
  ULift.{max u₁ u₂} (Fin Γ.cod.length) ⊕ Σ x : {x // Γ.Live x}, Fin (Γ.ins x.1).length

/-- The edge at a consumer slot. -/
def slotEdge : Γ.SlotT → E
  | .inl j => Γ.cod[j.down.1]
  | .inr ⟨x, j⟩ => (Γ.ins x.1)[j.1]

variable {Γ}

theorem portEdge_injective : Function.Injective Γ.portEdge := by
  rintro (⟨j⟩ | ⟨y, j⟩) (⟨j'⟩ | ⟨y', j'⟩) h <;> simp only [portEdge] at h
  · rw [Γ.dom_nodup.getElem_inj_iff] at h
    exact congrArg Sum.inl (congrArg ULift.up (Fin.ext h))
  · have h₁ : Γ.src Γ.dom[j.down.1] = none := (Γ.mem_dom _).1 (List.getElem_mem _)
    have h₂ : Γ.src (Γ.outs y'.1)[j'.1] = some y'.1 := (Γ.mem_outs _ _).1 (List.getElem_mem _)
    rw [h, h₂] at h₁
    cases h₁
  · have h₁ : Γ.src Γ.dom[j'.down.1] = none := (Γ.mem_dom _).1 (List.getElem_mem _)
    have h₂ : Γ.src (Γ.outs y.1)[j.1] = some y.1 := (Γ.mem_outs _ _).1 (List.getElem_mem _)
    rw [← h, h₂] at h₁
    cases h₁
  · have h₁ : Γ.src (Γ.outs y.1)[j.1] = some y.1 := (Γ.mem_outs _ _).1 (List.getElem_mem _)
    have h₂ : Γ.src (Γ.outs y'.1)[j'.1] = some y'.1 := (Γ.mem_outs _ _).1 (List.getElem_mem _)
    rw [h, h₂, Option.some.injEq] at h₁
    have hy : y = y' := Subtype.ext h₁.symm
    subst hy
    rw [(Γ.outs_nodup _).getElem_inj_iff] at h
    have : j = j' := Fin.ext h
    subst this
    rfl

theorem slotEdge_injective : Function.Injective Γ.slotEdge := by
  rintro (⟨j⟩ | ⟨y, j⟩) (⟨j'⟩ | ⟨y', j'⟩) h <;> simp only [slotEdge] at h
  · rw [Γ.cod_nodup.getElem_inj_iff] at h
    exact congrArg Sum.inl (congrArg ULift.up (Fin.ext h))
  · have h₁ : Γ.tgt Γ.cod[j.down.1] = none := (Γ.mem_cod _).1 (List.getElem_mem _)
    have h₂ : Γ.tgt (Γ.ins y'.1)[j'.1] = some y'.1 := (Γ.mem_ins _ _).1 (List.getElem_mem _)
    rw [h, h₂] at h₁
    cases h₁
  · have h₁ : Γ.tgt Γ.cod[j'.down.1] = none := (Γ.mem_cod _).1 (List.getElem_mem _)
    have h₂ : Γ.tgt (Γ.ins y.1)[j.1] = some y.1 := (Γ.mem_ins _ _).1 (List.getElem_mem _)
    rw [← h, h₂] at h₁
    cases h₁
  · have h₁ : Γ.tgt (Γ.ins y.1)[j.1] = some y.1 := (Γ.mem_ins _ _).1 (List.getElem_mem _)
    have h₂ : Γ.tgt (Γ.ins y'.1)[j'.1] = some y'.1 := (Γ.mem_ins _ _).1 (List.getElem_mem _)
    rw [h, h₂, Option.some.injEq] at h₁
    have hy : y = y' := Subtype.ext h₁.symm
    subst hy
    rw [(Γ.ins_nodup _).getElem_inj_iff] at h
    have : j = j' := Fin.ext h
    subst this
    rfl

theorem consumer_iff_exists_slot (c : E) : Γ.Consumer c ↔ ∃ σ, Γ.slotEdge σ = c := by
  constructor
  · rintro (h | ⟨x, hx, hl⟩)
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ((Γ.mem_cod c).2 h)
      exact ⟨.inl ⟨⟨j, hj⟩⟩, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ((Γ.mem_ins x _).2 hx)
      exact ⟨.inr ⟨⟨x, hl⟩, ⟨j, hj⟩⟩, rfl⟩
  · rintro ⟨(⟨j⟩ | ⟨x, j⟩), rfl⟩
    · exact Or.inl ((Γ.mem_cod _).1 (List.getElem_mem _))
    · exact Or.inr ⟨x.1, (Γ.mem_ins _ _).1 (List.getElem_mem _), x.2⟩

theorem isRoot_portEdge (p : Γ.PortT) : Γ.toPGraph.IsRoot Γ.val.IsDup (Γ.portEdge p) := by
  rcases p with ⟨j⟩ | ⟨y, j⟩
  · exact PGraph.isRoot_of_src_none ((Γ.mem_dom _).1 (List.getElem_mem _))
  · exact PGraph.isRoot_of_mem_outs (List.getElem_mem _) y.2.1

/-- The port of `Γ` as a position. -/
def portPos : Γ.PortT → Port N
  | .inl j => .dom j.down.1
  | .inr ⟨y, j⟩ => .out y.1 j.1

theorem originAt_portPos_iff (p : Γ.PortT) (e : E) :
    Γ.OriginAt e (Γ.portPos p) ↔ Γ.IsOrigin (Γ.portEdge p) e := by
  rcases p with ⟨j⟩ | ⟨y, j⟩
  · simp only [portPos, OriginAt, portEdge, List.getElem?_eq_getElem j.down.2, Option.some.injEq,
      exists_eq_left']
  · simp only [portPos, OriginAt, portEdge, List.getElem?_eq_getElem j.2, Option.some.injEq,
      exists_eq_left']

/-- Labels are constant along chains through duplicates. -/
theorem v₀_eq_of_reflTransGen_dup {e e' : E} (h : ReflTransGen (Γ.toPGraph.DupStep Γ.val.IsDup) e e') :
    Γ.val.v₀ e' = Γ.val.v₀ e := by
  induction h with
  | refl => rfl
  | tail _ h ih =>
    obtain ⟨x, ⟨a, ha⟩, hx, hx'⟩ := h
    obtain ⟨f, hf, hfa⟩ := Γ.val.ins_eq_of_dup ha
    obtain ⟨e₁, e₂, ho, h₁, h₂⟩ := Γ.val.outs_eq_of_t_dup ha
    have hin : _ ∈ Γ.ins x := (Γ.mem_ins x _).2 hx
    rw [hf, List.mem_singleton] at hin
    have hout : _ ∈ Γ.outs x := (Γ.mem_outs x _).2 hx'
    rw [ho] at hout
    rw [← ih, hin, hfa]
    rcases List.mem_pair.1 hout with h | h <;> rw [h]
    · exact h₁
    · exact h₂

end Ports

/-! ### Transport of ports and slots along a skeleton bijection -/

variable {Γ : Diagram G.toFreeGraphMonoid N E} {Υ : Diagram G.toFreeGraphMonoid N' E'}
  {π : {x // Γ.Live x} ≃ {y // Υ.Live y}}

/-- Ports correspond along `π`. -/
def portEquiv (hd : Γ.domWord = Υ.domWord) (h : SkeletonIso Γ Υ π) : Γ.PortT ≃ Υ.PortT :=
  Equiv.sumCongr (Equiv.ulift.trans ((finCongr (dom_length_eq_of_domWord hd)).trans Equiv.ulift.symm))
    (Equiv.sigmaCongr π fun y => finCongr (outs_length_eq_of_val (h.val_eq y)).symm)

/-- Slots correspond along `π`. -/
def slotEquiv (hc : Γ.codWord = Υ.codWord) (h : SkeletonIso Γ Υ π) : Γ.SlotT ≃ Υ.SlotT :=
  Equiv.sumCongr (Equiv.ulift.trans ((finCongr (cod_length_eq_of_codWord hc)).trans Equiv.ulift.symm))
    (Equiv.sigmaCongr π fun y => finCongr (ins_length_eq_of_val (h.val_eq y)).symm)

theorem originAt_slot_iff (hd : Γ.domWord = Υ.domWord) (hc : Γ.codWord = Υ.codWord)
    (h : SkeletonIso Γ Υ π) (p : Γ.PortT) (σ : Γ.SlotT) :
    Γ.IsOrigin (Γ.portEdge p) (Γ.slotEdge σ) ↔
      Υ.IsOrigin (Υ.portEdge (portEquiv hd h p)) (Υ.slotEdge (slotEquiv hc h σ)) := by
  rw [← originAt_portPos_iff, ← originAt_portPos_iff]
  have hm : OriginsMatch π (Γ.slotEdge σ) (Υ.slotEdge (slotEquiv hc h σ)) := by
    rcases σ with ⟨j⟩ | ⟨x, j⟩
    · exact h.cod_match j.down.1 _ _ (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _)
    · exact h.ins_match x j.1 _ _ (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _)
  rcases p with ⟨j⟩ | ⟨y, j⟩
  · exact hm.1 j.down.1
  · exact hm.2 y j.1

theorem _root_.FreeMarkov.getElem_eq_of_map_eq {α : Type*} {β : Type*} {γ : Type*} {l : List α}
    {l' : List β} (f : α → γ) (g : β → γ) (h : l.map f = l'.map g) (i : ℕ) (hi : i < l.length)
    (hi' : i < l'.length) : f l[i] = g l'[i] := by
  have := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
    Option.map_some, Option.some.injEq] at this
  exact this

theorem v₀_portEdge (hd : Γ.domWord = Υ.domWord) (h : SkeletonIso Γ Υ π) (p : Γ.PortT) :
    Υ.val.v₀ (Υ.portEdge (portEquiv hd h p)) = Γ.val.v₀ (Γ.portEdge p) := by
  rcases p with ⟨j⟩ | ⟨y, j⟩
  · have h' : Γ.dom.map Γ.val.v₀ = Υ.dom.map Υ.val.v₀ := FreeMonoid.ofList.injective hd
    exact (getElem_eq_of_map_eq _ _ h' j.down.1 j.down.2
      ((dom_length_eq_of_domWord hd) ▸ j.down.2)).symm
  · have h₁ := Γ.val.t_v₁ y.1
    have h₂ := Υ.val.t_v₁ (π y).1
    rw [h.val_eq y, h₁] at h₂
    have h' : (Γ.outs y.1).map Γ.val.v₀ = (Υ.outs (π y).1).map Υ.val.v₀ :=
      FreeMonoid.ofList.injective h₂
    exact (getElem_eq_of_map_eq _ _ h' j.1 j.2
      ((outs_length_eq_of_val (h.val_eq y)).symm ▸ j.2)).symm

/-! ### The duplicates of `Δ̃_Γ` over each port -/

section Count

variable (Γ) in
/-- The duplicates of `Δ̃_Γ` whose input has its origin at the port `p`. -/
def DupAt (p : Γ.PortT) (y : N) : Prop :=
  Γ.val.IsDup y ∧ ¬ Γ.QuasiTerminal y ∧
    ∃ f ∈ Γ.ins y, ReflTransGen (Γ.toPGraph.DupStep Γ.val.IsDup) (Γ.portEdge p) f

theorem dupAt_v₁ {p : Γ.PortT} {y : N} (h : Γ.DupAt p y) :
    Γ.val.v₁ y = G.dup (Γ.val.v₀ (Γ.portEdge p)) := by
  obtain ⟨⟨a, ha⟩, -, f, hf, hpf⟩ := h
  obtain ⟨g, hg, hga⟩ := Γ.val.ins_eq_of_dup ha
  rw [hg, List.mem_singleton] at hf
  subst hf
  rw [ha, v₀_eq_of_reflTransGen_dup hpf] at *
  rw [hga]

/-- Every duplicate of `Δ̃_Γ` lies over exactly one port. -/
theorem existsUnique_dupAt [Finite E] {y : N} (hy : Γ.val.IsDup y) (hq : ¬ Γ.QuasiTerminal y) :
    ∃! p, Γ.DupAt p y := by
  obtain ⟨a, ha⟩ := hy
  obtain ⟨f, hf, -⟩ := Γ.val.ins_eq_of_dup ha
  have hfy : Γ.tgt f = some y := (Γ.mem_ins y f).1 (by rw [hf]; exact List.mem_singleton_self _)
  obtain ⟨q, hqf, hq'⟩ := PGraph.exists_isOrigin Γ.dupCond f
  -- `q` reaches the codomain
  have hfc : Γ.toPGraph.ReachCod f := by
    rw [PGraph.not_quasiTerminal_dup_iff ⟨a, ha⟩] at hq
    obtain ⟨hne, hall⟩ := hq
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    exact (hall e he).of_step ⟨y, hfy, (Γ.mem_outs y e).1 he⟩
  have hqc : Γ.toPGraph.ReachCod q := hfc.of_reflTransGen (PGraph.reflTransGen_step_of_dup hqf)
  obtain ⟨p, rfl⟩ : ∃ p, Γ.portEdge p = q := by
    cases hs : Γ.src q with
    | none =>
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ((Γ.mem_dom q).2 hs)
      exact ⟨.inl ⟨⟨j, hj⟩⟩, rfl⟩
    | some z =>
      have hzo : q ∈ Γ.outs z := (Γ.mem_outs z q).2 hs
      have hl : Γ.Live z := ⟨hq' z hs, q, hzo, hqc⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hzo
      exact ⟨.inr ⟨⟨z, hl⟩, ⟨j, hj⟩⟩, rfl⟩
  refine ⟨p, ⟨⟨a, ha⟩, hq, f, by rw [hf]; exact List.mem_singleton_self _, hqf⟩, ?_⟩
  rintro p' ⟨-, -, f', hf', hpf'⟩
  rw [hf, List.mem_singleton] at hf'
  subst hf'
  exact portEdge_injective (PGraph.isOrigin_unique Γ.dupCond ⟨hpf', isRoot_portEdge p'⟩
    ⟨hqf, isRoot_portEdge p⟩)

open scoped Classical in
/-- The number of duplicates of `Δ̃_Γ` over a port is determined by the number of consumers with
their origin at that port. -/
theorem card_dupAt [Fintype N] [Fintype E] (p : Γ.PortT) :
    (Finset.univ.filter (Γ.DupAt p)).card + (if (Finset.univ.filter fun σ : Γ.SlotT =>
      Γ.IsOrigin (Γ.portEdge p) (Γ.slotEdge σ)).card = 0 then 0 else 1) =
      (Finset.univ.filter fun σ : Γ.SlotT => Γ.IsOrigin (Γ.portEdge p) (Γ.slotEdge σ)).card := by
  have hD₂ : ∀ x, Γ.val.IsDup x → ∃ e₁ e₂, Γ.outs x = [e₁, e₂] := by
    rintro x ⟨a, ha⟩
    obtain ⟨e₁, e₂, h, -⟩ := Γ.val.outs_eq_of_t_dup ha
    exact ⟨e₁, e₂, h⟩
  have key := PGraph.binCount_add Γ.dupCond hD₂ (Γ.portEdge p)
  have hcons : Γ.toPGraph.consCount Γ.val.IsDup (Γ.portEdge p) =
      (Finset.univ.filter fun σ : Γ.SlotT => Γ.IsOrigin (Γ.portEdge p) (Γ.slotEdge σ)).card := by
    unfold PGraph.consCount
    refine Finset.card_bij (fun c hc => (Classical.choose ((consumer_iff_exists_slot c).1
      (Finset.mem_filter.1 hc).2.2))) ?_ ?_ ?_
    · intro c hc
      have hs := Classical.choose_spec ((consumer_iff_exists_slot c).1 (Finset.mem_filter.1 hc).2.2)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hs]
      exact ⟨(Finset.mem_filter.1 hc).2.1, isRoot_portEdge p⟩
    · intro c hc c' hc' h
      have hs := Classical.choose_spec ((consumer_iff_exists_slot c).1 (Finset.mem_filter.1 hc).2.2)
      have hs' := Classical.choose_spec ((consumer_iff_exists_slot c').1 (Finset.mem_filter.1 hc').2.2)
      rw [← hs, ← hs', h]
    · intro σ hσ
      refine ⟨Γ.slotEdge σ, ?_, slotEdge_injective ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        exact ⟨hσ.1, (consumer_iff_exists_slot (Γ := Γ) _).2 ⟨σ, rfl⟩⟩
      · exact Classical.choose_spec ((consumer_iff_exists_slot (Γ := Γ) (Γ.slotEdge σ)).1
          ((consumer_iff_exists_slot (Γ := Γ) _).2 ⟨σ, rfl⟩))
  have hbin : Γ.toPGraph.binCount Γ.val.IsDup (Γ.portEdge p) = (Finset.univ.filter (Γ.DupAt p)).card := by
    unfold PGraph.binCount DupAt
    convert rfl
  have huse : Γ.toPGraph.Useful Γ.val.IsDup (Γ.portEdge p) ↔
      (Finset.univ.filter fun σ : Γ.SlotT => Γ.IsOrigin (Γ.portEdge p) (Γ.slotEdge σ)).card ≠ 0 := by
    rw [← hcons]
    unfold PGraph.consCount PGraph.Useful
    rw [Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp
  rw [← hbin, ← hcons]
  by_cases hu : Γ.toPGraph.Useful Γ.val.IsDup (Γ.portEdge p)
  · have hne : Γ.toPGraph.consCount Γ.val.IsDup (Γ.portEdge p) ≠ 0 := by
      rw [hcons]; exact huse.1 hu
    rw [ite_eq_right hne]
    rw [ite_eq_left hu] at key
    exact key
  · have h0 : Γ.toPGraph.consCount Γ.val.IsDup (Γ.portEdge p) = 0 := by
      rw [hcons]; by_contra h0; exact hu (huse.2 h0)
    rw [ite_eq_right hu] at key
    rw [h0, ite_eq_left rfl]
    omega

end Count


/-! ### The extension of `π` to `Δ̃` -/

section Extend

variable (Γ) in
/-- The duplicates of `Δ̃_Γ`. -/
abbrev DupT : Type u₁ := {y // Γ.val.IsDup y ∧ ¬ Γ.QuasiTerminal y}

/-- `Δ̃_Γ` is the disjoint union of the live nodes and the duplicates of `Δ̃_Γ`. -/
noncomputable def tildeEquiv (Γ : Diagram G.toFreeGraphMonoid N E) :
    {x // ¬ Γ.QuasiTerminal x} ≃ {x // Γ.Live x} ⊕ Γ.DupT := by
  classical
  exact
  { toFun := fun x => if h : Γ.val.IsDup x.1 then .inr ⟨x.1, h, x.2⟩
      else .inl ⟨x.1, (PGraph.live_iff x.1).2 ⟨h, x.2⟩⟩
    invFun := fun t => match t with
      | .inl x => ⟨x.1, x.2.not_quasiTerminal⟩
      | .inr y => ⟨y.1, y.2.2⟩
    left_inv := fun x => by
      by_cases h : Γ.val.IsDup x.1 <;> simp [h]
    right_inv := fun t => by
      rcases t with x | y
      · simp [x.2.1]
      · simp [y.2.1] }

theorem tildeEquiv_live (x : {x // Γ.Live x}) :
    Γ.tildeEquiv ⟨x.1, x.2.not_quasiTerminal⟩ = .inl x := by
  classical
  simp [tildeEquiv, x.2.1]

theorem tildeEquiv_symm_val (t : {x // Γ.Live x} ⊕ Γ.DupT) :
    (Γ.tildeEquiv.symm t).1 = Sum.elim (fun x => x.1) (fun y => y.1) t := by
  rcases t with x | y <;> rfl

variable [Finite E] in
/-- The port over which a duplicate of `Δ̃_Γ` lies. -/
noncomputable def portOf (y : Γ.DupT) : Γ.PortT :=
  (existsUnique_dupAt y.2.1 y.2.2).choose

theorem portOf_spec [Finite E] (y : Γ.DupT) : Γ.DupAt (portOf y) y.1 :=
  (existsUnique_dupAt y.2.1 y.2.2).choose_spec.1

theorem portOf_eq [Finite E] {y : Γ.DupT} {p : Γ.PortT} (h : Γ.DupAt p y.1) : portOf y = p :=
  ((existsUnique_dupAt y.2.1 y.2.2).choose_spec.2 p h).symm

/-- The duplicates of `Δ̃_Γ`, sorted by port. -/
noncomputable def dupSigma [Finite E] (Γ : Diagram G.toFreeGraphMonoid N E) :
    Γ.DupT ≃ Σ p : Γ.PortT, {y // Γ.DupAt p y} where
  toFun y := ⟨portOf y, ⟨y.1, portOf_spec y⟩⟩
  invFun t := ⟨t.2.1, t.2.2.1, t.2.2.2.1⟩
  left_inv y := rfl
  right_inv t := by
    obtain ⟨p, y, hy⟩ := t
    exact Sigma.subtype_ext (portOf_eq (Γ := Γ) (y := ⟨y, hy.1, hy.2.1⟩) hy) rfl

open scoped Classical in
theorem card_slots_eq [Fintype N] [Fintype N'] (hd : Γ.domWord = Υ.domWord) (hc : Γ.codWord = Υ.codWord)
    (h : SkeletonIso Γ Υ π) (p : Γ.PortT) :
    (Finset.univ.filter fun σ : Γ.SlotT => Γ.IsOrigin (Γ.portEdge p) (Γ.slotEdge σ)).card =
      (Finset.univ.filter fun σ : Υ.SlotT =>
        Υ.IsOrigin (Υ.portEdge (portEquiv hd h p)) (Υ.slotEdge σ)).card := by
  refine Finset.card_bij (fun σ _ => slotEquiv hc h σ) ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact (originAt_slot_iff hd hc h p σ).1 hσ
  · intro σ _ σ' _ h'
    exact (slotEquiv hc h).injective h'
  · intro σ' hσ'
    refine ⟨(slotEquiv hc h).symm σ', ?_, Equiv.apply_symm_apply _ _⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ' ⊢
    rw [originAt_slot_iff hd hc h p, Equiv.apply_symm_apply]
    exact hσ'

theorem card_dupAt_eq [Finite N] [Finite E] [Finite N'] [Finite E'] (hd : Γ.domWord = Υ.domWord)
    (hc : Γ.codWord = Υ.codWord) (h : SkeletonIso Γ Υ π) (p : Γ.PortT) :
    Nat.card {y // Γ.DupAt p y} = Nat.card {y // Υ.DupAt (portEquiv hd h p) y} := by
  classical
  have := Fintype.ofFinite N
  have := Fintype.ofFinite E
  have := Fintype.ofFinite N'
  have := Fintype.ofFinite E'
  have h₁ := card_dupAt (Γ := Γ) p
  have h₂ := card_dupAt (Γ := Υ) (portEquiv hd h p)
  rw [card_slots_eq hd hc h p] at h₁
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  convert (by omega : (Finset.univ.filter (Γ.DupAt p)).card =
    (Finset.univ.filter (Υ.DupAt (portEquiv hd h p))).card)

/-- **Lemma 4.3, first item, from a skeleton bijection.** "`π` extends to a bijection
`Δ̃_Γ → Δ̃_Υ` compatible with the valuations, that is, `v(x) = w(π(x))` for all `x ∈ Δ̃_Γ`." -/
theorem exists_tilde_of_skeletonIso [Finite N] [Finite E] [Finite N'] [Finite E']
    (hd : Γ.domWord = Υ.domWord) (hc : Γ.codWord = Υ.codWord) (h : SkeletonIso Γ Υ π) :
    ∃ π' : {x // ¬ Γ.QuasiTerminal x} ≃ {y // ¬ Υ.QuasiTerminal y},
      (∀ x, Υ.val.v₁ (π' x).1 = Γ.val.v₁ x.1) ∧
        ∀ x : {x // Γ.Live x}, (π' ⟨x.1, x.2.not_quasiTerminal⟩).1 = (π x).1 := by
  -- the duplicates over each port correspond
  have hf : ∀ p : Γ.PortT, Nonempty ({y // Γ.DupAt p y} ≃ {y // Υ.DupAt (portEquiv hd h p) y}) :=
    fun p => by
      have := Fintype.ofFinite {y // Γ.DupAt p y}
      have := Fintype.ofFinite {y // Υ.DupAt (portEquiv hd h p) y}
      refine ⟨Fintype.equivOfCardEq ?_⟩
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact card_dupAt_eq hd hc h p
  let ψp : ∀ p : Γ.PortT, {y // Γ.DupAt p y} ≃ {y // Υ.DupAt (portEquiv hd h p) y} :=
    fun p => (hf p).some
  let ψ : Γ.DupT ≃ Υ.DupT :=
    (dupSigma Γ).trans ((Equiv.sigmaCongr (portEquiv hd h) ψp).trans (dupSigma Υ).symm)
  have hψ : ∀ y : Γ.DupT, Υ.val.v₁ (ψ y).1 = Γ.val.v₁ y.1 := by
    intro y
    have h₁ : (ψ y).1 = ((ψp (portOf y)) ⟨y.1, portOf_spec y⟩).1 := rfl
    rw [h₁, dupAt_v₁ ((ψp (portOf y)) ⟨y.1, portOf_spec y⟩).2, v₀_portEdge hd h,
      dupAt_v₁ (portOf_spec y)]
  refine ⟨Γ.tildeEquiv.trans ((Equiv.sumCongr π ψ).trans Υ.tildeEquiv.symm), ?_, ?_⟩
  · intro x
    simp only [Equiv.trans_apply]
    rw [tildeEquiv_symm_val]
    have hx : Γ.val.v₁ x.1 = Sum.elim (fun z => Γ.val.v₁ z.1) (fun z => Γ.val.v₁ z.1)
        (Γ.tildeEquiv x) := by
      conv_lhs => rw [← Γ.tildeEquiv.symm_apply_apply x]
      rw [tildeEquiv_symm_val]
      rcases Γ.tildeEquiv x with z | z <;> rfl
    rw [hx]
    rcases Γ.tildeEquiv x with z | z
    · exact h.val_eq z
    · exact hψ z
  · intro x
    simp only [Equiv.trans_apply]
    rw [tildeEquiv_live, tildeEquiv_symm_val]
    rfl

end Extend

end Diagram

end FreeMarkov
