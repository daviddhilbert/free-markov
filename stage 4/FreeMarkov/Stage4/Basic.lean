/-
Free Markov categories, Stage 4: the notions of Section 4 after Remark 4.2 on a single
graph — directed paths as chains of consecutive edges, reaching the codomain, the
origin of an edge, quasi-terminal nodes, live nodes, consumers.

They are defined for a polarized graph together with a predicate `D` on its nodes ("the
value of the node is a duplicate"); for a diagram in a free DD-graph monoid `D` is
`Valuation.IsDup` (`Diagram.lean` of this stage).

Readings fixed here (recorded in `stage 4/STATUS.md`):

* "a directed path `p` with `p(0) = x` that ends in `cod(Γ)`" is a chain of consecutive
  edges from an output of `x` to an edge of `cod(Γ)` (`Step`, `ReachCod`); directed paths as
  lists (`PGraph.IsPath`, Stage 1) are equivalent (`exists_isPath_iff`).
* "every maximal directed path `p` with `p(0) = x` ends at a terminal node" is read as "no
  directed path starting at `x` ends in `cod(Γ)`": a maximal directed path ends at a terminal
  node or at an outer node, and an outer node at the end of a path is in `cod(Γ)`.
-/
module

public import FreeMarkov.Stage3

@[expose] public section

universe u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

namespace PGraph

variable {N : Type u₁} {E : Type u₂} (Γ : PGraph N E)

/-! ### Consecutive edges and directed paths -/

/-- `e(1) = e'(0)` is an inner node: `e, e'` are consecutive edges of a directed path. -/
def Step (e e' : E) : Prop := ∃ x, Γ.tgt e = some x ∧ Γ.src e' = some x

variable {Γ}

theorem reflTransGen_of_isChain : ∀ (e : E) (l : List E), (e :: l).IsChain Γ.Step →
    ReflTransGen Γ.Step e ((e :: l).getLast (List.cons_ne_nil _ _))
  | e, [], _ => ReflTransGen.refl
  | e, e' :: l, h => by
    rw [List.isChain_cons_cons] at h
    rw [List.getLast_cons_cons]
    exact ReflTransGen.head h.1 (reflTransGen_of_isChain e' l h.2)

theorem exists_isChain_of_reflTransGen {e e' : E} (h : ReflTransGen Γ.Step e e') :
    ∃ l : List E, (e :: l).IsChain Γ.Step ∧ (e :: l).getLast (List.cons_ne_nil _ _) = e' := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨[], List.isChain_singleton _, rfl⟩
  | head hab _ ih =>
    obtain ⟨l, hl, hl'⟩ := ih
    exact ⟨_ :: l, List.isChain_cons_cons.2 ⟨hab, hl⟩, by rw [List.getLast_cons_cons]; exact hl'⟩

/-- A directed path (a list of edges, Stage 1) from `e` to `e'` exists if and only if `e'`
follows `e` through consecutive edges. -/
theorem exists_isPath_iff (e e' : E) :
    (∃ p, Γ.IsPath p ∧ p.head? = some e ∧ p.getLast? = some e') ↔ ReflTransGen Γ.Step e e' := by
  constructor
  · rintro ⟨p, hp, h₁, h₂⟩
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hp.1
    simp only [List.head?_cons, Option.some.injEq] at h₁
    subst h₁
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), Option.some.injEq] at h₂
    rw [← h₂]
    exact reflTransGen_of_isChain _ _ hp.2
  · intro h
    obtain ⟨l, hl, hl'⟩ := exists_isChain_of_reflTransGen h
    refine ⟨e :: l, ⟨List.cons_ne_nil _ _, hl⟩, rfl, ?_⟩
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hl']

theorem Step.lt {e e' : E} (h : Γ.Step e e') {x : N} (hx : Γ.src e = some x)
    {y : N} (hy : Γ.tgt e' = some y) : Γ.Lt x y := by
  obtain ⟨z, hz, hz'⟩ := h
  exact (Γ.lt_of_edge hx hz).trans (Γ.lt_of_edge hz' hy)

/-- Along a chain of consecutive edges the target of the first is below the source of the
last. -/
theorem le_of_transGen_step {e e' : E} (h : TransGen Γ.Step e e') :
    ∃ x y, Γ.tgt e = some x ∧ Γ.src e' = some y ∧ Γ.Le x y := by
  induction h with
  | single h =>
    obtain ⟨x, hx, hx'⟩ := h
    exact ⟨x, x, hx, hx', Or.inr rfl⟩
  | tail _ h ih =>
    obtain ⟨x, y, hx, hy, hxy⟩ := ih
    obtain ⟨z, hz, hz'⟩ := h
    exact ⟨x, z, hx, hz', Or.inl (hxy.trans_lt (Γ.lt_of_edge hy hz))⟩

theorem not_transGen_step_self (e : E) : ¬ TransGen Γ.Step e e := by
  intro h
  obtain ⟨x, y, hx, hy, hxy⟩ := le_of_transGen_step h
  exact Γ.lt_irrefl _ (hxy.trans_lt (Γ.lt_of_edge hy hx))

/-- Induction downstream: the relation "`a` comes after `b`" is well founded. -/
theorem wellFounded_down [Finite E] : WellFounded fun a b : E => TransGen Γ.Step b a := by
  have : IsTrans E fun a b : E => TransGen Γ.Step b a := ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩
  have : Std.Irrefl fun a b : E => TransGen Γ.Step b a := ⟨fun a h => not_transGen_step_self a h⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- Induction upstream: the relation "`a` comes before `b`" is well founded. -/
theorem wellFounded_up [Finite E] : WellFounded fun a b : E => TransGen Γ.Step a b := by
  have : IsTrans E fun a b : E => TransGen Γ.Step a b := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  have : Std.Irrefl fun a b : E => TransGen Γ.Step a b := ⟨fun a h => not_transGen_step_self a h⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

theorem step_of_mem {e e' : E} {x : N} (he : e ∈ Γ.ins x) (he' : e' ∈ Γ.outs x) :
    Γ.Step e e' := ⟨x, (Γ.mem_ins x e).1 he, (Γ.mem_outs x e').1 he'⟩

theorem Step.mem {e e' : E} (h : Γ.Step e e') : ∃ x, e ∈ Γ.ins x ∧ e' ∈ Γ.outs x := by
  obtain ⟨x, hx, hx'⟩ := h
  exact ⟨x, (Γ.mem_ins x e).2 hx, (Γ.mem_outs x e').2 hx'⟩

/-! ### Reaching the codomain, origins, live and quasi-terminal nodes -/

variable (Γ) (D : N → Prop)

/-- A directed path beginning with `e` ends in `cod(Γ)`. -/
def ReachCod (e : E) : Prop := ∃ c, ReflTransGen Γ.Step e c ∧ Γ.tgt c = none

/-- `e, e'` are consecutive edges and their common node is a duplicate: following `e'`
backward through the duplicate leads to `e`. -/
def DupStep (e e' : E) : Prop := ∃ x, D x ∧ Γ.tgt e = some x ∧ Γ.src e' = some x

/-- An edge whose source is not a duplicate: an edge of `dom(Γ)` or an output of a node whose
value is not a duplicate. -/
def IsRoot (q : E) : Prop := ∀ x, Γ.src q = some x → ¬ D x

/-- **Origin** (Section 4). "For an edge `e` of `Γ`, its origin `e°` is the edge obtained by
following `e` backward through the duplicates: if `e(0)` is a node with `v(e(0))` a duplicate
then `e° = e'°`, where `e'` is the input of `e(0)`, and otherwise `e° = e`."  `IsOrigin q e`:
`q` is the origin of `e` (it is unique and exists, `isOrigin_unique`, `exists_isOrigin`). -/
def IsOrigin (q e : E) : Prop := ReflTransGen (Γ.DupStep D) q e ∧ Γ.IsRoot D q

/-- **Live node** (Section 4). "A node `x` of `Γ` is live if ... `v(x)` is not a duplicate
and there is a directed path `p` in `Γ` with `p(0) = x` that ends in `cod(Γ)`." -/
def Live (x : N) : Prop := ¬ D x ∧ ∃ e ∈ Γ.outs x, Γ.ReachCod e

/-- **Quasi-terminal node** (Section 4). "A node `x` ... is quasi-terminal if either it is
terminal or every maximal directed path `p` in `Γ` with `p(0) = x` ends at a terminal node or,
in case that `v(x)` is a duplicate, this is so for all such paths through one of the
prongs."  The nodes that are not quasi-terminal form `Δ̃_Γ`. -/
def QuasiTerminal (x : N) : Prop :=
  (∀ e ∈ Γ.outs x, ¬ Γ.ReachCod e) ∨ (D x ∧ ∃ e ∈ Γ.outs x, ¬ Γ.ReachCod e)

/-- **Consumer** (Section 4). "An edge of `Γ` is a consumer if it belongs to `cod(Γ)` or is an
input of a live node." -/
def Consumer (e : E) : Prop := Γ.tgt e = none ∨ ∃ x, Γ.tgt e = some x ∧ Γ.Live D x

/-- Nodes whose value is a duplicate have exactly one input (true for diagrams,
`Valuation.dupCond`). -/
def DupCond : Prop := ∀ x, D x → ∃ e, Γ.ins x = [e]

variable {Γ D}

theorem reachCod_of_tgt_none {e : E} (h : Γ.tgt e = none) : Γ.ReachCod e :=
  ⟨e, ReflTransGen.refl, h⟩

theorem ReachCod.of_step {e e' : E} (h : Γ.Step e e') (h' : Γ.ReachCod e') : Γ.ReachCod e := by
  obtain ⟨c, hc, hc'⟩ := h'
  exact ⟨c, ReflTransGen.head h hc, hc'⟩

theorem ReachCod.of_reflTransGen {e e' : E} (h : ReflTransGen Γ.Step e e') (h' : Γ.ReachCod e') :
    Γ.ReachCod e := by
  obtain ⟨c, hc, hc'⟩ := h'
  exact ⟨c, h.trans hc, hc'⟩

/-- An edge reaches the codomain iff it is in the codomain or an output of its target does. -/
theorem reachCod_iff (e : E) : Γ.ReachCod e ↔
    Γ.tgt e = none ∨ ∃ x, Γ.tgt e = some x ∧ ∃ e' ∈ Γ.outs x, Γ.ReachCod e' := by
  constructor
  · rintro ⟨c, hc, hc'⟩
    rcases hc.cases_head with rfl | ⟨e', ⟨x, hx, hx'⟩, h⟩
    · exact Or.inl hc'
    · exact Or.inr ⟨x, hx, e', (Γ.mem_outs x e').2 hx', c, h, hc'⟩
  · rintro (h | ⟨x, hx, e', he', h⟩)
    · exact reachCod_of_tgt_none h
    · exact h.of_step ⟨x, hx, (Γ.mem_outs x e').1 he'⟩

theorem DupStep.step {e e' : E} (h : Γ.DupStep D e e') : Γ.Step e e' := by
  obtain ⟨x, -, hx, hx'⟩ := h
  exact ⟨x, hx, hx'⟩

theorem reflTransGen_step_of_dup {e e' : E} (h : ReflTransGen (Γ.DupStep D) e e') :
    ReflTransGen Γ.Step e e' := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ h ih => exact ih.tail h.step

theorem IsRoot.not_dupStep {q e : E} (h : Γ.IsRoot D q) : ¬ Γ.DupStep D e q := by
  rintro ⟨x, hx, -, hx'⟩
  exact h x hx' hx

theorem isRoot_of_src_none {q : E} (h : Γ.src q = none) : Γ.IsRoot D q := by
  intro x hx
  rw [h] at hx
  cases hx

theorem isRoot_of_mem_outs {q : E} {x : N} (h : q ∈ Γ.outs x) (hx : ¬ D x) : Γ.IsRoot D q := by
  intro y hy
  rw [(Γ.mem_outs x q).1 h, Option.some.injEq] at hy
  exact hy ▸ hx

/-- With one input per duplicate, the edge preceding `e` through a duplicate is unique. -/
theorem DupStep.unique (hD : Γ.DupCond D) {e₁ e₂ e : E} (h₁ : Γ.DupStep D e₁ e)
    (h₂ : Γ.DupStep D e₂ e) : e₁ = e₂ := by
  obtain ⟨x, hx, hx₁, hx'⟩ := h₁
  obtain ⟨y, -, hy₂, hy'⟩ := h₂
  rw [hx', Option.some.injEq] at hy'
  subst hy'
  obtain ⟨f, hf⟩ := hD x hx
  have h₁ : e₁ ∈ Γ.ins x := (Γ.mem_ins x e₁).2 hx₁
  have h₂ : e₂ ∈ Γ.ins x := (Γ.mem_ins x e₂).2 hy₂
  rw [hf, List.mem_singleton] at h₁ h₂
  rw [h₁, h₂]

/-- Two chains through duplicates ending at the same edge: one is an initial part of the
other (the backward walk is deterministic). -/
theorem reflTransGen_dup_total (hD : Γ.DupCond D) {a b e : E} (ha : ReflTransGen (Γ.DupStep D) a e)
    (hb : ReflTransGen (Γ.DupStep D) b e) :
    ReflTransGen (Γ.DupStep D) a b ∨ ReflTransGen (Γ.DupStep D) b a := by
  induction ha generalizing b with
  | refl => exact Or.inr hb
  | @tail c d hac hcd ih =>
    rcases hb.cases_tail with rfl | ⟨c', hbc', hc'd⟩
    · exact Or.inl (hac.tail hcd)
    · rw [DupStep.unique hD hc'd hcd] at hbc'
      exact ih hbc'

/-- **The origin is unique.** -/
theorem isOrigin_unique (hD : Γ.DupCond D) {q q' e : E} (h : Γ.IsOrigin D q e)
    (h' : Γ.IsOrigin D q' e) : q = q' := by
  rcases reflTransGen_dup_total hD h.1 h'.1 with h₁ | h₁
  · rcases h₁.cases_tail with rfl | ⟨c, -, hc⟩
    · rfl
    · exact (h'.2.not_dupStep hc).elim
  · rcases h₁.cases_tail with rfl | ⟨c, -, hc⟩
    · rfl
    · exact (h.2.not_dupStep hc).elim

/-- **The origin exists** ("this is well defined because there are no directed circuits"). -/
theorem exists_isOrigin [Finite E] (hD : Γ.DupCond D) (e : E) : ∃ q, Γ.IsOrigin D q e := by
  induction e using Γ.wellFounded_up.induction with
  | _ e ih =>
    by_cases h : ∃ x, Γ.src e = some x ∧ D x
    · obtain ⟨x, hx, hDx⟩ := h
      obtain ⟨f, hf⟩ := hD x hDx
      have hfx : Γ.tgt f = some x := (Γ.mem_ins x f).1 (by rw [hf]; exact List.mem_singleton_self _)
      have hst : Γ.DupStep D f e := ⟨x, hDx, hfx, hx⟩
      obtain ⟨q, hq, hq'⟩ := ih f (TransGen.single hst.step)
      exact ⟨q, hq.tail hst, hq'⟩
    · exact ⟨e, ReflTransGen.refl, fun x hx hDx => h ⟨x, hx, hDx⟩⟩

/-- The origin of `e`. -/
noncomputable def origin [Finite E] (hD : Γ.DupCond D) (e : E) : E :=
  (exists_isOrigin hD e).choose

theorem origin_spec [Finite E] (hD : Γ.DupCond D) (e : E) : Γ.IsOrigin D (Γ.origin hD e) e :=
  (exists_isOrigin hD e).choose_spec

theorem origin_eq_iff [Finite E] (hD : Γ.DupCond D) (e q : E) :
    Γ.origin hD e = q ↔ Γ.IsOrigin D q e :=
  ⟨fun h => h ▸ origin_spec hD e, fun h => isOrigin_unique hD (origin_spec hD e) h⟩

/-- "In other words": a node whose value is not a duplicate is live iff it is not
quasi-terminal. -/
theorem live_iff (x : N) : Γ.Live D x ↔ ¬ D x ∧ ¬ Γ.QuasiTerminal D x := by
  unfold Live QuasiTerminal
  constructor
  · rintro ⟨hx, e, he, h⟩
    refine ⟨hx, ?_⟩
    rintro (h' | ⟨h', -⟩)
    · exact h' e he h
    · exact hx h'
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    by_contra h'
    push Not at h'
    exact h (Or.inl h')

theorem Live.not_dup {x : N} (h : Γ.Live D x) : ¬ D x := h.1

theorem Live.not_quasiTerminal {x : N} (h : Γ.Live D x) : ¬ Γ.QuasiTerminal D x :=
  ((live_iff x).1 h).2

/-- A duplicate outside `Δ_Γ`: both prongs reach the codomain. -/
theorem not_quasiTerminal_dup_iff {x : N} (hx : D x) :
    ¬ Γ.QuasiTerminal D x ↔ (Γ.outs x ≠ [] ∧ ∀ e ∈ Γ.outs x, Γ.ReachCod e) := by
  unfold QuasiTerminal
  constructor
  · intro h
    push Not at h
    obtain ⟨⟨e, he, -⟩, h₂⟩ := h
    exact ⟨List.ne_nil_of_mem he, h₂ hx⟩
  · rintro ⟨hne, h⟩ (h' | ⟨-, e, he, h'⟩)
    · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
      exact h' e he (h e he)
    · exact h' (h e he)

theorem Consumer.reachCod {e : E} (h : Γ.Consumer D e) : Γ.ReachCod e := by
  rcases h with h | ⟨x, hx, -, e', he', h⟩
  · exact reachCod_of_tgt_none h
  · exact h.of_step ⟨x, hx, (Γ.mem_outs x e').1 he'⟩

/-- The first edge after `e` (through duplicates) that is a consumer or ends a path in the
codomain: every edge reaching the codomain has a consumer following it through duplicates. -/
theorem exists_consumer_of_reachCod [Finite E] {e : E} (h : Γ.ReachCod e) :
    ∃ c, ReflTransGen (Γ.DupStep D) e c ∧ Γ.Consumer D c := by
  induction e using Γ.wellFounded_down.induction with
  | _ e ih =>
    rcases (reachCod_iff e).1 h with h' | ⟨x, hx, e', he', h'⟩
    · exact ⟨e, ReflTransGen.refl, Or.inl h'⟩
    · by_cases hDx : D x
      · have hst : Γ.DupStep D e e' := ⟨x, hDx, hx, (Γ.mem_outs x e').1 he'⟩
        obtain ⟨c, hc, hc'⟩ := ih e' (TransGen.single hst.step) h'
        exact ⟨c, ReflTransGen.head hst hc, hc'⟩
      · exact ⟨e, ReflTransGen.refl, Or.inr ⟨x, hx, hDx, e', he', h'⟩⟩

end PGraph

end FreeMarkov
