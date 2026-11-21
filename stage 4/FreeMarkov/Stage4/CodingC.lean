/-
Free Markov categories, Stage 4: codes of the nodes and edges of a Markov minimal sorted comb.

"This shows that `Γ` is determined, up to isomorphisms, by its skeleton and the shapes of these
trees."  Every node of a Markov minimal diagram is a live node, a duplicate or a discard, and every
edge a consumer, the input of a duplicate or the input of a discard.  A duplicate is coded by its
first leaf, a discard by the port of its input, the input of a duplicate by the code of the
duplicate (`codeN`, `codeE`).  In a sorted comb the codes of the edges at a port and of the second
prong of a duplicate are determined by the leaves of the tree and the rank (`codeE_port`,
`codeE_second`).
-/
module

public import FreeMarkov.Stage4.CodingB
public import Mathlib.Data.Finset.Max

@[expose] public section

universe w v u₁ u₂

namespace FreeMarkov

open Relation

namespace Diagram

open scoped Classical

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

section Defs

variable (D : Diagram G.toFreeGraphMonoid N E)

/-- The port at an edge, if any. -/
noncomputable def portOfE (e : E) : Option D.PortT :=
  if h : ∃ p, D.portEdge p = e then some h.choose else none

/-- The code of an edge. -/
noncomputable def codeE (e : E) : Option (E ⊕ E ⊕ D.PortT) :=
  if D.Consumer e then some (.inl e) else
  match D.tgt e with
  | none => none
  | some x => if D.val.IsDup x then (D.outs x).head?.map (fun ℓ => .inr (.inl ℓ))
      else (D.portOfE e).map (fun p => .inr (.inr p))

/-- The code of a node. -/
noncomputable def codeN (x : N) : Option ({x // D.Live x} ⊕ E ⊕ D.PortT) :=
  if h : D.Live x then some (.inl ⟨x, h⟩) else
  if D.val.IsDup x then (D.outs x).head?.map (fun ℓ => .inr (.inl ℓ)) else
  match D.ins x with
  | [f] => (D.portOfE f).map (fun p => .inr (.inr p))
  | _ => none

/-- An element of smallest rank. -/
noncomputable def minR (rk : E → ℕ) (L : Finset E) (hL : L.Nonempty) : E :=
  (L.exists_min_image rk hL).choose

theorem minR_mem (rk : E → ℕ) (L : Finset E) (hL : L.Nonempty) : minR rk L hL ∈ L :=
  (L.exists_min_image rk hL).choose_spec.1

theorem minR_le (rk : E → ℕ) (L : Finset E) (hL : L.Nonempty) {c : E} (hc : c ∈ L) :
    rk (minR rk L hL) ≤ rk c :=
  (L.exists_min_image rk hL).choose_spec.2 c hc

theorem minR_eq {rk : E → ℕ} (hrk : Function.Injective rk) {L : Finset E} (hL : L.Nonempty) {m : E}
    (hm : m ∈ L) (hmin : ∀ c ∈ L, rk m ≤ rk c) : minR rk L hL = m :=
  hrk (le_antisymm (minR_le rk L hL hm) (hmin _ (minR_mem rk L hL)))

/-- The code of the edge at a port whose tree has the leaves `L`. -/
noncomputable def ofLeaves (rk : E → ℕ) (L : Finset E) (p : D.PortT) : Option (E ⊕ E ⊕ D.PortT) :=
  if hL : L.Nonempty then (if L.card = 1 then some (.inl (minR rk L hL)) else some (.inr (.inl (minR rk L hL))))
  else some (.inr (.inr p))

/-- The code of the second prong of a duplicate whose remaining leaves are `L`. -/
noncomputable def nextOf (rk : E → ℕ) (L : Finset E) : Option (E ⊕ E ⊕ D.PortT) :=
  if hL : L.Nonempty then (if L.card = 1 then some (.inl (minR rk L hL)) else some (.inr (.inl (minR rk L hL))))
  else none

end Defs

variable {D : Diagram G.toFreeGraphMonoid N E}

theorem portOfE_portEdge (p : D.PortT) : D.portOfE (D.portEdge p) = some p := by
  have h : ∃ p', D.portEdge p' = D.portEdge p := ⟨p, rfl⟩
  simp only [portOfE, dite_eq_left h, Option.some.injEq]
  exact portEdge_injective h.choose_spec

theorem codeE_consumer {e : E} (hc : D.Consumer e) : D.codeE e = some (.inl e) := by
  simp [codeE, hc]

theorem codeE_dupIn {e : E} {d : N} {a : S} (hte : D.tgt e = some d) (hd : D.val.v₁ d = G.dup a)
    {ℓ o : E} (ho : D.outs d = [ℓ, o]) : D.codeE e = some (.inr (.inl ℓ)) := by
  have hD : D.val.IsDup d := ⟨a, hd⟩
  simp [codeE, not_consumer_of_tgt_dup hte hD, hte, hD, ho]

theorem codeE_discIn {e : E} {x : N} (hte : D.tgt e = some x) (hx : D.val.IsDisc x) (p : D.PortT)
    (hp : D.portEdge p = e) : D.codeE e = some (.inr (.inr p)) := by
  have hnc : ¬ D.Consumer e := by
    rintro (h | ⟨y, hy, hl⟩)
    · rw [hte] at h; cases h
    · rw [hte, Option.some.injEq] at hy
      subst hy
      obtain ⟨-, f, hf, -⟩ := hl
      obtain ⟨b, hb⟩ := hx
      rw [D.val.outs_eq_nil_of_disc hb] at hf
      cases hf
  subst hp
  simp [codeE, hnc, hte, D.val.not_isDup_of_isDisc hx, portOfE_portEdge]

theorem codeN_live {x : N} (hx : D.Live x) : D.codeN x = some (.inl ⟨x, hx⟩) := by
  simp [codeN, hx]

theorem codeN_dup {x : N} {a : S} (hx : D.val.v₁ x = G.dup a) {ℓ o : E} (ho : D.outs x = [ℓ, o]) :
    D.codeN x = some (.inr (.inl ℓ)) := by
  have hD : D.val.IsDup x := ⟨a, hx⟩
  have hl : ¬ D.Live x := fun h => h.1 hD
  simp [codeN, hl, hD, ho]

theorem codeN_disc {x : N} (hx : D.val.IsDisc x) {f : E} (hf : D.ins x = [f]) (p : D.PortT)
    (hp : D.portEdge p = f) : D.codeN x = some (.inr (.inr p)) := by
  have hD := D.val.not_isDup_of_isDisc hx
  have hl : ¬ D.Live x := by
    rintro ⟨-, e, he, -⟩
    obtain ⟨b, hb⟩ := hx
    rw [D.val.outs_eq_nil_of_disc hb] at he
    cases he
  subst hp
  simp [codeN, hl, hD, hf, portOfE_portEdge]

/-! ### The structure of a Markov minimal diagram -/

section Minimal

variable (hX : D.MarkovMinimal)
include hX

/-- A node that is neither live nor a duplicate is a discard. -/
theorem disc_of_not_live (x : N) (hl : ¬ D.Live x) (hd : ¬ D.val.IsDup x) : D.val.IsDisc x :=
  hX x (by
    by_contra hq
    exact hl ((PGraph.live_iff x).2 ⟨hd, hq⟩))

/-- The input of a discard is the edge at a port. -/
theorem port_of_disc_input {e : E} {x : N} (hte : D.tgt e = some x) (hx : D.val.IsDisc x) :
    ∃ p, D.portEdge p = e := by
  have hnr : ¬ D.ReachCod e := by
    intro h
    rcases (PGraph.reachCod_iff e).1 h with h' | ⟨y, hy, f, hf, -⟩
    · rw [hte] at h'; cases h'
    · rw [hte, Option.some.injEq] at hy
      subst hy
      obtain ⟨b, hb⟩ := hx
      rw [D.val.outs_eq_nil_of_disc hb] at hf
      cases hf
  cases hs : D.src e with
  | none =>
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ((D.mem_dom e).2 hs)
    exact ⟨.inl ⟨⟨j, hj⟩⟩, rfl⟩
  | some z =>
    have hze : e ∈ D.outs z := (D.mem_outs z e).2 hs
    by_cases hzd : D.val.IsDup z
    · obtain ⟨a, ha⟩ := hzd
      exact (hnr (reachCod_out hX ha hze)).elim
    · by_cases hzl : D.Live z
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hze
        exact ⟨.inr ⟨⟨z, hzl⟩, ⟨j, hj⟩⟩, rfl⟩
      · obtain ⟨b, hb⟩ := disc_of_not_live hX z hzl hzd
        rw [D.val.outs_eq_nil_of_disc hb] at hze
        cases hze

theorem codeE_ne_none (e : E) : D.codeE e ≠ none := by
  by_cases hc : D.Consumer e
  · rw [codeE_consumer hc]; exact Option.some_ne_none _
  cases hte : D.tgt e with
  | none => exact (hc (Or.inl hte)).elim
  | some x =>
    by_cases hD : D.val.IsDup x
    · obtain ⟨a, ha⟩ := hD
      obtain ⟨ℓ, o, ho, -⟩ := D.val.outs_eq_of_t_dup ha
      rw [codeE_dupIn hte ha ho]; exact Option.some_ne_none _
    · have hl : ¬ D.Live x := fun hl => hc (Or.inr ⟨x, hte, hl⟩)
      have hx := disc_of_not_live hX x hl hD
      obtain ⟨p, hp⟩ := port_of_disc_input hX hte hx
      rw [codeE_discIn hte hx p hp]; exact Option.some_ne_none _

theorem codeN_ne_none (x : N) : D.codeN x ≠ none := by
  by_cases hl : D.Live x
  · rw [codeN_live hl]; exact Option.some_ne_none _
  by_cases hD : D.val.IsDup x
  · obtain ⟨a, ha⟩ := hD
    obtain ⟨ℓ, o, ho, -⟩ := D.val.outs_eq_of_t_dup ha
    rw [codeN_dup ha ho]; exact Option.some_ne_none _
  · have hx := disc_of_not_live hX x hl hD
    obtain ⟨b, hb⟩ := hx
    obtain ⟨f, hf, -⟩ := D.val.ins_eq_of_disc hb
    obtain ⟨p, hp⟩ := port_of_disc_input hX ((D.mem_ins x f).1 (by rw [hf]; simp)) ⟨b, hb⟩
    rw [codeN_disc ⟨b, hb⟩ hf p hp]; exact Option.some_ne_none _

/-- What the code of an edge says. -/
theorem codeE_cases {e : E} {t : E ⊕ E ⊕ D.PortT} (h : D.codeE e = some t) :
    (∃ c, t = .inl c ∧ e = c ∧ D.Consumer c) ∨
    (∃ ℓ, t = .inr (.inl ℓ) ∧ ∃ d a o, D.tgt e = some d ∧ D.val.v₁ d = G.dup a ∧ D.outs d = [ℓ, o]) ∨
    (∃ p, t = .inr (.inr p) ∧ D.portEdge p = e ∧ ∃ x, D.tgt e = some x ∧ D.val.IsDisc x) := by
  by_cases hc : D.Consumer e
  · rw [codeE_consumer hc, Option.some.injEq] at h
    exact Or.inl ⟨e, h.symm, rfl, hc⟩
  cases hte : D.tgt e with
  | none => exact (hc (Or.inl hte)).elim
  | some x =>
    by_cases hD : D.val.IsDup x
    · obtain ⟨a, ha⟩ := hD
      obtain ⟨ℓ, o, ho, -⟩ := D.val.outs_eq_of_t_dup ha
      rw [codeE_dupIn hte ha ho, Option.some.injEq] at h
      exact Or.inr (Or.inl ⟨ℓ, h.symm, x, a, o, rfl, ha, ho⟩)
    · have hl : ¬ D.Live x := fun hl => hc (Or.inr ⟨x, hte, hl⟩)
      have hx := disc_of_not_live hX x hl hD
      obtain ⟨p, hp⟩ := port_of_disc_input hX hte hx
      rw [codeE_discIn hte hx p hp, Option.some.injEq] at h
      exact Or.inr (Or.inr ⟨p, h.symm, hp, x, rfl, hx⟩)

/-- What the code of a node says. -/
theorem codeN_cases {x : N} {t : {x // D.Live x} ⊕ E ⊕ D.PortT} (h : D.codeN x = some t) :
    (∃ hl : D.Live x, t = .inl ⟨x, hl⟩) ∨
    (∃ ℓ, t = .inr (.inl ℓ) ∧ ∃ a o, D.val.v₁ x = G.dup a ∧ D.outs x = [ℓ, o]) ∨
    (∃ p, t = .inr (.inr p) ∧ D.val.IsDisc x ∧ D.ins x = [D.portEdge p]) := by
  by_cases hl : D.Live x
  · rw [codeN_live hl, Option.some.injEq] at h
    exact Or.inl ⟨hl, h.symm⟩
  by_cases hD : D.val.IsDup x
  · obtain ⟨a, ha⟩ := hD
    obtain ⟨ℓ, o, ho, -⟩ := D.val.outs_eq_of_t_dup ha
    rw [codeN_dup ha ho, Option.some.injEq] at h
    exact Or.inr (Or.inl ⟨ℓ, h.symm, a, o, ha, ho⟩)
  · have hx := disc_of_not_live hX x hl hD
    obtain ⟨b, hb⟩ := hx
    obtain ⟨f, hf, -⟩ := D.val.ins_eq_of_disc hb
    obtain ⟨p, hp⟩ := port_of_disc_input hX ((D.mem_ins x f).1 (by rw [hf]; simp)) ⟨b, hb⟩
    rw [codeN_disc ⟨b, hb⟩ hf p hp, Option.some.injEq] at h
    exact Or.inr (Or.inr ⟨p, h.symm, ⟨b, hb⟩, by rw [hf, hp]⟩)

theorem codeE_injective {e e' : E} (h : D.codeE e = D.codeE e') : e = e' := by
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 (codeE_ne_none hX e)
  rw [ht] at h
  rcases codeE_cases hX ht with ⟨c, rfl, rfl, -⟩ | ⟨ℓ, rfl, d, a, o, hd, ha, ho⟩ |
      ⟨p, rfl, hp, -⟩ <;>
    rcases codeE_cases hX h.symm with ⟨c', h₁, rfl, -⟩ | ⟨ℓ', h₁, d', a', o', hd', ha', ho'⟩ |
      ⟨p', h₁, hpp', -⟩ <;> simp only [reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h₁
  · exact h₁
  · subst h₁
    have h₂ : D.src ℓ = some d := (D.mem_outs d ℓ).1 (by rw [ho]; simp)
    have h₃ : D.src ℓ = some d' := (D.mem_outs d' ℓ).1 (by rw [ho']; simp)
    rw [h₂, Option.some.injEq] at h₃
    subst h₃
    obtain ⟨f, hf, -⟩ := D.val.ins_eq_of_dup ha
    have h₄ : e ∈ D.ins d := (D.mem_ins d e).2 hd
    have h₅ : e' ∈ D.ins d := (D.mem_ins d e').2 hd'
    rw [hf, List.mem_singleton] at h₄ h₅
    rw [h₄, h₅]
  · subst h₁
    rw [← hp, ← hpp']

theorem codeN_injective {x x' : N} (h : D.codeN x = D.codeN x') : x = x' := by
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 (codeN_ne_none hX x)
  rw [ht] at h
  rcases codeN_cases hX ht with ⟨hl, rfl⟩ | ⟨ℓ, rfl, a, o, ha, ho⟩ | ⟨p, rfl, hd, hi⟩ <;>
    rcases codeN_cases hX h.symm with ⟨hl', h₁⟩ | ⟨ℓ', h₁, a', o', ha', ho'⟩ | ⟨p', h₁, hd', hi'⟩ <;>
    simp only [reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq, Subtype.mk.injEq] at h₁
  · exact h₁
  · subst h₁
    have h₂ : D.src ℓ = some x := (D.mem_outs x ℓ).1 (by rw [ho]; simp)
    have h₃ : D.src ℓ = some x' := (D.mem_outs x' ℓ).1 (by rw [ho']; simp)
    rw [h₂, Option.some.injEq] at h₃
    exact h₃
  · subst h₁
    have h₂ : D.tgt (D.portEdge p) = some x := (D.mem_ins x _).1 (by rw [hi]; simp)
    have h₃ : D.tgt (D.portEdge p) = some x' := (D.mem_ins x' _).1 (by rw [hi']; simp)
    rw [h₂, Option.some.injEq] at h₃
    exact h₃

end Minimal

end Diagram

end FreeMarkov
