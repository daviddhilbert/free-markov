/-
Free Markov categories, Stage 5: free `DD`-graph monoids in which every letter has at most one
producer, and the **label coherence** of their diagrams.

A `ProdSig` is an alphabet `X` together with a family of *producers* `p : P`, each with a source
word `src p` and an output letter `out p`, distinct producers having distinct output letters.
Its free `DD`-graph monoid `Q.G` has the duplicates and discards on the letters and one arrow
`mech p : src p → out p` for each producer.  Two instances are used in Section 5:

* no producers (`P` empty): the free `DD`-graph monoid with letters `a_1, …, a_n` whose only arrows
  are the duplicates and the discards (Remarks 5.2 and 5.3);
* letters `1, …, n` and one producer `κ_i : w_{S_i} → i` for each `i` (Definition 5.4; the free
  `DD`-graph monoid `W(G)` of Definition 6.2 is of this kind).

`ProdSig.sameSkeleton_of_labels` (label coherence): two diagrams with the same domain (without
repeated letters) and the same codomain, in each of which every producer occurs at most once and
never with its output letter in the domain, and in which the same producers occur, have the same
skeleton.  The reason is the one given in Remarks 5.2, 5.3 and in the proof of Proposition 6.6:
the origin of an edge is determined by its letter (the edge of the domain with that letter, or the
output of the node of its producer), and a node of a producer is live exactly when its letter is
connected to the codomain through producers that occur.

No cited result is used in this file.
-/
module

public import FreeMarkov.Stage5.Multipliers

@[expose] public section

universe u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

/-- A production signature: letters `X`, producers `P`, the source word and the output letter of
each producer; distinct producers have distinct output letters. -/
structure ProdSig where
  /-- The letters. -/
  X : Type
  /-- The producers. -/
  P : Type
  /-- The output letter of a producer. -/
  out : P → X
  out_injective : Function.Injective out
  /-- The source word of a producer. -/
  src : P → FreeMonoid X

namespace ProdSig

variable (Q : ProdSig)

/-- The arrows of `Q.G`: duplicates, discards, producers. -/
inductive Arr (Q : ProdSig) where
  | dup (x : Q.X)
  | disc (x : Q.X)
  | mech (p : Q.P)

/-- The free `DD`-graph monoid of a production signature. -/
@[reducible] def G : FreeDDGraphMonoid.{0, 0} Q.X where
  A := Q.Arr
  s
    | .dup x => FreeMonoid.of x
    | .disc x => FreeMonoid.of x
    | .mech p => Q.src p
  t
    | .dup x => FreeMonoid.of x * FreeMonoid.of x
    | .disc _ => 1
    | .mech p => FreeMonoid.of (Q.out p)
  dup := .dup
  disc := .disc
  s_dup _ := rfl
  t_dup _ := rfl
  s_disc _ := rfl
  t_disc _ := rfl

/-- The letters of a word, as a list. -/
abbrev letters (a : FreeMonoid Q.X) : List Q.X := FreeMonoid.toList a

/-- The letters that are connected to the codomain letters `T` through producers satisfying `K`:
`ℓ` is in `T`, or `ℓ` occurs in the source of a producer `p` with `K p` whose output letter is
connected. -/
inductive LiveLab (K : Q.P → Prop) (T : List Q.X) : Q.X → Prop
  | cod {ℓ : Q.X} : ℓ ∈ T → LiveLab K T ℓ
  | step {p : Q.P} {ℓ : Q.X} : K p → LiveLab K T (Q.out p) → ℓ ∈ Q.letters (Q.src p) →
      LiveLab K T ℓ

variable {Q} {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}

/-! ### Nodes and labels -/

section Diagram

variable (Γ : Diagram Q.G.toFreeGraphMonoid N E)

/-- The producers that occur in `Γ`. -/
def Occurs (p : Q.P) : Prop := ∃ x, Γ.val.v₁ x = .mech p

/-- The **label conditions**: every producer occurs at most once, and never with its output letter
in the domain. -/
structure LabelCond : Prop where
  unique : ∀ p x y, Γ.val.v₁ x = .mech p → Γ.val.v₁ y = .mech p → x = y
  not_dom : ∀ p x, Γ.val.v₁ x = .mech p → Q.out p ∉ Q.letters Γ.domWord

variable {Γ}

theorem outs_of_mech {x : N} {p : Q.P} (h : Γ.val.v₁ x = .mech p) :
    ∃ q, Γ.outs x = [q] ∧ Γ.val.v₀ q = Q.out p := by
  have h₁ := Γ.val.t_v₁ x
  rw [h] at h₁
  have h' : (Γ.outs x).map Γ.val.v₀ = [Q.out p] := (FreeMonoid.ofList.injective h₁).symm
  rcases hx : Γ.outs x with _ | ⟨e, _ | ⟨e', l⟩⟩ <;> rw [hx] at h' <;> simp at h'
  exact ⟨e, rfl, h'⟩

theorem ins_of_mech {x : N} {p : Q.P} (h : Γ.val.v₁ x = .mech p) :
    (Γ.ins x).map Γ.val.v₀ = Q.letters (Q.src p) := by
  have h₁ := Γ.val.s_v₁ x
  rw [h] at h₁
  exact (congrArg FreeMonoid.toList h₁).symm

theorem not_isDup_mech {x : N} {p : Q.P} (h : Γ.val.v₁ x = .mech p) : ¬ Γ.val.IsDup x := by
  rintro ⟨a, ha⟩
  rw [h] at ha
  cases ha

/-- Duplicates keep the letter. -/
theorem label_of_dupStep {e e' : E} (h : Γ.toPGraph.DupStep Γ.val.IsDup e e') :
    Γ.val.v₀ e = Γ.val.v₀ e' := by
  obtain ⟨x, ⟨a, ha⟩, hx, hx'⟩ := h
  obtain ⟨e₀, h₀, l₀⟩ := Γ.val.ins_eq_of_dup ha
  obtain ⟨e₁, e₂, h₁, l₁, l₂⟩ := Γ.val.outs_eq_of_t_dup ha
  have he : e ∈ Γ.ins x := (Γ.mem_ins x e).2 hx
  have he' : e' ∈ Γ.outs x := (Γ.mem_outs x e').2 hx'
  rw [h₀] at he
  rw [h₁] at he'
  rw [List.mem_singleton.1 he, l₀]
  rcases List.mem_pair.1 he' with rfl | rfl
  · exact l₁.symm
  · exact l₂.symm

theorem label_of_reflTransGen {e e' : E} (h : ReflTransGen (Γ.toPGraph.DupStep Γ.val.IsDup) e e') :
    Γ.val.v₀ e = Γ.val.v₀ e' := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (label_of_dupStep h)

theorem label_of_isOrigin {q e : E} (h : Γ.IsOrigin q e) : Γ.val.v₀ q = Γ.val.v₀ e :=
  label_of_reflTransGen h.1

/-- A root is an edge of the domain or the output of the node of a producer. -/
theorem root_cases {q : E} (h : Γ.toPGraph.IsRoot Γ.val.IsDup q) :
    Γ.src q = none ∨ ∃ x p, Γ.src q = some x ∧ Γ.val.v₁ x = .mech p ∧ Γ.outs x = [q] ∧
      Γ.val.v₀ q = Q.out p := by
  rcases hq : Γ.src q with _ | x
  · exact Or.inl rfl
  · right
    have hD := h x hq
    have hqx : q ∈ Γ.outs x := (Γ.mem_outs x q).2 hq
    rcases hv : Γ.val.v₁ x with a | a | p
    · exact (hD ⟨a, hv⟩).elim
    · rw [Γ.val.outs_eq_nil_of_disc (G := Q.G) hv] at hqx
      cases hqx
    · obtain ⟨q', hq', hl⟩ := outs_of_mech hv
      rw [hq'] at hqx
      obtain rfl := List.mem_singleton.1 hqx
      exact ⟨x, p, rfl, hv, hq', hl⟩

theorem dom_label_mem {e : E} (h : Γ.src e = none) : Γ.val.v₀ e ∈ Q.letters Γ.domWord := by
  change Γ.val.v₀ e ∈ Γ.dom.map Γ.val.v₀
  exact List.mem_map_of_mem ((Γ.mem_dom e).2 h)

theorem cod_label_mem {e : E} (h : Γ.tgt e = none) : Γ.val.v₀ e ∈ Q.letters Γ.codWord := by
  change Γ.val.v₀ e ∈ Γ.cod.map Γ.val.v₀
  exact List.mem_map_of_mem ((Γ.mem_cod e).2 h)

/-! ### Origins are determined by letters -/

variable [Finite E]

/-- The origin of an edge is in the domain at position `j` iff the `j`-th letter of the domain is
the letter of the edge. -/
theorem originAt_dom_iff (hΓ : LabelCond Γ) (hnd : (Q.letters Γ.domWord).Nodup) (e : E) (j : ℕ) :
    Γ.OriginAt e (.dom j) ↔ (Q.letters Γ.domWord)[j]? = some (Γ.val.v₀ e) := by
  change _ ↔ (Γ.dom.map Γ.val.v₀)[j]? = _
  constructor
  · rintro ⟨q, hq, ho⟩
    rw [List.getElem?_map, hq, Option.map_some, label_of_isOrigin ho]
  · intro hj
    obtain ⟨q, ho⟩ := Γ.toPGraph.exists_isOrigin Γ.dupCond e
    rcases root_cases ho.2 with hq | ⟨x, p, hx, hp, -, hl⟩
    · obtain ⟨j', hj', hqj⟩ := List.getElem_of_mem ((Γ.mem_dom q).2 hq)
      have h₁ : (Γ.dom.map Γ.val.v₀)[j']? = some (Γ.val.v₀ e) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hj', hqj, Option.map_some,
          label_of_isOrigin ho]
      have hjj : j' = j := by
        have hl₁ : j' < (Γ.dom.map Γ.val.v₀).length := by simpa using hj'
        have hl₂ : j < (Γ.dom.map Γ.val.v₀).length := by
          by_contra hc
          rw [List.getElem?_eq_none (not_lt.1 hc)] at hj
          cases hj
        rw [List.getElem?_eq_getElem hl₁] at h₁
        rw [List.getElem?_eq_getElem hl₂] at hj
        exact (List.Nodup.getElem_inj_iff hnd).1 ((Option.some.inj h₁).trans (Option.some.inj hj).symm)
      subst hjj
      exact ⟨q, by rw [List.getElem?_eq_getElem hj', hqj], ho⟩
    · exfalso
      refine hΓ.not_dom p x hp ?_
      rw [← hl, label_of_isOrigin ho]
      exact List.mem_of_getElem? hj

/-- The origin of an edge is an output of the node `y` (at position `j`) iff `y` is the node of the
producer of the letter of the edge (and `j = 0`). -/
theorem originAt_out_iff (hΓ : LabelCond Γ) (e : E) (y : N) (j : ℕ) :
    Γ.OriginAt e (.out y j) ↔ ∃ p, Γ.val.v₁ y = .mech p ∧ Q.out p = Γ.val.v₀ e ∧ j = 0 := by
  constructor
  · rintro ⟨q, hq, ho⟩
    have hqy : Γ.src q = some y := (Γ.mem_outs y q).1 (List.mem_of_getElem? hq)
    rcases root_cases ho.2 with hn | ⟨x, p, hx, hp, hxq, hl⟩
    · rw [hn] at hqy; cases hqy
    · rw [hx] at hqy
      cases hqy
      refine ⟨p, hp, by rw [← hl, label_of_isOrigin ho], ?_⟩
      rw [hxq] at hq
      rcases j with _ | j
      · rfl
      · simp at hq
  · rintro ⟨p, hp, hl, rfl⟩
    obtain ⟨q, ho⟩ := Γ.toPGraph.exists_isOrigin Γ.dupCond e
    rcases root_cases ho.2 with hn | ⟨x, p', hx, hp', hxq, hl'⟩
    · exfalso
      refine hΓ.not_dom p y hp ?_
      rw [hl, ← label_of_isOrigin ho]
      exact dom_label_mem hn
    · have hpp : p' = p := Q.out_injective (by rw [← hl', label_of_isOrigin ho, hl])
      subst hpp
      have hxy : x = y := hΓ.unique _ _ _ hp' hp
      subst hxy
      exact ⟨q, by rw [hxq]; rfl, ho⟩

/-! ### Live nodes are determined by letters -/

omit [Finite E] in
/-- An edge connected to the codomain carries a letter connected to the codomain letters. -/
theorem liveLab_of_reachCod {e : E} (h : Γ.toPGraph.ReachCod e) :
    Q.LiveLab (Occurs Γ) (Q.letters Γ.codWord) (Γ.val.v₀ e) := by
  obtain ⟨c, hc, hc'⟩ := h
  induction hc using ReflTransGen.head_induction_on with
  | refl => exact .cod (cod_label_mem hc')
  | @head e e' hst _ ih =>
    obtain ⟨x, hx, hx'⟩ := hst
    have he : e ∈ Γ.ins x := (Γ.mem_ins x e).2 hx
    have he' : e' ∈ Γ.outs x := (Γ.mem_outs x e').2 hx'
    rcases hv : Γ.val.v₁ x with a | a | p
    · obtain ⟨e₀, h₀, l₀⟩ := Γ.val.ins_eq_of_dup (G := Q.G) hv
      obtain ⟨e₁, e₂, h₁, l₁, l₂⟩ := Γ.val.outs_eq_of_t_dup (G := Q.G) hv
      rw [h₀] at he
      rw [h₁] at he'
      have : Γ.val.v₀ e = Γ.val.v₀ e' := by
        rw [List.mem_singleton.1 he, l₀]
        rcases List.mem_pair.1 he' with rfl | rfl
        · exact l₁.symm
        · exact l₂.symm
      rw [this]
      exact ih
    · rw [Γ.val.outs_eq_nil_of_disc (G := Q.G) hv] at he'
      cases he'
    · obtain ⟨q, hq, hl⟩ := outs_of_mech hv
      rw [hq] at he'
      rw [List.mem_singleton.1 he'] at ih
      rw [hl] at ih
      refine .step ⟨x, hv⟩ ih ?_
      rw [← ins_of_mech hv]
      exact List.mem_map_of_mem he

omit [Finite E] in
theorem mech_of_live {x : N} (h : Γ.Live x) : ∃ p, Γ.val.v₁ x = .mech p := by
  obtain ⟨hD, e, he, -⟩ := h
  rcases hv : Γ.val.v₁ x with a | a | p
  · exact (hD ⟨a, hv⟩).elim
  · rw [Γ.val.outs_eq_nil_of_disc (G := Q.G) hv] at he
    cases he
  · exact ⟨p, rfl⟩

/-- **Live nodes.** The node of a producer `p` is live iff `out p` is connected to the codomain
letters through producers that occur. -/
theorem live_iff_liveLab (hΓ : LabelCond Γ) {y : N} {p : Q.P} (hy : Γ.val.v₁ y = .mech p) :
    Γ.Live y ↔ Q.LiveLab (Occurs Γ) (Q.letters Γ.codWord) (Q.out p) := by
  constructor
  · rintro ⟨-, e, he, hr⟩
    obtain ⟨q, hq, hl⟩ := outs_of_mech hy
    rw [hq] at he
    rw [List.mem_singleton.1 he] at hr
    rw [← hl]
    exact liveLab_of_reachCod hr
  · intro h
    -- induction on the connection, for every node of a producer with the given letter
    suffices H : ∀ ℓ, Q.LiveLab (Occurs Γ) (Q.letters Γ.codWord) ℓ →
        ∀ (p : Q.P) (y : N), Γ.val.v₁ y = .mech p → Q.out p = ℓ → Γ.Live y from
      H _ h p y hy rfl
    intro ℓ hℓ
    induction hℓ with
    | @cod ℓ hℓ =>
      intro p y hy hpl
      obtain ⟨c, hc, hcl⟩ := List.mem_map.1 (show ℓ ∈ Γ.cod.map Γ.val.v₀ from hℓ)
      have hc' : Γ.tgt c = none := (Γ.mem_cod c).1 hc
      obtain ⟨q, hq, ho⟩ := (originAt_out_iff hΓ c y 0).2 ⟨p, hy, hpl.trans hcl.symm, rfl⟩
      refine ⟨not_isDup_mech hy, q, List.mem_of_getElem? hq, ?_⟩
      exact ⟨c, Γ.toPGraph.reflTransGen_step_of_dup ho.1, hc'⟩
    | @step p' ℓ hK _ hℓ ih =>
      intro p y hy hpl
      obtain ⟨z, hz⟩ := hK
      obtain ⟨-, e'', he'', hr''⟩ := ih p' z hz rfl
      rw [← ins_of_mech hz] at hℓ
      obtain ⟨e, he, hel⟩ := List.mem_map.1 hℓ
      obtain ⟨q, hq, ho⟩ := (originAt_out_iff hΓ e y 0).2 ⟨p, hy, hpl.trans hel.symm, rfl⟩
      refine ⟨not_isDup_mech hy, q, List.mem_of_getElem? hq, ?_⟩
      have hre : Γ.toPGraph.ReachCod e :=
        PGraph.ReachCod.of_step ⟨z, (Γ.mem_ins z e).1 he, (Γ.mem_outs z e'').1 he''⟩ hr''
      obtain ⟨c, hc, hc'⟩ := hre
      exact ⟨c, (Γ.toPGraph.reflTransGen_step_of_dup ho.1).trans hc, hc'⟩

end Diagram

/-! ### Label coherence -/

section Coherence

variable {Γ : Diagram Q.G.toFreeGraphMonoid N E} {Υ : Diagram Q.G.toFreeGraphMonoid N' E'}
  [Finite E] [Finite E']

/-- The live nodes of `Γ` correspond to the producers `p` that occur and whose output letter is
connected to the codomain letters. -/
noncomputable def liveEquiv (hΓ : LabelCond Γ) :
    {x // Γ.Live x} ≃ {p // Occurs Γ p ∧ Q.LiveLab (Occurs Γ) (Q.letters Γ.codWord) (Q.out p)} := by
  classical
  refine Equiv.ofBijective (fun x => ⟨Classical.choose (mech_of_live x.2), ?_, ?_⟩) ⟨?_, ?_⟩
  · exact ⟨x.1, Classical.choose_spec (mech_of_live x.2)⟩
  · exact (live_iff_liveLab hΓ (Classical.choose_spec (mech_of_live x.2))).1 x.2
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    simp only at h
    have hx := Classical.choose_spec (mech_of_live x.2)
    have hy := Classical.choose_spec (mech_of_live y.2)
    rw [h] at hx
    exact Subtype.ext (hΓ.unique _ _ _ hx hy)
  · rintro ⟨p, ⟨y, hy⟩, hl⟩
    have hly : Γ.Live y := (live_iff_liveLab hΓ hy).2 hl
    refine ⟨⟨y, hly⟩, Subtype.ext ?_⟩
    have h := Classical.choose_spec (mech_of_live hly)
    exact ProdSig.Arr.mech.inj (h.symm.trans hy)

theorem liveEquiv_spec (hΓ : LabelCond Γ) (x : {x // Γ.Live x}) :
    Γ.val.v₁ x.1 = .mech (liveEquiv hΓ x).1 :=
  Classical.choose_spec (mech_of_live x.2)

theorem liveEquiv_symm_spec (hΓ : LabelCond Γ) (p) :
    Γ.val.v₁ ((liveEquiv hΓ).symm p).1 = .mech p.1 := by
  have h := liveEquiv_spec hΓ ((liveEquiv hΓ).symm p)
  rwa [Equiv.apply_symm_apply] at h

/-- **Label coherence.** Two diagrams in `Q.G` with the same domain, whose letters are pairwise
distinct, and the same codomain, satisfying the label conditions, in which the same producers
occur, have the same skeleton. -/
theorem sameSkeleton_of_labels (hdom : Γ.domWord = Υ.domWord)
    (hnd : (Q.letters Γ.domWord).Nodup) (hcod : Γ.codWord = Υ.codWord) (hΓ : LabelCond Γ)
    (hΥ : LabelCond Υ) (hocc : ∀ p, Occurs Γ p ↔ Occurs Υ p) : Γ.SameSkeleton Υ := by
  have hnd' : (Q.letters Υ.domWord).Nodup := hdom ▸ hnd
  have hK : Occurs Γ = Occurs Υ := funext fun p => propext (hocc p)
  let e₁ := liveEquiv hΓ
  let e₂ := liveEquiv hΥ
  let c : {p // Occurs Γ p ∧ Q.LiveLab (Occurs Γ) (Q.letters Γ.codWord) (Q.out p)} ≃
      {p // Occurs Υ p ∧ Q.LiveLab (Occurs Υ) (Q.letters Υ.codWord) (Q.out p)} :=
    Equiv.subtypeEquivRight fun p => by rw [hK, hcod]
  let π := (e₁.trans c).trans e₂.symm
  have hπ : ∀ x, Υ.val.v₁ (π x).1 = Γ.val.v₁ x.1 := by
    intro x
    exact (liveEquiv_symm_spec hΥ _).trans (liveEquiv_spec hΓ x).symm
  -- origins of edges with the same letter match
  have OM : ∀ (e : E) (e' : E'), Γ.val.v₀ e = Υ.val.v₀ e' → Diagram.OriginsMatch π e e' := by
    intro e e' hl
    refine ⟨fun j => ?_, fun y j => ?_⟩
    · rw [originAt_dom_iff hΓ hnd, originAt_dom_iff hΥ hnd', hdom, hl]
    · rw [originAt_out_iff hΓ, originAt_out_iff hΥ, hπ, hl]
  refine ⟨hdom, hcod, π, ⟨hπ, ?_, ?_⟩⟩
  · intro i e e' he he'
    refine OM e e' ?_
    have h₁ : (Γ.cod.map Γ.val.v₀)[i]? = (Υ.cod.map Υ.val.v₀)[i]? :=
      congrArg (fun a => (FreeMonoid.toList a)[i]?) hcod
    rw [List.getElem?_map, List.getElem?_map, he, he'] at h₁
    exact Option.some.inj h₁
  · intro x i e e' he he'
    refine OM e e' ?_
    have h₁ := ins_of_mech (liveEquiv_spec hΓ x)
    have h₂ := ins_of_mech (show Υ.val.v₁ (π x).1 = .mech (liveEquiv hΓ x).1 by
      rw [hπ, liveEquiv_spec hΓ x])
    have h₃ : ((Γ.ins x.1).map Γ.val.v₀)[i]? = ((Υ.ins (π x).1).map Υ.val.v₀)[i]? := by
      rw [h₁, h₂]
    rw [List.getElem?_map, List.getElem?_map, he, he'] at h₃
    exact Option.some.inj h₃

end Coherence

end ProdSig

end FreeMarkov
