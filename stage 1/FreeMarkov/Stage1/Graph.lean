/-
Free Markov categories, Stage 1: polarized progressive graphs and anchored graphs
as incidence data (Section 2 of the paper; design decision D1 of
`formalization/PLAN.md`).

The paper defines a graph as a Hausdorff space `Γ` with a finite set `Γ₀` of
nodes whose complement is a finite union of open intervals (the edges).  Sections
2–6 use only the incidence data, which determines a graph without circles up to
isomorphism.  Following D1, a graph is formalized as that data:

* a type `N` of (inner) nodes and a type `E` of edges;
* for each edge, its source and its target, an inner node (`some x`) or an outer
  node (`none`); an outer node is attached to exactly one end of one edge, so it
  needs no name of its own;
* for each node `x`, the total orderings of `inn(x)` and `out(x)`, as duplicate-free
  lists enumerating the edges with target, respectively source, `x`
  ("polarized");
* no directed circuit ("progressive");
* for an anchored graph, the total orderings of `dom(Γ)` and `cod(Γ)`, as
  duplicate-free lists enumerating the edges whose source, respectively target, is
  an outer node.

The topological wording of Section 2 (Hausdorff spaces, compactifications,
outer nodes as points) is cited background, recorded in the blueprint.
-/
module

public import FreeMarkov.Stage0
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Relation
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅ u₆

namespace FreeMarkov

/-- The relation "there is an edge from the node `x` to the node `y`", for given
source and target maps. -/
def EdgeAdj {N : Type u₁} {E : Type u₂} (src tgt : E → Option N) (x y : N) : Prop :=
  ∃ e, src e = some x ∧ tgt e = some y

/-- The image of a chain under a map that preserves the relation. -/
theorem transGen_map {α : Type u₁} {β : Type u₂} {r : α → α → Prop} {p : β → β → Prop}
    (f : α → β) (h : ∀ a b, r a b → p (f a) (f b)) {a b : α} (hab : Relation.TransGen r a b) :
    Relation.TransGen p (f a) (f b) := by
  induction hab with
  | single h' => exact .single (h _ _ h')
  | tail _ h' ih => exact ih.tail (h _ _ h')

/-- A **polarized progressive graph** (Section 2), as incidence data on a type `N` of
nodes and a type `E` of edges.

*Section 2.* "An **orientation** of an edge `e` is just a total ordering on the pair
of endpoints of `ê`, where the source `e(0)` is ... and the target `e(1)` ... We say
that `Γ` is **progressive** if it carries a choice of orientation for each of its
edges such that there is no directed circuit ... the **input** `inn(x)` of a node
`x ∈ Γ₀` is the set of the oriented edges with target `x` and the **output**
`out(x)` the set of those with source `x` ... If, in addition, `Γ` is equipped with
a choice of total orderings on `inn(x)` and `out(x)` for each `x ∈ Γ₀` then it is
**polarized**."

`src e = none` means that the source of `e` is an outer node, and similarly for
`tgt`.  A directed circuit `e₁, …, eₙ` passes through inner nodes only (an outer
node is the endpoint of a single edge end), so "no directed circuit" is the
irreflexivity of the transitive closure of the adjacency of nodes. -/
structure PGraph (N : Type u₁) (E : Type u₂) where
  /-- The source `e(0)` of an edge: an inner node, or `none` for an outer node. -/
  src : E → Option N
  /-- The target `e(1)` of an edge: an inner node, or `none` for an outer node. -/
  tgt : E → Option N
  /-- The input `inn(x)`, with its total ordering. -/
  ins : N → List E
  /-- The output `out(x)`, with its total ordering. -/
  outs : N → List E
  ins_nodup (x : N) : (ins x).Nodup
  outs_nodup (x : N) : (outs x).Nodup
  mem_ins (x : N) (e : E) : e ∈ ins x ↔ tgt e = some x
  mem_outs (x : N) (e : E) : e ∈ outs x ↔ src e = some x
  /-- There is no directed circuit. -/
  acyclic (x : N) : ¬ Relation.TransGen (EdgeAdj src tgt) x x

/-- A total ordering of the elements of `E` satisfying `P`, as a duplicate-free list
enumerating them. -/
structure Enumeration {E : Type u₂} (P : E → Prop) where
  /-- The elements in order. -/
  list : List E
  nodup : list.Nodup
  mem_iff (e : E) : e ∈ list ↔ P e

/-- An **anchored** polarized progressive graph.

*Section 2.* "The **domain** `dom(Γ)` of `Γ` consists of the edges whose sources are
outer nodes and the **codomain** `cod(Γ)` those whose targets are outer nodes ... We
say that `Γ` is **anchored** if both `dom(Γ)` and `cod(Γ)` are equipped with a total
ordering." -/
structure AGraph (N : Type u₁) (E : Type u₂) extends PGraph N E where
  /-- The domain `dom(Γ)`, in its total ordering. -/
  dom : List E
  /-- The codomain `cod(Γ)`, in its total ordering. -/
  cod : List E
  dom_nodup : dom.Nodup
  cod_nodup : cod.Nodup
  mem_dom (e : E) : e ∈ dom ↔ src e = none
  mem_cod (e : E) : e ∈ cod ↔ tgt e = none

namespace PGraph

variable {N : Type u₁} {E : Type u₂} (Γ : PGraph N E)

/-- `x ⋖ y`: there is an edge from the node `x` to the node `y`. -/
def Adj (x y : N) : Prop := EdgeAdj Γ.src Γ.tgt x y

/-- *Section 2.* An edge `e` is **pinned** if both its ends are attached to inner
nodes. -/
def IsPinned (e : E) : Prop := Γ.src e ≠ none ∧ Γ.tgt e ≠ none

/-- *Section 2.* An edge `e` is **loose** if neither end is attached to an inner
node. -/
def IsLoose (e : E) : Prop := Γ.src e = none ∧ Γ.tgt e = none

/-- *Section 2.* An edge `e` is **half-loose** if exactly one end is attached to an
inner node. -/
def IsHalfLoose (e : E) : Prop := ¬ Γ.IsPinned e ∧ ¬ Γ.IsLoose e

/-- *Section 2.* The edge `e` belongs to the domain `dom(Γ)`: its source is an outer
node. -/
abbrev IsDom (e : E) : Prop := Γ.src e = none

/-- *Section 2.* The edge `e` belongs to the codomain `cod(Γ)`: its target is an outer
node. -/
abbrev IsCod (e : E) : Prop := Γ.tgt e = none

/-- *Section 2.* "An inner node `x ∈ Γ₀` is **initial** if `inn(x) = ∅`." -/
def IsInitial (x : N) : Prop := Γ.ins x = []

/-- *Section 2.* "... and **terminal** if `out(x) = ∅`." -/
def IsTerminal (x : N) : Prop := Γ.outs x = []

theorem isHalfLoose_iff (e : E) :
    Γ.IsHalfLoose e ↔ (Γ.src e = none ∧ Γ.tgt e ≠ none) ∨ (Γ.src e ≠ none ∧ Γ.tgt e = none) := by
  unfold IsHalfLoose IsPinned IsLoose
  by_cases h₁ : Γ.src e = none <;> by_cases h₂ : Γ.tgt e = none <;> simp [h₁, h₂]

theorem isInitial_iff (x : N) : Γ.IsInitial x ↔ ∀ e, Γ.tgt e ≠ some x := by
  unfold IsInitial
  rw [List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun e => not_congr (Γ.mem_ins x e)

theorem isTerminal_iff (x : N) : Γ.IsTerminal x ↔ ∀ e, Γ.src e ≠ some x := by
  unfold IsTerminal
  rw [List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun e => not_congr (Γ.mem_outs x e)

theorem adj_iff (x y : N) : Γ.Adj x y ↔ ∃ e, Γ.src e = some x ∧ Γ.tgt e = some y := Iff.rfl

theorem not_transGen_adj_self (x : N) : ¬ Relation.TransGen Γ.Adj x x := Γ.acyclic x

end PGraph

namespace Enumeration

variable {E : Type u₂} {P : E → Prop}

theorem mem_of_mem (o : Enumeration P) {e : E} (h : e ∈ o.list) : P e := (o.mem_iff e).1 h

/-- An enumeration of `P` identifies the elements satisfying `P` with the positions
`Fin n` of the list. -/
noncomputable def equivFin (o : Enumeration P) : {e // P e} ≃ Fin o.list.length := by
  classical
  exact ((List.Nodup.getEquiv o.list o.nodup).trans (Equiv.subtypeEquivRight o.mem_iff)).symm

@[simp] theorem equivFin_symm_apply_val (o : Enumeration P) (i : Fin o.list.length) :
    (o.equivFin.symm i).1 = o.list[i] := by
  classical
  simp [equivFin]

theorem equivFin_symm_mk (o : Enumeration P) (i : ℕ) (hi : i < o.list.length) :
    o.equivFin.symm ⟨i, hi⟩ = ⟨o.list[i], o.mem_of_mem (List.getElem_mem _)⟩ :=
  Subtype.ext (by simp)

/-- The bijection between the elements enumerated by two enumerations of the same
length that matches them position by position. -/
noncomputable def matching {E' : Type u₃} {P' : E' → Prop} (o : Enumeration P)
    (o' : Enumeration P') (h : o.list.length = o'.list.length) : {e // P e} ≃ {e // P' e} :=
  o.equivFin.trans ((finCongr h).trans o'.equivFin.symm)

theorem matching_symm_apply {E' : Type u₃} {P' : E' → Prop} (o : Enumeration P)
    (o' : Enumeration P') (h : o.list.length = o'.list.length) (i : Fin o.list.length) :
    o.matching o' h (o.equivFin.symm i) = o'.equivFin.symm (finCongr h i) := by
  simp [matching]

theorem matching_getElem {E' : Type u₃} {P' : E' → Prop} (o : Enumeration P)
    (o' : Enumeration P') (h : o.list.length = o'.list.length) (i : ℕ) (hi : i < o.list.length) :
    (o.matching o' h ⟨o.list[i], o.mem_of_mem (List.getElem_mem _)⟩).1 = o'.list[i]'(h ▸ hi) := by
  rw [← o.equivFin_symm_mk i hi, matching_symm_apply, equivFin_symm_apply_val]
  rfl

/-- The matching sends `x` to an element `y` with `f x = g y` whenever `f` and `g`
agree position by position on the two lists. -/
theorem matching_spec {E' : Type u₃} {P' : E' → Prop} {C : Type u₄} (o : Enumeration P)
    (o' : Enumeration P') (h : o.list.length = o'.list.length) (f : E → C) (g : E' → C)
    (hfg : o.list.map f = o'.list.map g) (x : {e // P e}) :
    g (o.matching o' h x).1 = f x.1 := by
  obtain ⟨i, rfl⟩ := o.equivFin.symm.surjective x
  rw [matching_symm_apply, equivFin_symm_apply_val, equivFin_symm_apply_val]
  have := congrArg (fun l => l[i.1]?) hfg
  simp only [List.getElem?_map, List.getElem?_eq_getElem i.2,
    List.getElem?_eq_getElem (h ▸ i.2 : i.1 < o'.list.length), Option.map_some,
    Option.some.injEq] at this
  exact this.symm

/-- Matchings are compatible with maps that carry the enumerations to enumerations. -/
theorem matching_map {E' : Type u₃} {P' : E' → Prop} {F : Type u₄} {F' : Type u₅}
    {Q : F → Prop} {Q' : F' → Prop} (o : Enumeration P) (o' : Enumeration P')
    (p : Enumeration Q) (p' : Enumeration Q') (h : o.list.length = o'.list.length)
    (h' : p.list.length = p'.list.length) (φ : E → F) (ψ : E' → F')
    (hp : p.list = o.list.map φ) (hp' : p'.list = o'.list.map ψ) (c : {e // P e})
    (hc : Q (φ c.1)) :
    (p.matching p' h' ⟨φ c.1, hc⟩).1 = ψ (o.matching o' h c).1 := by
  obtain ⟨j, rfl⟩ := o.equivFin.symm.surjective c
  have hj : j.1 < p.list.length := by rw [hp, List.length_map]; exact j.2
  have hc' : (⟨φ (o.equivFin.symm j).1, hc⟩ : {e // Q e}) = p.equivFin.symm ⟨j, hj⟩ := by
    refine Subtype.ext ?_
    simp only [equivFin_symm_apply_val]
    simp [hp]
  rw [hc', matching_symm_apply, matching_symm_apply, equivFin_symm_apply_val,
    equivFin_symm_apply_val]
  simp [hp']

end Enumeration

namespace AGraph

variable {N : Type u₁} {E : Type u₂}

/-- The domain of an anchored graph as an enumeration of the edges whose source is an
outer node. -/
def domEnum (Γ : AGraph N E) : Enumeration Γ.IsDom := ⟨Γ.dom, Γ.dom_nodup, Γ.mem_dom⟩

/-- The codomain of an anchored graph as an enumeration of the edges whose target is
an outer node. -/
def codEnum (Γ : AGraph N E) : Enumeration Γ.IsCod := ⟨Γ.cod, Γ.cod_nodup, Γ.mem_cod⟩

/-- Anchoring a polarized graph by total orderings of its domain and codomain. -/
def ofPGraph (Γ : PGraph N E) (d : Enumeration Γ.IsDom) (c : Enumeration Γ.IsCod) :
    AGraph N E where
  toPGraph := Γ
  dom := d.list
  cod := c.list
  dom_nodup := d.nodup
  cod_nodup := c.nodup
  mem_dom := d.mem_iff
  mem_cod := c.mem_iff

end AGraph

/-! ### Isomorphisms of graphs -/

/-- An **isomorphism of polarized graphs** `Γ → Γ'`: bijections of nodes and of edges
that carry the ordered inputs and outputs of each node to those of its image.  (They
then preserve sources and targets: `PGraph.Iso.src_map`, `tgt_map`.) -/
structure PGraph.Iso {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}
    (Γ : PGraph N E) (Γ' : PGraph N' E') where
  /-- The bijection of nodes. -/
  eN : N ≃ N'
  /-- The bijection of edges. -/
  eE : E ≃ E'
  ins_map (x : N) : Γ'.ins (eN x) = (Γ.ins x).map eE
  outs_map (x : N) : Γ'.outs (eN x) = (Γ.outs x).map eE

/-- An **isomorphism of anchored graphs**: an isomorphism of polarized graphs that
preserves the anchoring. -/
structure AGraph.Iso {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}
    (Γ : AGraph N E) (Γ' : AGraph N' E') extends PGraph.Iso Γ.toPGraph Γ'.toPGraph where
  dom_map : Γ'.dom = Γ.dom.map eE
  cod_map : Γ'.cod = Γ.cod.map eE

namespace PGraph.Iso

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄} {N'' : Type u₅}
  {E'' : Type u₆} {Γ : PGraph N E} {Γ' : PGraph N' E'} {Γ'' : PGraph N'' E''}

theorem src_map (i : Γ.Iso Γ') (e : E) : Γ'.src (i.eE e) = (Γ.src e).map i.eN := by
  cases h : Γ.src e with
  | some x =>
    rw [Option.map_some, ← Γ'.mem_outs, i.outs_map]
    exact List.mem_map_of_mem ((Γ.mem_outs x e).2 h)
  | none =>
    rw [Option.map_none]
    by_contra h'
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 h'
    rw [← Γ'.mem_outs, ← i.eN.apply_symm_apply y, i.outs_map] at hy
    obtain ⟨e', he', hee'⟩ := List.mem_map.1 hy
    rw [i.eE.injective hee', Γ.mem_outs] at he'
    rw [h] at he'
    exact Option.some_ne_none _ he'.symm

theorem tgt_map (i : Γ.Iso Γ') (e : E) : Γ'.tgt (i.eE e) = (Γ.tgt e).map i.eN := by
  cases h : Γ.tgt e with
  | some x =>
    rw [Option.map_some, ← Γ'.mem_ins, i.ins_map]
    exact List.mem_map_of_mem ((Γ.mem_ins x e).2 h)
  | none =>
    rw [Option.map_none]
    by_contra h'
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 h'
    rw [← Γ'.mem_ins, ← i.eN.apply_symm_apply y, i.ins_map] at hy
    obtain ⟨e', he', hee'⟩ := List.mem_map.1 hy
    rw [i.eE.injective hee', Γ.mem_ins] at he'
    rw [h] at he'
    exact Option.some_ne_none _ he'.symm

/-- The identity isomorphism. -/
def refl (Γ : PGraph N E) : Γ.Iso Γ where
  eN := Equiv.refl N
  eE := Equiv.refl E
  ins_map _ := by simp
  outs_map _ := by simp

/-- The inverse isomorphism. -/
def symm (i : Γ.Iso Γ') : Γ'.Iso Γ where
  eN := i.eN.symm
  eE := i.eE.symm
  ins_map x := by
    rw [← i.eN.apply_symm_apply x, i.ins_map]
    simp
  outs_map x := by
    rw [← i.eN.apply_symm_apply x, i.outs_map]
    simp

/-- The composite isomorphism. -/
def trans (i : Γ.Iso Γ') (k : Γ'.Iso Γ'') : Γ.Iso Γ'' where
  eN := i.eN.trans k.eN
  eE := i.eE.trans k.eE
  ins_map x := by simp [k.ins_map, i.ins_map]
  outs_map x := by simp [k.outs_map, i.outs_map]

end PGraph.Iso

namespace AGraph.Iso

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄} {N'' : Type u₅}
  {E'' : Type u₆} {Γ : AGraph N E} {Γ' : AGraph N' E'} {Γ'' : AGraph N'' E''}

/-- The identity isomorphism. -/
def refl (Γ : AGraph N E) : Γ.Iso Γ where
  toIso := PGraph.Iso.refl _
  dom_map := by simp [PGraph.Iso.refl]
  cod_map := by simp [PGraph.Iso.refl]

/-- The inverse isomorphism. -/
def symm (i : Γ.Iso Γ') : Γ'.Iso Γ where
  toIso := i.toIso.symm
  dom_map := by simp [PGraph.Iso.symm, i.dom_map]
  cod_map := by simp [PGraph.Iso.symm, i.cod_map]

/-- The composite isomorphism. -/
def trans (i : Γ.Iso Γ') (k : Γ'.Iso Γ'') : Γ.Iso Γ'' where
  toIso := i.toIso.trans k.toIso
  dom_map := by simp [PGraph.Iso.trans, i.dom_map, k.dom_map]
  cod_map := by simp [PGraph.Iso.trans, i.cod_map, k.cod_map]

end AGraph.Iso

/-! ### Transport along bijections -/

namespace PGraph

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}

/-- The polarized graph obtained by renaming nodes and edges along bijections. -/
def transport (Γ : PGraph N E) (eN : N ≃ N') (eE : E ≃ E') : PGraph N' E' where
  src e := (Γ.src (eE.symm e)).map eN
  tgt e := (Γ.tgt (eE.symm e)).map eN
  ins x := (Γ.ins (eN.symm x)).map eE
  outs x := (Γ.outs (eN.symm x)).map eE
  ins_nodup x := (Γ.ins_nodup _).map eE.injective
  outs_nodup x := (Γ.outs_nodup _).map eE.injective
  mem_ins x e := by
    rw [List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Equiv.symm_apply_apply, (Γ.mem_ins _ _).1 ha]
      simp
    · intro h
      refine ⟨eE.symm e, ?_, by simp⟩
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [Γ.mem_ins, hy, Equiv.symm_apply_apply]
  mem_outs x e := by
    rw [List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Equiv.symm_apply_apply, (Γ.mem_outs _ _).1 ha]
      simp
    · intro h
      refine ⟨eE.symm e, ?_, by simp⟩
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [Γ.mem_outs, hy, Equiv.symm_apply_apply]
  acyclic x h := by
    refine Γ.acyclic (eN.symm x) (transGen_map eN.symm (fun a b hab => ?_) h)
    obtain ⟨e, he₁, he₂⟩ := hab
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.1 he₁
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 he₂
    exact ⟨eE.symm e, by simpa using ha', by simpa using hb'⟩

/-- A graph is isomorphic to its transport. -/
def isoTransport (Γ : PGraph N E) (eN : N ≃ N') (eE : E ≃ E') : Γ.Iso (Γ.transport eN eE) where
  eN := eN
  eE := eE
  ins_map x := by simp [transport]
  outs_map x := by simp [transport]

end PGraph

namespace AGraph

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}

/-- The anchored graph obtained by renaming nodes and edges along bijections. -/
def transport (Γ : AGraph N E) (eN : N ≃ N') (eE : E ≃ E') : AGraph N' E' where
  toPGraph := Γ.toPGraph.transport eN eE
  dom := Γ.dom.map eE
  cod := Γ.cod.map eE
  dom_nodup := Γ.dom_nodup.map eE.injective
  cod_nodup := Γ.cod_nodup.map eE.injective
  mem_dom e := by
    rw [List.mem_map]
    simp only [PGraph.transport, Option.map_eq_none_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using (Γ.mem_dom a).1 ha
    · intro h
      exact ⟨eE.symm e, (Γ.mem_dom _).2 h, by simp⟩
  mem_cod e := by
    rw [List.mem_map]
    simp only [PGraph.transport, Option.map_eq_none_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using (Γ.mem_cod a).1 ha
    · intro h
      exact ⟨eE.symm e, (Γ.mem_cod _).2 h, by simp⟩

/-- An anchored graph is isomorphic to its transport. -/
def isoTransport (Γ : AGraph N E) (eN : N ≃ N') (eE : E ≃ E') : Γ.Iso (Γ.transport eN eE) where
  toIso := Γ.toPGraph.isoTransport eN eE
  dom_map := rfl
  cod_map := rfl

end AGraph

end FreeMarkov
