/-
Free Markov categories, Stage 4: duplicates and discards in a diagram, the skeleton of a
diagram ("have the same skeleton"), directed paths and splitter paths between live nodes and
edges of the domain and codomain.

* `Valuation.IsDup`, `IsDisc`: the value of a node is a duplicate, a discard; a duplicate
  has one input and two outputs, a discard one input and no output.
* `Diagram.SkeletonIso Γ Υ π`: the conditions of "have the same skeleton" for a given
  bijection `π` of live nodes; `Diagram.SameSkeleton`.
* `PGraph.HasPath`, `PGraph.HasSplitter`: directed paths and splitter paths between ends
  (a node, or the `i`-th edge of the domain, respectively of the codomain), stated with
  directed paths as lists (Stage 1), and their description through origins of consumers
  (`dPath_iff_sPath`, `hasSplitter_iff`), which is the core of the proof of the second and
  third items of Lemma 4.3.
-/
module

public import FreeMarkov.Stage4.Basic

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅

namespace FreeMarkov

open Relation

/-! ### Duplicates and discards -/

namespace Valuation

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {ins outs : N → List E}

/-- The value of the node `x` is a duplicate. -/
def IsDup (val : Valuation G.toFreeGraphMonoid ins outs) (x : N) : Prop := ∃ a, val.v₁ x = G.dup a

/-- The value of the node `x` is a discard. -/
def IsDisc (val : Valuation G.toFreeGraphMonoid ins outs) (x : N) : Prop :=
  ∃ a, val.v₁ x = G.disc a

theorem ins_eq_of_s (val : Valuation G.toFreeGraphMonoid ins outs) {x : N} {a : S}
    (h : G.s (val.v₁ x) = FreeMonoid.of a) : ∃ e, ins x = [e] ∧ val.v₀ e = a := by
  rw [val.s_v₁] at h
  have h' : (ins x).map val.v₀ = [a] := FreeMonoid.ofList.injective h
  rcases hx : ins x with _ | ⟨e, _ | ⟨e', l⟩⟩ <;> rw [hx] at h' <;> simp at h'
  exact ⟨e, rfl, h'⟩

theorem outs_eq_of_t_dup (val : Valuation G.toFreeGraphMonoid ins outs) {x : N} {a : S}
    (h : val.v₁ x = G.dup a) : ∃ e₁ e₂, outs x = [e₁, e₂] ∧ val.v₀ e₁ = a ∧ val.v₀ e₂ = a := by
  have h₁ := val.t_v₁ x
  rw [h, G.t_dup] at h₁
  have h' : (outs x).map val.v₀ = [a, a] := (FreeMonoid.ofList.injective h₁).symm
  rcases hx : outs x with _ | ⟨e, _ | ⟨e', _ | ⟨e'', l⟩⟩⟩ <;> rw [hx] at h' <;> simp at h'
  exact ⟨e, e', rfl, h'.1, h'.2⟩

theorem ins_eq_of_dup (val : Valuation G.toFreeGraphMonoid ins outs) {x : N} {a : S}
    (h : val.v₁ x = G.dup a) : ∃ e, ins x = [e] ∧ val.v₀ e = a :=
  val.ins_eq_of_s (by rw [h, G.s_dup])

theorem ins_eq_of_disc (val : Valuation G.toFreeGraphMonoid ins outs) {x : N} {a : S}
    (h : val.v₁ x = G.disc a) : ∃ e, ins x = [e] ∧ val.v₀ e = a :=
  val.ins_eq_of_s (by rw [h, G.s_disc])

theorem outs_eq_nil_of_disc (val : Valuation G.toFreeGraphMonoid ins outs) {x : N} {a : S}
    (h : val.v₁ x = G.disc a) : outs x = [] := by
  have h₁ := val.t_v₁ x
  rw [h, G.t_disc] at h₁
  have h' : (outs x).map val.v₀ = [] := (FreeMonoid.ofList.injective h₁).symm
  simpa using h'

theorem not_isDup_of_isDisc (val : Valuation G.toFreeGraphMonoid ins outs) {x : N}
    (h : val.IsDisc x) : ¬ val.IsDup x := by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb⟩ := h
  obtain ⟨e₁, e₂, h₁, -⟩ := val.outs_eq_of_t_dup ha
  rw [val.outs_eq_nil_of_disc hb] at h₁
  cases h₁

end Valuation

namespace PDiagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

theorem dupCond (Γ : PDiagram G.toFreeGraphMonoid N E) : Γ.toPGraph.DupCond Γ.val.IsDup := by
  rintro x ⟨a, ha⟩
  obtain ⟨e, he, -⟩ := Γ.val.ins_eq_of_dup ha
  exact ⟨e, he⟩

end PDiagram

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

theorem dupCond (Γ : Diagram G.toFreeGraphMonoid N E) : Γ.toPGraph.DupCond Γ.val.IsDup := by
  rintro x ⟨a, ha⟩
  obtain ⟨e, he, -⟩ := Γ.val.ins_eq_of_dup ha
  exact ⟨e, he⟩

/-! ### The notions of Section 4 for a diagram -/

variable (Γ : Diagram G.toFreeGraphMonoid N E)

/-- Live nodes of a diagram (Section 4). -/
abbrev Live (x : N) : Prop := Γ.toPGraph.Live Γ.val.IsDup x

/-- Quasi-terminal nodes of a diagram, the set `Δ_Γ` (Section 4). -/
abbrev QuasiTerminal (x : N) : Prop := Γ.toPGraph.QuasiTerminal Γ.val.IsDup x

/-- `q` is the origin `e°` of `e` (Section 4). -/
abbrev IsOrigin (q e : E) : Prop := Γ.toPGraph.IsOrigin Γ.val.IsDup q e

/-- Consumers (Section 4). -/
abbrev Consumer (e : E) : Prop := Γ.toPGraph.Consumer Γ.val.IsDup e

/-- Where the origin of an edge is: the `j`-th edge of `dom(Γ)` (`dom j`), or the `j`-th output
of the node `y` (`out y j`). -/
inductive Port (L : Type u₅) where
  | dom (j : ℕ)
  | out (y : L) (j : ℕ)

/-- The origin of `e` is at the port `p`: "`e°` is the `j`-th edge in `dom(Γ)`", "`e°` is the
`j`-th output of `y`". -/
def OriginAt (e : E) : Port N → Prop
  | .dom j => ∃ q, Γ.dom[j]? = some q ∧ Γ.IsOrigin q e
  | .out y j => ∃ q, (Γ.outs y)[j]? = some q ∧ Γ.IsOrigin q e

variable {Γ} {Υ : Diagram G.toFreeGraphMonoid N' E'}

/-- The origins of corresponding consumers match: "`e°` is the `j`-th edge in `dom(Γ)` if and
only if `e'°` is the `j`-th edge in `dom(Υ)`, and `e°` is the `j`-th output of a live node `y`
if and only if `e'°` is the `j`-th output of `π(y)`". -/
def OriginsMatch (π : {x // Γ.Live x} ≃ {y // Υ.Live y}) (e : E) (e' : E') : Prop :=
  (∀ j, Γ.OriginAt e (.dom j) ↔ Υ.OriginAt e' (.dom j)) ∧
    ∀ (y : {x // Γ.Live x}) j, Γ.OriginAt e (.out y.1 j) ↔ Υ.OriginAt e' (.out (π y).1 j)

variable (Γ Υ) in
/-- The conditions of **"have the same skeleton"** for a given bijection `π` from the live
nodes of `Γ` onto those of `Υ` (Section 4): "`v(x) = w(π(x))` for all live `x` and the origins
match: if `e` is the `i`-th edge in `cod(Γ)`, or the `i`-th input of a live node `x`, and `e'`
is the `i`-th edge in `cod(Υ)`, or the `i`-th input of `π(x)`, respectively, then ...". -/
structure SkeletonIso (π : {x // Γ.Live x} ≃ {y // Υ.Live y}) : Prop where
  val_eq : ∀ x, Υ.val.v₁ (π x).1 = Γ.val.v₁ x.1
  cod_match : ∀ (i : ℕ) e e', Γ.cod[i]? = some e → Υ.cod[i]? = some e' → OriginsMatch π e e'
  ins_match : ∀ (x : {x // Γ.Live x}) (i : ℕ) e e', (Γ.ins x.1)[i]? = some e →
    (Υ.ins (π x).1)[i]? = some e' → OriginsMatch π e e'

variable (Γ Υ) in
/-- **Same skeleton** (Section 4). "We say that two anchored diagrams `(Γ, v)`, `(Υ, w)` in `G`
with the same domain and the same codomain have the same skeleton if there is a bijection `π`
from the set of the live nodes of `Γ` onto that of `Υ` such that ..." -/
def SameSkeleton : Prop :=
  Γ.domWord = Υ.domWord ∧ Γ.codWord = Υ.codWord ∧
    ∃ π : {x // Γ.Live x} ≃ {y // Υ.Live y}, SkeletonIso Γ Υ π

end Diagram

/-! ### Directed paths and splitter paths between ends -/

/-- An end of a directed path: a node, or an edge of the domain (at the start) or of the
codomain (at the end), given by its position. -/
inductive PEnd (L : Type u₅) where
  | node (x : L)
  | edge (i : ℕ)

namespace PEnd

variable {L : Type u₅} {L' : Type u₃}

/-- Mapping the nodes of an end. -/
def map (f : L → L') : PEnd L → PEnd L'
  | node x => node (f x)
  | edge i => edge i

@[simp] theorem map_node (f : L → L') (x : L) : (node x).map f = node (f x) := rfl
@[simp] theorem map_edge (f : L → L') (i : ℕ) : (edge i : PEnd L).map f = edge i := rfl

theorem map_map {L'' : Type u₄} (f : L → L') (g : L' → L'') (s : PEnd L) :
    (s.map f).map g = s.map (g ∘ f) := by
  cases s <;> rfl

end PEnd

namespace PEnd

/-- A start whose edges are not outputs of duplicates: an edge of the domain or a node whose
value is not a duplicate. -/
def RootStart {N : Type u₁} (D : N → Prop) : PEnd N → Prop
  | .node x => ¬ D x
  | .edge _ => True

end PEnd

namespace AGraph

variable {N : Type u₁} {E : Type u₂} (Γ : AGraph N E)

/-- The edges a directed path may begin with at the start `s`. -/
def startEdges : PEnd N → List E
  | .node x => Γ.outs x
  | .edge i => Γ.dom[i]?.toList

/-- The edges a directed path may end with at the end `t`. -/
def endEdges : PEnd N → List E
  | .node y => Γ.ins y
  | .edge j => Γ.cod[j]?.toList

/-- The directed path `p` begins at `s`: "with `p(0) = x`", or "begins with the `i`-th edge in
the domain". -/
def PathBegins (p : List E) : PEnd N → Prop
  | .node x => Γ.pathSrc p = some x
  | .edge i => p.head?.isSome ∧ p.head? = Γ.dom[i]?

/-- The directed path `p` ends at `t`: "with `p(1) = y`", or "ends with the `j`-th edge in the
codomain". -/
def PathEnds (p : List E) : PEnd N → Prop
  | .node y => Γ.pathTgt p = some y
  | .edge j => p.getLast?.isSome ∧ p.getLast? = Γ.cod[j]?

/-- There is a directed path from `s` to `t` (Lemma 4.3, second item). -/
def HasPath (s t : PEnd N) : Prop := ∃ p, Γ.IsPath p ∧ Γ.PathBegins p s ∧ Γ.PathEnds p t

/-- Two directed paths begin at the same point `p(0) = p'(0)` (an inner node, or the same outer
node, i.e. the same edge of the domain). -/
def SameStart (p p' : List E) : Prop :=
  (∃ x, Γ.pathSrc p = some x ∧ Γ.pathSrc p' = some x) ∨ (Γ.pathSrc p = none ∧ p.head? = p'.head?)

/-- **Splitter path** between the ends `t`, `t'` (Section 4): "a pair of directed paths `p`,
`p'` in `Γ` with `p(0) = p'(0)`", ending at `t` and at `t'`. -/
def HasSplitter (t t' : PEnd N) : Prop :=
  ∃ p p', Γ.IsPath p ∧ Γ.IsPath p' ∧ Γ.SameStart p p' ∧ Γ.PathEnds p t ∧ Γ.PathEnds p' t'

/-- There are edges at `s` and `t` joined by consecutive edges. -/
def DPath (s t : PEnd N) : Prop :=
  ∃ e ∈ Γ.startEdges s, ∃ e' ∈ Γ.endEdges t, ReflTransGen Γ.Step e e'

variable {Γ}

theorem mem_startEdges_iff (p : List E) (hp : p ≠ []) (s : PEnd N) :
    Γ.PathBegins p s ↔ p.head hp ∈ Γ.startEdges s := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hp
  cases s with
  | node x =>
    simp only [PathBegins, PGraph.pathSrc, List.head?_cons, Option.bind_some, startEdges,
      List.head_cons]
    exact (Γ.mem_outs x a).symm
  | edge i =>
    simp only [PathBegins, List.head?_cons, Option.isSome_some, true_and, startEdges,
      List.head_cons]
    cases Γ.dom[i]? <;> simp [eq_comm]

theorem mem_endEdges_iff (p : List E) (hp : p ≠ []) (t : PEnd N) :
    Γ.PathEnds p t ↔ p.getLast hp ∈ Γ.endEdges t := by
  cases t with
  | node y =>
    simp only [PathEnds, PGraph.pathTgt, List.getLast?_eq_some_getLast hp, Option.bind_some,
      endEdges]
    exact (Γ.mem_ins y _).symm
  | edge j =>
    simp only [PathEnds, List.getLast?_eq_some_getLast hp, Option.isSome_some, true_and,
      endEdges]
    cases Γ.cod[j]? <;> simp [eq_comm]

/-- Directed paths as lists and chains of consecutive edges describe the same connections. -/
theorem hasPath_iff_dPath (s t : PEnd N) : Γ.HasPath s t ↔ Γ.DPath s t := by
  constructor
  · rintro ⟨p, hp, hs, ht⟩
    refine ⟨p.head hp.1, (mem_startEdges_iff p hp.1 s).1 hs, p.getLast hp.1,
      (mem_endEdges_iff p hp.1 t).1 ht, ?_⟩
    refine (PGraph.exists_isPath_iff _ _).1 ⟨p, hp, ?_, ?_⟩
    · exact List.head?_eq_some_head hp.1
    · exact List.getLast?_eq_some_getLast hp.1
  · rintro ⟨e, he, e', he', h⟩
    obtain ⟨p, hp, h₁, h₂⟩ := (PGraph.exists_isPath_iff _ _).2 h
    have h₁' : p.head hp.1 = e := by
      rw [List.head?_eq_some_head hp.1] at h₁
      exact Option.some.inj h₁
    have h₂' : p.getLast hp.1 = e' := by
      rw [List.getLast?_eq_some_getLast hp.1] at h₂
      exact Option.some.inj h₂
    exact ⟨p, hp, (mem_startEdges_iff p hp.1 s).2 (h₁' ▸ he),
      (mem_endEdges_iff p hp.1 t).2 (h₂' ▸ he')⟩

/-! ### Paths through origins of consumers -/

variable (Γ) (D : N → Prop)

/-- The end `t` has a consumer whose origin is at the start `s`. -/
def Feeds (s t : PEnd N) : Prop :=
  ∃ e ∈ Γ.endEdges t, ∃ q ∈ Γ.startEdges s, Γ.IsOrigin D q e

/-- Chains of consumers and live nodes: the description of directed paths through the
skeleton (proof of Lemma 4.3, second item). -/
inductive SPath (s : PEnd N) : PEnd N → Prop
  | feeds {t : PEnd N} : Γ.Feeds D s t → SPath s t
  | trans {y : N} {t : PEnd N} : SPath s (.node y) → Γ.Live D y → Γ.Feeds D (.node y) t → SPath s t

/-- An end whose edges are consumers: an edge of the codomain or a live node. -/
def ConsumerEnd : PEnd N → Prop
  | .node y => Γ.Live D y
  | .edge _ => True

variable {Γ D}

theorem isRoot_of_rootStart {s : PEnd N} (hs : PEnd.RootStart D s) {q : E} (hq : q ∈ Γ.startEdges s) :
    Γ.IsRoot D q := by
  cases s with
  | node x => exact PGraph.isRoot_of_mem_outs hq hs
  | edge i =>
    have : Γ.dom[i]? = some q := by simpa [startEdges] using hq
    exact PGraph.isRoot_of_src_none ((Γ.mem_dom q).1 (List.mem_of_getElem? this))

theorem ConsumerEnd.consumer {t : PEnd N} (ht : Γ.ConsumerEnd D t) {e : E}
    (he : e ∈ Γ.endEdges t) : Γ.Consumer D e := by
  cases t with
  | node y => exact Or.inr ⟨y, (Γ.mem_ins y e).1 he, ht⟩
  | edge j =>
    have : Γ.cod[j]? = some e := by simpa [endEdges] using he
    exact Or.inl ((Γ.mem_cod e).1 (List.mem_of_getElem? this))

theorem SPath.dPath {s t : PEnd N} (h : Γ.SPath D s t) : Γ.DPath s t := by
  induction h with
  | feeds h =>
    obtain ⟨e, he, q, hq, hqe, -⟩ := h
    exact ⟨q, hq, e, he, PGraph.reflTransGen_step_of_dup hqe⟩
  | trans _ _ h ih =>
    obtain ⟨e₀, he₀, e₁, he₁, h₀₁⟩ := ih
    obtain ⟨e, he, q, hq, hqe, -⟩ := h
    exact ⟨e₀, he₀, e, he,
      h₀₁.trans (ReflTransGen.head (Γ.step_of_mem he₁ hq) (PGraph.reflTransGen_step_of_dup hqe))⟩

/-- The key step: following a chain of consecutive edges from a start, the origin of each edge
that reaches the codomain is at the start or at an output of a live node reached by a chain of
consumers. -/
theorem sPath_aux {s : PEnd N} (hs : PEnd.RootStart D s) {e₀ e : E} (he₀ : e₀ ∈ Γ.startEdges s)
    (h : ReflTransGen Γ.Step e₀ e) (hc : Γ.ReachCod e) :
    (∃ q ∈ Γ.startEdges s, Γ.IsOrigin D q e) ∨
      ∃ z, Γ.Live D z ∧ (∃ q ∈ Γ.outs z, Γ.IsOrigin D q e) ∧ Γ.SPath D s (.node z) := by
  induction h with
  | refl => exact Or.inl ⟨e₀, he₀, ReflTransGen.refl, isRoot_of_rootStart hs he₀⟩
  | @tail e₁ e h₁ hst ih =>
    obtain ⟨z, hz, hz'⟩ := hst
    have ih := ih (hc.of_step ⟨z, hz, hz'⟩)
    by_cases hDz : D z
    · have hd : Γ.DupStep D e₁ e := ⟨z, hDz, hz, hz'⟩
      rcases ih with ⟨q, hq, hqe, hr⟩ | ⟨z', hz'l, ⟨q, hq, hqe, hr⟩, hsp⟩
      · exact Or.inl ⟨q, hq, hqe.tail hd, hr⟩
      · exact Or.inr ⟨z', hz'l, ⟨q, hq, hqe.tail hd, hr⟩, hsp⟩
    · have hlive : Γ.Live D z := ⟨hDz, e, (Γ.mem_outs z e).2 hz', hc⟩
      have hin : e₁ ∈ Γ.endEdges (.node z) := (Γ.mem_ins z e₁).2 hz
      refine Or.inr ⟨z, hlive, ⟨e, (Γ.mem_outs z e).2 hz', ReflTransGen.refl,
        PGraph.isRoot_of_mem_outs ((Γ.mem_outs z e).2 hz') hDz⟩, ?_⟩
      rcases ih with ⟨q, hq, hqe⟩ | ⟨z', hz'l, ⟨q, hq, hqe⟩, hsp⟩
      · exact .feeds ⟨e₁, hin, q, hq, hqe⟩
      · exact .trans hsp hz'l ⟨e₁, hin, q, hq, hqe⟩

/-- **Directed paths through the skeleton.** Between a start that is an edge of the domain or a
node whose value is not a duplicate and an end that is an edge of the codomain or a live node,
there is a directed path iff there is a chain of consumers, each with its origin at the
previous live node (proof of Lemma 4.3, second item). -/
theorem dPath_iff_sPath {s t : PEnd N} (hs : PEnd.RootStart D s) (ht : Γ.ConsumerEnd D t) :
    Γ.DPath s t ↔ Γ.SPath D s t := by
  refine ⟨fun ⟨e₀, he₀, e, he, h⟩ => ?_, SPath.dPath⟩
  rcases sPath_aux hs he₀ h (ht.consumer he).reachCod with ⟨q, hq, hqe⟩ | ⟨z, hz, ⟨q, hq, hqe⟩, hsp⟩
  · exact .feeds ⟨e, he, q, hq, hqe⟩
  · exact .trans hsp hz ⟨e, he, q, hq, hqe⟩

theorem DPath.reachCod {s t : PEnd N} (h : Γ.DPath s t) (ht : Γ.ConsumerEnd D t) :
    ∃ e ∈ Γ.startEdges s, Γ.ReachCod e := by
  obtain ⟨e, he, e', he', h⟩ := h
  exact ⟨e, he, (ht.consumer he').reachCod.of_reflTransGen h⟩

theorem _root_.FreeMarkov.exists_getElem?_of_mem {l : List E} {e : E} (h : e ∈ l) : ∃ i : ℕ, l[i]? = some e := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, List.getElem?_eq_getElem hi⟩

/-- **Splitter paths through the skeleton** (proof of Lemma 4.3, third item): between two ends
that are live nodes or edges of the codomain there is a splitter path iff both are reached by
directed paths from a common start that is a live node or an edge of the domain. -/
theorem hasSplitter_iff [Finite E] (hD : Γ.DupCond D) {t t' : PEnd N} (ht : Γ.ConsumerEnd D t) :
    Γ.HasSplitter t t' ↔ ∃ s : PEnd N, (∀ x, s = .node x → Γ.Live D x) ∧ Γ.DPath s t ∧ Γ.DPath s t' := by
  constructor
  · rintro ⟨p, p', hp, hp', hss, hpt, hpt'⟩
    have hpt₁ := (mem_endEdges_iff p hp.1 t).1 hpt
    have hpt₁' := (mem_endEdges_iff p' hp'.1 t').1 hpt'
    have hr : ReflTransGen Γ.Step (p.head hp.1) (p.getLast hp.1) :=
      (PGraph.exists_isPath_iff _ _).1 ⟨p, hp, List.head?_eq_some_head _, List.getLast?_eq_some_getLast _⟩
    have hr' : ReflTransGen Γ.Step (p'.head hp'.1) (p'.getLast hp'.1) :=
      (PGraph.exists_isPath_iff _ _).1 ⟨p', hp', List.head?_eq_some_head _, List.getLast?_eq_some_getLast _⟩
    have hc := (ht.consumer hpt₁).reachCod.of_reflTransGen hr
    -- the common first point
    have key : ∀ f f' : E, ReflTransGen Γ.Step f (p.getLast hp.1) →
        ReflTransGen Γ.Step f' (p'.getLast hp'.1) → (∀ x, Γ.src f = some x → Γ.src f' = some x) →
        (Γ.src f = none → f = f') →
        ∃ s : PEnd N, (∀ x, s = .node x → Γ.Live D x) ∧ Γ.DPath s t ∧ Γ.DPath s t' := by
      intro f f' hf hf' hsrc hnone
      cases hfs : Γ.src f with
      | none =>
        have := hnone hfs
        subst this
        obtain ⟨i, hi⟩ := exists_getElem?_of_mem ((Γ.mem_dom f).2 hfs)
        refine ⟨.edge i, (fun _ h => by cases h), ⟨f, ?_, _, hpt₁, hf⟩, ⟨f, ?_, _, hpt₁', hf'⟩⟩ <;>
          simp [startEdges, hi]
      | some x =>
        have hf'x := hsrc x hfs
        have hfo : f ∈ Γ.outs x := (Γ.mem_outs x f).2 hfs
        have hf'o : f' ∈ Γ.outs x := (Γ.mem_outs x f').2 hf'x
        have hcf : Γ.ReachCod f := (ht.consumer hpt₁).reachCod.of_reflTransGen hf
        by_cases hDx : D x
        · obtain ⟨g, hg⟩ := hD x hDx
          have hgx : Γ.tgt g = some x := (Γ.mem_ins x g).1 (by rw [hg]; exact List.mem_singleton_self _)
          obtain ⟨q, hqg, hq⟩ := PGraph.exists_isOrigin hD g
          have hqf : ReflTransGen Γ.Step q f :=
            (PGraph.reflTransGen_step_of_dup hqg).tail ⟨x, hgx, hfs⟩
          have hqf' : ReflTransGen Γ.Step q f' :=
            (PGraph.reflTransGen_step_of_dup hqg).tail ⟨x, hgx, hf'x⟩
          cases hqs : Γ.src q with
          | none =>
            obtain ⟨i, hi⟩ := exists_getElem?_of_mem ((Γ.mem_dom q).2 hqs)
            refine ⟨.edge i, (fun _ h => by cases h), ⟨q, ?_, _, hpt₁, hqf.trans hf⟩,
              ⟨q, ?_, _, hpt₁', hqf'.trans hf'⟩⟩ <;> simp [startEdges, hi]
          | some z =>
            have hqo : q ∈ Γ.outs z := (Γ.mem_outs z q).2 hqs
            have hlive : Γ.Live D z := ⟨hq z hqs, q, hqo, hcf.of_reflTransGen hqf⟩
            refine ⟨.node z, (fun y h => by cases h; exact hlive), ⟨q, hqo, _, hpt₁, hqf.trans hf⟩,
              ⟨q, hqo, _, hpt₁', hqf'.trans hf'⟩⟩
        · have hlive : Γ.Live D x := ⟨hDx, f, hfo, hcf⟩
          exact ⟨.node x, (fun y h => by cases h; exact hlive), ⟨f, hfo, _, hpt₁, hf⟩,
            ⟨f', hf'o, _, hpt₁', hf'⟩⟩
    rcases hss with ⟨x, hx, hx'⟩ | ⟨hn, hh⟩
    · refine key _ _ hr hr' (fun y hy => ?_) (fun hy => ?_)
      · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hp.1
        obtain ⟨a', l', rfl⟩ := List.exists_cons_of_ne_nil hp'.1
        simp only [PGraph.pathSrc, List.head?_cons, Option.bind_some] at hx hx'
        simp only [List.head_cons] at hy ⊢
        rw [hx'] ; rw [hx] at hy; exact hy
      · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hp.1
        simp only [PGraph.pathSrc, List.head?_cons, Option.bind_some] at hx
        simp only [List.head_cons] at hy
        rw [hx] at hy
        cases hy
    · refine key _ _ hr hr' (fun y hy => ?_) (fun _ => ?_)
      · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hp.1
        simp only [PGraph.pathSrc, List.head?_cons, Option.bind_some] at hn
        simp only [List.head_cons] at hy
        rw [hn] at hy
        cases hy
      · rw [List.head?_eq_some_head hp.1, List.head?_eq_some_head hp'.1] at hh
        exact Option.some.inj hh
  · rintro ⟨s, hs, ⟨e, he, c, hc, h⟩, ⟨e', he', c', hc', h'⟩⟩
    obtain ⟨p, hp, h₁, h₂⟩ := (PGraph.exists_isPath_iff _ _).2 h
    obtain ⟨p', hp', h₁', h₂'⟩ := (PGraph.exists_isPath_iff _ _).2 h'
    have hph : p.head hp.1 = e := Option.some.inj ((List.head?_eq_some_head hp.1).symm.trans h₁)
    have hph' : p'.head hp'.1 = e' := Option.some.inj ((List.head?_eq_some_head hp'.1).symm.trans h₁')
    have hpl : p.getLast hp.1 = c :=
      Option.some.inj ((List.getLast?_eq_some_getLast hp.1).symm.trans h₂)
    have hpl' : p'.getLast hp'.1 = c' :=
      Option.some.inj ((List.getLast?_eq_some_getLast hp'.1).symm.trans h₂')
    refine ⟨p, p', hp, hp', ?_, (mem_endEdges_iff p hp.1 t).2 (hpl ▸ hc),
      (mem_endEdges_iff p' hp'.1 t').2 (hpl' ▸ hc')⟩
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hp.1
    obtain ⟨a', l', rfl⟩ := List.exists_cons_of_ne_nil hp'.1
    simp only [List.head_cons] at hph hph'
    subst hph hph'
    cases s with
    | node x =>
      refine Or.inl ⟨x, ?_, ?_⟩ <;> simp only [PGraph.pathSrc, List.head?_cons, Option.bind_some]
      · exact (Γ.mem_outs x _).1 he
      · exact (Γ.mem_outs x _).1 he'
    | edge i =>
      simp only [startEdges] at he he'
      have h₁ : Γ.dom[i]? = some a := by simpa using he
      have h₂ : Γ.dom[i]? = some a' := by simpa using he'
      rw [h₁, Option.some.injEq] at h₂
      subst h₂
      refine Or.inr ⟨?_, rfl⟩
      simp only [PGraph.pathSrc, List.head?_cons, Option.bind_some]
      exact (Γ.mem_dom _).1 (List.mem_of_getElem? h₁)

end AGraph

end FreeMarkov
