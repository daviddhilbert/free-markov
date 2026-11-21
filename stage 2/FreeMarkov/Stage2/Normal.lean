/-
Free Markov categories, Stage 2: normal subgraphs (Definition 3.1), `Γ'^♭`, the two
observations after Definition 3.1, Lemma 3.2 and `Γ'^♯`.

A subgraph is given by a set of nodes and a set of edges (`Subgraph`), and its
polarized graph is Stage 1's `Γ.sub P Q`.  For the surgery we use the layers
`Γ[L, M]` provided by Lemma 3.2 in the form of a structure `ValidLayer Γ A` (levels
`L ⊆ M` with `A ⊆ Γ[L, M]` and `Γ[L, M]^♭ = A^♭`), together with the elementary facts
about the edges cut by `L` and `M` that the "more precisely" paragraph of Section 3
uses (`cut(L) = dom(Γ') ⊎ R`, `cut(M) = cod(Γ') ⊎ R`).
-/
module

public import FreeMarkov.Stage2.Paths

@[expose] public section

universe u₁ u₂

namespace FreeMarkov

open Relation

/-- A **subgraph** `Γ'` of a graph with nodes `N` and edges `E` (Section 2): "a
subset `Γ'₀ ⊆ Γ₀` and a subset `Γ'₁ ⊆ Γ₁`".  Its polarized graph is
`Γ.sub A.node A.edge`. -/
@[ext] structure Subgraph (N : Type u₁) (E : Type u₂) where
  /-- The nodes `Γ'₀`. -/
  node : N → Prop
  /-- The edges `Γ'₁`. -/
  edge : E → Prop

namespace Subgraph

variable {N : Type u₁} {E : Type u₂}

/-- Inclusion of subgraphs, `Γ' ⊆ Γ''`. -/
instance : LE (Subgraph N E) :=
  ⟨fun A B => (∀ x, A.node x → B.node x) ∧ ∀ e, A.edge e → B.edge e⟩

theorem le_def {A B : Subgraph N E} :
    A ≤ B ↔ (∀ x, A.node x → B.node x) ∧ ∀ e, A.edge e → B.edge e := Iff.rfl

/-- The whole graph as a subgraph. -/
def univ (N : Type u₁) (E : Type u₂) : Subgraph N E := ⟨fun _ => True, fun _ => True⟩

/-- The empty subgraph. -/
def empty (N : Type u₁) (E : Type u₂) : Subgraph N E := ⟨fun _ => False, fun _ => False⟩

end Subgraph

namespace PGraph

variable {N : Type u₁} {E : Type u₂} (Γ : PGraph N E)

/-- The edge `e` is loose in a subgraph with node set `P` (both ends outside `P`); for
`e` in the subgraph this is `(Γ.sub P Q).IsLoose e` (`sub_isLoose_iff`). -/
def LooseIn (P : N → Prop) (e : E) : Prop :=
  (∀ x, Γ.src e = some x → ¬ P x) ∧ (∀ y, Γ.tgt e = some y → ¬ P y)

theorem sub_isLoose_iff_looseIn {P : N → Prop} {Q : E → Prop} (e : {e // Q e}) :
    (Γ.sub P Q).IsLoose e ↔ Γ.LooseIn P e.1 := sub_isLoose_iff e

/-- The subgraph `Γ'^♭`: "the subgraph obtained from `Γ'` by deleting its loose
edges". -/
def flat (A : Subgraph N E) : Subgraph N E := ⟨A.node, fun e => A.edge e ∧ ¬ Γ.LooseIn A.node e⟩

/-- The layer `Γ[L, M]` as a subgraph. -/
def layerSub (L M : Set N) : Subgraph N E := ⟨Γ.LayerNode L M, Γ.LayerEdge L M⟩

/-- The second condition of Definition 3.1: "all the edges at `x` in `Γ` are included
in `Γ'`". -/
def EdgeAt (A : Subgraph N E) : Prop :=
  ∀ x, A.node x → ∀ e, Γ.src e = some x ∨ Γ.tgt e = some x → A.edge e

/-- **Definition 3.1.** A subgraph `Γ' ⊆ Γ` is **normal** if
* no directed path in `Γ` contains two distinct edges in `Γ'` if one of them is loose in
  `Γ'`,
* the degree of every `x ∈ Γ'₀` in `Γ'` is the same as in `Γ`, in other words, all the
  edges at `x` in `Γ` are included in `Γ'`,
* every directed path `p` in `Γ` with `p(0), p(1) ∈ Γ'₀` belongs to `Γ'` (its edges and
  the nodes it passes through are in `Γ'`). -/
structure IsNormal (A : Subgraph N E) : Prop where
  path_loose : ∀ p, Γ.IsPath p → ∀ e ∈ p, ∀ e' ∈ p, e ≠ e' → ∀ (he : A.edge e), A.edge e' →
    ¬ (Γ.sub A.node A.edge).IsLoose ⟨e, he⟩
  edge_at : Γ.EdgeAt A
  path_mem : ∀ p, Γ.IsPath p → ∀ x y, Γ.pathSrc p = some x → Γ.pathTgt p = some y →
    A.node x → A.node y → ∀ e ∈ p,
      A.edge e ∧ (∀ z, Γ.src e = some z → A.node z) ∧ (∀ z, Γ.tgt e = some z → A.node z)

variable {Γ}

/-- *After Definition 3.1.* "Observe that if two subgraphs `Γ'`, `Γ''` have the same set
of nodes and both satisfy the second condition above then `Γ'^♭`, `Γ''^♭` must be
equal." -/
theorem flat_eq_of_edgeAt {A B : Subgraph N E} (hnode : A.node = B.node) (hA : Γ.EdgeAt A)
    (hB : Γ.EdgeAt B) : Γ.flat A = Γ.flat B := by
  have key : ∀ {A B : Subgraph N E}, A.node = B.node → Γ.EdgeAt B → ∀ e,
      (A.edge e ∧ ¬ Γ.LooseIn A.node e) → (B.edge e ∧ ¬ Γ.LooseIn B.node e) := by
    intro A B hnode hB e ⟨_, hl⟩
    rw [hnode] at hl
    refine ⟨?_, hl⟩
    unfold LooseIn at hl
    simp only [not_and_or, not_forall, not_not, exists_prop] at hl
    rcases hl with ⟨x, hx, hPx⟩ | ⟨y, hy, hPy⟩
    · exact hB x hPx e (Or.inl hx)
    · exact hB y hPy e (Or.inr hy)
  refine Subgraph.ext hnode ?_
  funext e
  exact propext ⟨key hnode hB e, key hnode.symm hA e⟩

/-- *After Definition 3.1.* "in a normal subgraph `Γ'` of `Γ`, if `x ∈ Γ'₀` is initial in
`Γ'` then it is initial in `Γ`". -/
theorem IsNormal.isInitial {A : Subgraph N E} (h : Γ.IsNormal A) (x : {x // A.node x})
    (hx : (Γ.sub A.node A.edge).IsInitial x) : Γ.IsInitial x.1 := by
  unfold IsInitial at hx ⊢
  rw [← sub_ins_map_val x (fun e he => h.edge_at x.1 x.2 e (Or.inr ((Γ.mem_ins _ _).1 he))), hx]
  rfl

/-- *After Definition 3.1.* "... similarly if it is terminal". -/
theorem IsNormal.isTerminal {A : Subgraph N E} (h : Γ.IsNormal A) (x : {x // A.node x})
    (hx : (Γ.sub A.node A.edge).IsTerminal x) : Γ.IsTerminal x.1 := by
  unfold IsTerminal at hx ⊢
  rw [← sub_outs_map_val x (fun e he => h.edge_at x.1 x.2 e (Or.inl ((Γ.mem_outs _ _).1 he))),
    hx]
  rfl

/-- The first condition of Definition 3.1 in terms of `Reach`. -/
theorem IsNormal.not_reach {A : Subgraph N E} (h : Γ.IsNormal A) {e e' : E} (he : A.edge e)
    (he' : A.edge e') (hl : Γ.LooseIn A.node e) : ¬ Γ.Reach e e' ∧ ¬ Γ.Reach e' e := by
  have hl' : (Γ.sub A.node A.edge).IsLoose ⟨e, he⟩ := (Γ.sub_isLoose_iff_looseIn _).2 hl
  constructor
  · intro hr
    obtain ⟨p, hp, h₁, h₂⟩ := Γ.exists_path_of_reach hr
    exact h.path_loose p hp e h₁ e' h₂ hr.ne he he' hl'
  · intro hr
    obtain ⟨p, hp, h₁, h₂⟩ := Γ.exists_path_of_reach hr
    exact h.path_loose p hp e h₂ e' h₁ hr.ne.symm he he' hl'

/-- The third condition of Definition 3.1 in terms of nodes: the nodes of a normal
subgraph form a convex set of `Γ̇`. -/
theorem IsNormal.convex {A : Subgraph N E} (h : Γ.IsNormal A) {x y z : N} (hx : A.node x)
    (hy : A.node y) (hxz : Γ.Le x z) (hzy : Γ.Le z y) : A.node z := by
  rcases hxz with hxz | rfl
  · rcases hzy with hzy | rfl
    · obtain ⟨p, hp, hp₁, hp₂, e, he, hez⟩ := Γ.exists_path_through hxz hzy
      exact (h.path_mem p hp x y hp₁ hp₂ hx hy e he).2.1 z hez
    · exact hy
  · exact hx

theorem le_of_reflTransGen {x y : N} (h : ReflTransGen Γ.Adj x y) : Γ.Le x y := by
  rcases reflTransGen_iff_eq_or_transGen.1 h with rfl | h
  · exact le_refl' _
  · exact Or.inl h

/-! ### Lemma 3.2 -/

theorem layerEdge_of_src {L M : Set N} (hL : Γ.IsLevel L) {x : N} (hx : Γ.LayerNode L M x)
    {e : E} (he : Γ.src e = some x) : Γ.LayerEdge L M e :=
  Γ.layerEdge_of_mem_outs hL hx ((Γ.mem_outs x e).2 he)

theorem layerEdge_of_tgt {L M : Set N} (hM : Γ.IsLevel M) {x : N} (hx : Γ.LayerNode L M x)
    {e : E} (he : Γ.tgt e = some x) : Γ.LayerEdge L M e :=
  Γ.layerEdge_of_mem_ins hM hx ((Γ.mem_ins x e).2 he)

theorem edgeAt_layerSub {L M : Set N} (hL : Γ.IsLevel L) (hM : Γ.IsLevel M) :
    Γ.EdgeAt (Γ.layerSub L M) := by
  rintro x hx e (he | he)
  · exact Γ.layerEdge_of_src hL hx he
  · exact Γ.layerEdge_of_tgt hM hx he

theorem not_looseIn_of_src {P : N → Prop} {e : E} {x : N} (he : Γ.src e = some x) (hx : P x) :
    ¬ Γ.LooseIn P e := fun hl => hl.1 x he hx

theorem not_looseIn_of_tgt {P : N → Prop} {e : E} {x : N} (he : Γ.tgt e = some x) (hx : P x) :
    ¬ Γ.LooseIn P e := fun hl => hl.2 x he hx

/-- **Lemma 3.2, "if".** A subgraph `Γ'` with `Γ' ⊆ Γ[L, M]` and `Γ[L, M]^♭ = Γ'^♭` for
levels `L ⊆ M` is normal. -/
theorem isNormal_of_layer {L M : Set N} (hL : Γ.IsLevel L) (hM : Γ.IsLevel M)
    {A : Subgraph N E} (hle : A ≤ Γ.layerSub L M)
    (hflat : Γ.flat (Γ.layerSub L M) = Γ.flat A) : Γ.IsNormal A := by
  have hnode : ∀ x, A.node x ↔ Γ.LayerNode L M x := fun x => by
    have := congrArg (fun B : Subgraph N E => B.node x) hflat
    exact (Eq.to_iff this).symm
  have hedge : ∀ e, (Γ.LayerEdge L M e ∧ ¬ Γ.LooseIn (Γ.LayerNode L M) e) ↔
      (A.edge e ∧ ¬ Γ.LooseIn A.node e) := fun e => by
    have := congrArg (fun B : Subgraph N E => B.edge e) hflat
    exact Eq.to_iff this
  have hedgeAt : Γ.EdgeAt A := by
    intro x hx e hxe
    have hx' := (hnode x).1 hx
    have hle' : Γ.LayerEdge L M e := Γ.edgeAt_layerSub hL hM x hx' e hxe
    refine ((hedge e).1 ⟨hle', ?_⟩).1
    rcases hxe with hxe | hxe
    · exact Γ.not_looseIn_of_src hxe hx'
    · exact Γ.not_looseIn_of_tgt hxe hx'
  refine ⟨?_, hedgeAt, ?_⟩
  · intro p hp e he e' he' hne hA hA' hloose
    have hl : Γ.LooseIn A.node e := (Γ.sub_isLoose_iff_looseIn ⟨e, hA⟩).1 hloose
    have hlay := hle.2 e hA
    have hlay' := hle.2 e' hA'
    rcases Γ.reach_of_mem_path hp he he' hne with ⟨x, y, hx, hy, hxy⟩ | ⟨x, y, hx, hy, hxy⟩
    · have hxL : x ∉ L := hlay.2 x hx
      have hxM : x ∉ M := fun hxM => hl.2 x hx ((hnode x).2 ⟨hxM, hxL⟩)
      exact hxM (hM.mem_of_le hxy (hlay'.1 y hy))
    · have hyM : y ∈ M := hlay.1 y hy
      have hyL : y ∈ L := by
        by_contra hyL
        exact hl.1 y hy ((hnode y).2 ⟨hyM, hyL⟩)
      exact hlay'.2 x hx (hL.mem_of_le hxy hyL)
  · intro p hp x y hpx hpy hx hy e he
    obtain ⟨⟨z, hz, hxz⟩, ⟨z', hz', hz'y⟩⟩ := Γ.src_tgt_of_mem_path hp hpx hpy he
    have hzz' : Γ.Lt z z' := Γ.lt_of_edge hz hz'
    have hx' := (hnode x).1 hx
    have hy' := (hnode y).1 hy
    have hzN : A.node z :=
      (hnode z).2 ⟨hM.mem_of_le (hzz'.le.trans hz'y) hy'.1, hL.not_mem_of_le hxz hx'.2⟩
    have hz'N : A.node z' :=
      (hnode z').2 ⟨hM.mem_of_le hz'y hy'.1, hL.not_mem_of_le (hxz.trans hzz'.le) hx'.2⟩
    refine ⟨hedgeAt z hzN e (Or.inl hz), ?_, ?_⟩
    · intro w hw
      rw [hz] at hw
      cases hw
      exact hzN
    · intro w hw
      rw [hz'] at hw
      cases hw
      exact hz'N

variable (Γ)

/-- The lower level of `Γ'^♯` (proof of Lemma 3.2): the nodes `x` such that either
`x ∉ Γ'₀` and `x < y` for some `y ∈ Γ'₀`, or `x ≤ e(0) ∈ Γ̇` for some loose edge `e` in
`Γ'`. -/
def sharpL (A : Subgraph N E) : Set N :=
  {x | (¬ A.node x ∧ ∃ y, A.node y ∧ Γ.Lt x y) ∨
    ∃ e z, A.edge e ∧ Γ.LooseIn A.node e ∧ Γ.src e = some z ∧ Γ.Le x z}

/-- The upper level of `Γ'^♯` (proof of Lemma 3.2): the nodes `x` such that `x ≤ y` for
some `y ∈ Γ'₀` or `x ≤ e(0) ∈ Γ̇` for some loose edge `e` in `Γ'`. -/
def sharpM (A : Subgraph N E) : Set N :=
  {x | (∃ y, A.node y ∧ Γ.Le x y) ∨
    ∃ e z, A.edge e ∧ Γ.LooseIn A.node e ∧ Γ.src e = some z ∧ Γ.Le x z}

/-- `Γ'^♯`: "the layer `Γ[L, M]` constructed from `Γ'` in the latter half of the proof"
of Lemma 3.2. -/
def sharp (A : Subgraph N E) : Subgraph N E := Γ.layerSub (Γ.sharpL A) (Γ.sharpM A)

variable {Γ}

section Sharp

variable {A : Subgraph N E} (h : Γ.IsNormal A)
include h

theorem IsNormal.isLevel_sharpL : Γ.IsLevel (Γ.sharpL A) := by
  rintro x' x hx'x (⟨hx, y, hy, hxy⟩ | ⟨e, z, he, hl, hz, hxz⟩)
  · refine Or.inl ⟨fun hx' => hx (h.convex hx' hy hx'x.le hxy.le), y, hy, hx'x.trans hxy⟩
  · exact Or.inr ⟨e, z, he, hl, hz, hx'x.le.trans hxz⟩

omit h in
theorem isLevel_sharpM : Γ.IsLevel (Γ.sharpM A) := by
  rintro x' x hx'x (⟨y, hy, hxy⟩ | ⟨e, z, he, hl, hz, hxz⟩)
  · exact Or.inl ⟨y, hy, hx'x.le.trans hxy⟩
  · exact Or.inr ⟨e, z, he, hl, hz, hx'x.le.trans hxz⟩

omit h in
theorem sharpL_subset_sharpM : Γ.sharpL A ⊆ Γ.sharpM A := by
  rintro x (⟨-, y, hy, hxy⟩ | hx)
  · exact Or.inl ⟨y, hy, hxy.le⟩
  · exact Or.inr hx

/-- "So `L ∩ Γ'₀ = ∅`." -/
theorem IsNormal.not_node_of_mem_sharpL {x : N} (hx : x ∈ Γ.sharpL A) : ¬ A.node x := by
  rcases hx with ⟨hx, -⟩ | ⟨e, z, he, hl, hz, hxz⟩
  · exact hx
  · intro hxN
    have hzN : ¬ A.node z := hl.1 z hz
    rcases hxz with hxz | rfl
    · obtain ⟨c, ⟨e₀, he₀x, he₀c⟩, hcz⟩ := TransGen.head'_iff.1 hxz
      have he₀ : A.edge e₀ := h.edge_at x hxN e₀ (Or.inl he₀x)
      exact (h.not_reach he he₀ hl).2 ⟨c, z, he₀c, hz, le_of_reflTransGen hcz⟩
    · exact hzN hxN

/-- "We have `M ∖ L = Γ'₀`." -/
theorem IsNormal.node_iff_sharp (x : N) :
    A.node x ↔ Γ.LayerNode (Γ.sharpL A) (Γ.sharpM A) x := by
  constructor
  · intro hx
    exact ⟨Or.inl ⟨x, hx, le_refl' x⟩, fun hL => h.not_node_of_mem_sharpL hL hx⟩
  · rintro ⟨⟨y, hy, hxy | rfl⟩ | hM, hL⟩
    · by_contra hx
      exact hL (Or.inl ⟨hx, y, hy, hxy⟩)
    · exact hy
    · exact (hL (Or.inr hM)).elim

theorem IsNormal.layerEdge_sharp {e : E} (he : A.edge e) :
    Γ.LayerEdge (Γ.sharpL A) (Γ.sharpM A) e := by
  constructor
  · intro x hx
    by_cases hxN : A.node x
    · exact Or.inl ⟨x, hxN, le_refl' x⟩
    · by_cases hy : ∃ y, Γ.tgt e = some y ∧ A.node y
      · obtain ⟨y, hy, hyN⟩ := hy
        exact sharpL_subset_sharpM (Or.inl ⟨hxN, y, hyN, Γ.lt_of_edge hx hy⟩)
      · refine Or.inr ⟨e, x, he, ⟨?_, ?_⟩, hx, le_refl' x⟩
        · intro x' hx'
          rw [hx] at hx'
          cases hx'
          exact hxN
        · intro y hy' hyN
          exact hy ⟨y, hy', hyN⟩
  · intro y hy hyL
    by_cases hyN : A.node y
    · exact h.not_node_of_mem_sharpL hyL hyN
    · rcases hyL with ⟨-, y', hy'N, hyy'⟩ | ⟨e₂, z, he₂, hl₂, hz, hyz⟩
      · obtain ⟨c, hyc, ⟨e₁, he₁c, he₁y'⟩⟩ := TransGen.tail'_iff.1 hyy'
        have he₁ : A.edge e₁ := h.edge_at y' hy'N e₁ (Or.inr he₁y')
        have hr : Γ.Reach e e₁ := ⟨y, c, hy, he₁c, le_of_reflTransGen hyc⟩
        by_cases hl : Γ.LooseIn A.node e
        · exact (h.not_reach he he₁ hl).1 hr
        · unfold LooseIn at hl
          simp only [not_and_or, not_forall, not_not, exists_prop] at hl
          rcases hl with ⟨x, hx, hxN⟩ | ⟨y'', hy'', hy''N⟩
          · exact hyN (h.convex hxN hy'N (Γ.lt_of_edge hx hy).le
              ((le_of_reflTransGen hyc).trans (Γ.lt_of_edge he₁c he₁y').le))
          · rw [hy] at hy''
            cases hy''
            exact hyN hy''N
      · exact (h.not_reach he₂ he hl₂).2 ⟨y, z, hy, hz, hyz⟩

theorem IsNormal.le_sharp : A ≤ Γ.sharp A :=
  ⟨fun x hx => (h.node_iff_sharp x).1 hx, fun _ he => h.layerEdge_sharp he⟩

/-- "Since `Γ[L, M]^♭` is normal too, we have `Γ[L, M]^♭ = Γ'^♭`." -/
theorem IsNormal.flat_sharp : Γ.flat (Γ.sharp A) = Γ.flat A :=
  flat_eq_of_edgeAt (funext fun x => propext (h.node_iff_sharp x).symm)
    (Γ.edgeAt_layerSub h.isLevel_sharpL isLevel_sharpM) h.edge_at

end Sharp

/-- **Lemma 3.2.** "A subgraph `Γ' ⊆ Γ` is normal if and only if there is a layer
`Γ[L, M]` in `Γ` such that `Γ' ⊆ Γ[L, M]` and `Γ[L, M]^♭ = Γ'^♭`." -/
theorem isNormal_iff (A : Subgraph N E) :
    Γ.IsNormal A ↔ ∃ L M : Set N, Γ.IsLevel L ∧ Γ.IsLevel M ∧ L ⊆ M ∧
      A ≤ Γ.layerSub L M ∧ Γ.flat (Γ.layerSub L M) = Γ.flat A := by
  constructor
  · intro h
    exact ⟨_, _, h.isLevel_sharpL, isLevel_sharpM, sharpL_subset_sharpM, h.le_sharp, h.flat_sharp⟩
  · rintro ⟨L, M, hL, hM, -, hle, hflat⟩
    exact isNormal_of_layer hL hM hle hflat

/-! ### Valid layers -/

variable (Γ)

/-- A layer `Γ[L, M]` as in Lemma 3.2 for the subgraph `A`: levels `L ⊆ M` with
`A ⊆ Γ[L, M]` and `Γ[L, M]^♭ = A^♭`.  The surgery may be computed with any of them
(proof of Lemma 3.3). -/
structure ValidLayer (A : Subgraph N E) where
  /-- The lower level. -/
  L : Set N
  /-- The upper level. -/
  M : Set N
  isLevel_L : Γ.IsLevel L
  isLevel_M : Γ.IsLevel M
  subset : L ⊆ M
  le : A ≤ Γ.layerSub L M
  flat_eq : Γ.flat (Γ.layerSub L M) = Γ.flat A

variable {Γ}

/-- The layer `Γ'^♯` as a valid layer. -/
def IsNormal.sharpLayer {A : Subgraph N E} (h : Γ.IsNormal A) : Γ.ValidLayer A :=
  ⟨_, _, h.isLevel_sharpL, isLevel_sharpM, sharpL_subset_sharpM, h.le_sharp, h.flat_sharp⟩

theorem isNormal_iff_nonempty_validLayer (A : Subgraph N E) :
    Γ.IsNormal A ↔ Nonempty (Γ.ValidLayer A) :=
  ⟨fun h => ⟨h.sharpLayer⟩, fun ⟨V⟩ => isNormal_of_layer V.isLevel_L V.isLevel_M V.le V.flat_eq⟩

namespace ValidLayer

variable {A : Subgraph N E} (V : Γ.ValidLayer A)

theorem isNormal (V : Γ.ValidLayer A) : Γ.IsNormal A := isNormal_of_layer V.isLevel_L V.isLevel_M V.le V.flat_eq

theorem node_iff (x : N) : A.node x ↔ Γ.LayerNode V.L V.M x := by
  have := congrArg (fun B : Subgraph N E => B.node x) V.flat_eq
  exact (Eq.to_iff this).symm

theorem edge_flat_iff (e : E) : (Γ.LayerEdge V.L V.M e ∧ ¬ Γ.LooseIn (Γ.LayerNode V.L V.M) e) ↔
    (A.edge e ∧ ¬ Γ.LooseIn A.node e) := by
  have := congrArg (fun B : Subgraph N E => B.edge e) V.flat_eq
  exact Eq.to_iff this

theorem edgeAt (V : Γ.ValidLayer A) : Γ.EdgeAt A := V.isNormal.edge_at

theorem layerEdge {e : E} (he : A.edge e) : Γ.LayerEdge V.L V.M e := V.le.2 e he

theorem looseIn_iff (e : E) : Γ.LooseIn A.node e ↔ Γ.LooseIn (Γ.LayerNode V.L V.M) e := by
  have : A.node = Γ.LayerNode V.L V.M := funext fun x => propext (V.node_iff x)
  rw [this]

/-- An edge of `A` whose source is not a node of `A` is cut by `L`. -/
theorem cut_L_of_dom {e : E} (he : A.edge e) (hs : ∀ x, Γ.src e = some x → ¬ A.node x) :
    Γ.Cut V.L e := by
  obtain ⟨h₁, h₂⟩ := V.layerEdge he
  refine ⟨fun x hx => ?_, h₂⟩
  by_contra hxL
  exact hs x hx ((V.node_iff x).2 ⟨h₁ x hx, hxL⟩)

/-- An edge of `A` whose target is not a node of `A` is cut by `M`. -/
theorem cut_M_of_cod {e : E} (he : A.edge e) (ht : ∀ y, Γ.tgt e = some y → ¬ A.node y) :
    Γ.Cut V.M e := by
  obtain ⟨h₁, h₂⟩ := V.layerEdge he
  refine ⟨h₁, fun y hy hyM => ?_⟩
  exact ht y hy ((V.node_iff y).2 ⟨hyM, h₂ y hy⟩)

/-- The source of an edge cut by `L` is not a node of `A`. -/
theorem not_node_src_of_cut_L {e : E} (he : Γ.Cut V.L e) (x : N) (hx : Γ.src e = some x) :
    ¬ A.node x := fun hxN => ((V.node_iff x).1 hxN).2 (he.1 x hx)

/-- The target of an edge cut by `M` is not a node of `A`. -/
theorem not_node_tgt_of_cut_M {e : E} (he : Γ.Cut V.M e) (y : N) (hy : Γ.tgt e = some y) :
    ¬ A.node y := fun hyN => he.2 y hy ((V.node_iff y).1 hyN).1

/-- An edge cut by `L` that is not in `A` is cut by `M` (it is loose in `Γ[L, M]`). -/
theorem cut_M_of_cut_L {e : E} (he : Γ.Cut V.L e) (hA : ¬ A.edge e) : Γ.Cut V.M e := by
  have hlay : Γ.LayerEdge V.L V.M e :=
    (Γ.mem_layerEdge_iff V.subset e).2 (Or.inr (Or.inl he))
  have hl : Γ.LooseIn (Γ.LayerNode V.L V.M) e := by
    by_contra hl
    exact hA ((V.edge_flat_iff e).1 ⟨hlay, hl⟩).1
  refine ⟨hlay.1, fun y hy hyM => hl.2 y hy ⟨hyM, he.2 y hy⟩⟩

/-- An edge cut by `M` that is not in `A` is cut by `L`. -/
theorem cut_L_of_cut_M {e : E} (he : Γ.Cut V.M e) (hA : ¬ A.edge e) : Γ.Cut V.L e := by
  have hlay : Γ.LayerEdge V.L V.M e :=
    (Γ.mem_layerEdge_iff V.subset e).2 (Or.inr (Or.inr he))
  have hl : Γ.LooseIn (Γ.LayerNode V.L V.M) e := by
    by_contra hl
    exact hA ((V.edge_flat_iff e).1 ⟨hlay, hl⟩).1
  refine ⟨fun x hx => ?_, hlay.2⟩
  by_contra hxL
  exact hl.1 x hx ⟨he.1 x hx, hxL⟩

end ValidLayer

end PGraph

end FreeMarkov
