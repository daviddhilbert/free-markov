/-
Free Markov categories, Stage 1: directed paths, the partial order `Γ̇` on the nodes,
levels, the edges cut by a level, subgraphs and layers `Γ[L, M]` (Section 2, after
Theorem 2.3).
-/
module

public import FreeMarkov.Stage1.Value

@[expose] public section

universe w v u₁ u₂

namespace FreeMarkov

open Relation

namespace PGraph

variable {N : Type u₁} {E : Type u₂} (Γ : PGraph N E)

/-! ### Directed paths and the partial order on nodes -/

/-- *Section 2.* "A **directed path** `p` in `Γ` is a sequence of edges `e₁, …, eₙ`,
`n ≥ 1`, with `eᵢ(1) = eᵢ₊₁(0)` for `i < n`."  Two consecutive edges meet at an inner
node (an outer node is the endpoint of a single edge end). -/
def IsPath (p : List E) : Prop :=
  p ≠ [] ∧ p.IsChain (fun e e' => ∃ x, Γ.tgt e = some x ∧ Γ.src e' = some x)

/-- The start `p(0) = e₁(0)` of a path (`none` for an outer node). -/
def pathSrc (p : List E) : Option N := p.head?.bind Γ.src

/-- The end `p(1) = eₙ(1)` of a path (`none` for an outer node). -/
def pathTgt (p : List E) : Option N := p.getLast?.bind Γ.tgt

/-- *Section 2.* "`x < y` if and only if there is a directed path `p` in `Γ` from
`p(0) = x` to `p(1) = y`" (`lt_iff_exists_path`). -/
def Lt (x y : N) : Prop := TransGen Γ.Adj x y

/-- *Section 2.* "we write `x ≤ y` if `x < y` or `x = y`". -/
def Le (x y : N) : Prop := Γ.Lt x y ∨ x = y

theorem lt_of_path : ∀ (p : List E) (x y : N), Γ.IsPath p → Γ.pathSrc p = some x →
    Γ.pathTgt p = some y → Γ.Lt x y
  | [], _, _, h, _, _ => (h.1 rfl).elim
  | [e], x, y, _, hx, hy => .single ⟨e, by simpa [pathSrc] using hx, by simpa [pathTgt] using hy⟩
  | e :: e' :: ps, x, y, h, hx, hy => by
    obtain ⟨⟨z, hz, hz'⟩, hc⟩ := List.isChain_cons_cons.1 h.2
    have ih := lt_of_path (e' :: ps) z y ⟨List.cons_ne_nil _ _, hc⟩
      (by simpa [pathSrc] using hz') (by simpa [pathTgt] using hy)
    exact TransGen.head ⟨e, by simpa [pathSrc] using hx, hz⟩ ih

theorem exists_path_of_lt {x y : N} (h : Γ.Lt x y) :
    ∃ p, Γ.IsPath p ∧ Γ.pathSrc p = some x ∧ Γ.pathTgt p = some y := by
  induction h using TransGen.head_induction_on with
  | single hab =>
    obtain ⟨e, he₁, he₂⟩ := hab
    exact ⟨[e], ⟨List.cons_ne_nil _ _, List.isChain_singleton _⟩, by simpa [pathSrc],
      by simpa [pathTgt]⟩
  | head hab _ ih =>
    obtain ⟨e, he₁, he₂⟩ := hab
    obtain ⟨p, hp, hp₁, hp₂⟩ := ih
    obtain ⟨e', ps, rfl⟩ := List.exists_cons_of_ne_nil hp.1
    refine ⟨e :: e' :: ps, ⟨List.cons_ne_nil _ _, List.isChain_cons_cons.2 ⟨⟨_, he₂, ?_⟩, hp.2⟩⟩,
      by simpa [pathSrc], by simpa [pathTgt] using hp₂⟩
    simpa [pathSrc] using hp₁

theorem lt_iff_exists_path (x y : N) :
    Γ.Lt x y ↔ ∃ p, Γ.IsPath p ∧ Γ.pathSrc p = some x ∧ Γ.pathTgt p = some y :=
  ⟨Γ.exists_path_of_lt, fun ⟨p, hp, hx, hy⟩ => Γ.lt_of_path p x y hp hx hy⟩

theorem lt_irrefl (x : N) : ¬ Γ.Lt x x := Γ.acyclic x

theorem lt_trans {x y z : N} (h : Γ.Lt x y) (h' : Γ.Lt y z) : Γ.Lt x z := h.trans h'

theorem lt_of_edge {e : E} {x y : N} (hx : Γ.src e = some x) (hy : Γ.tgt e = some y) :
    Γ.Lt x y := .single ⟨e, hx, hy⟩

/-- *Section 2.* "This is a strict partial ordering since there are no directed
circuits ... the thus formed partially ordered set is denoted by `Γ̇`." -/
@[reducible] def nodeOrder : PartialOrder N where
  le := Γ.Le
  lt := Γ.Lt
  le_refl _ := Or.inr rfl
  le_trans x y z := by
    rintro (h | rfl) (h' | rfl)
    · exact Or.inl (h.trans h')
    · exact Or.inl h
    · exact Or.inl h'
    · exact Or.inr rfl
  le_antisymm x y h h' := by
    rcases h with h | h
    · rcases h' with h' | h'
      · exact (Γ.lt_irrefl x (h.trans h')).elim
      · exact h'.symm
    · exact h
  lt_iff_le_not_ge x y := by
    constructor
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (h' | rfl)
      · exact Γ.lt_irrefl x (h.trans h')
      · exact Γ.lt_irrefl _ h
    · rintro ⟨h | rfl, h'⟩
      · exact h
      · exact (h' (Or.inr rfl)).elim

/-! ### Levels and cuts -/

/-- *Section 2.* "An initial segment of `Γ̇` is referred to as a **level** of `Γ`." -/
def IsLevel (L : Set N) : Prop := ∀ x y, Γ.Lt x y → y ∈ L → x ∈ L

theorem isLevel_iff_isLowerSet (L : Set N) :
    Γ.IsLevel L ↔ @IsLowerSet N Γ.nodeOrder.toLE L := by
  constructor
  · intro h x y hxy hx
    rcases hxy with hxy | rfl
    · exact h y x hxy hx
    · exact hx
  · intro h x y hxy hy
    exact h (Or.inl hxy) hy

/-- *Section 2.* "with `∅` the smallest one". -/
theorem isLevel_empty : Γ.IsLevel ∅ := fun _ _ _ h => h

/-- *Section 2.* "... and `Γ̇` the largest one". -/
theorem isLevel_univ : Γ.IsLevel Set.univ := fun _ _ _ _ => trivial

/-- The source of `e` is an outer node or lies in `S`. -/
def SrcIn (S : Set N) (e : E) : Prop := ∀ x, Γ.src e = some x → x ∈ S

/-- The target of `e` is an outer node or lies in `S`. -/
def TgtIn (S : Set N) (e : E) : Prop := ∀ x, Γ.tgt e = some x → x ∈ S

/-- *Section 2.* "An edge `e` is said to be **cut** by a level `L` when
`e(0) ∈ L ∪ dom(Γ)` and `e(1) ∈ (Γ̇ ∖ L) ∪ cod(Γ)`." -/
def Cut (L : Set N) (e : E) : Prop := Γ.SrcIn L e ∧ Γ.TgtIn Lᶜ e

theorem srcIn_iff (S : Set N) (e : E) : Γ.SrcIn S e ↔ Γ.src e = none ∨ ∃ x ∈ S, Γ.src e = some x := by
  unfold SrcIn
  cases Γ.src e <;> simp

theorem tgtIn_iff (S : Set N) (e : E) : Γ.TgtIn S e ↔ Γ.tgt e = none ∨ ∃ x ∈ S, Γ.tgt e = some x := by
  unfold TgtIn
  cases Γ.tgt e <;> simp

/-- *Section 2.* "a loose edge of `Γ` is cut by every level". -/
theorem cut_of_isLoose {e : E} (h : Γ.IsLoose e) (L : Set N) : Γ.Cut L e :=
  ⟨fun x hx => (by rw [h.1] at hx; cases hx), fun x hx => (by rw [h.2] at hx; cases hx)⟩

/-- *Section 2.* `cut(∅) = dom(Γ)`. -/
theorem cut_empty_iff (e : E) : Γ.Cut ∅ e ↔ Γ.IsDom e := by
  unfold Cut SrcIn TgtIn IsDom
  constructor
  · rintro ⟨h, -⟩
    cases hs : Γ.src e with
    | none => rfl
    | some x => exact (h x hs).elim
  · intro h
    exact ⟨fun x hx => (by rw [h] at hx; cases hx), fun _ _ => Set.mem_compl (Set.notMem_empty _)⟩

/-- *Section 2.* `cut(Γ̇) = cod(Γ)`. -/
theorem cut_univ_iff (e : E) : Γ.Cut Set.univ e ↔ Γ.IsCod e := by
  unfold Cut SrcIn TgtIn IsCod
  constructor
  · rintro ⟨-, h⟩
    cases ht : Γ.tgt e with
    | none => rfl
    | some x => exact (h x ht (Set.mem_univ x)).elim
  · intro h
    exact ⟨fun _ _ => trivial, fun x hx => (by rw [h] at hx; cases hx)⟩

/-! ### Subgraphs -/

/-- The element `a` as an element of the subtype `{a // P a}`, if it belongs to it. -/
noncomputable def restrict {α : Type*} (P : α → Prop) (a : α) : Option {a // P a} := by
  classical
  exact if h : P a then some ⟨a, h⟩ else none

theorem restrict_eq_some_iff {α : Type*} {P : α → Prop} (a : α) (b : {a // P a}) :
    restrict P a = some b ↔ b.1 = a := by
  classical
  unfold restrict
  by_cases h : P a
  · simp only [h, dite_true, Option.some.injEq]
    constructor
    · rintro rfl; rfl
    · intro hb; exact Subtype.ext hb.symm
  · simp only [h, dite_false, reduceCtorEq, false_iff]
    intro hb
    exact h (hb ▸ b.2)

theorem restrict_of_mem {α : Type*} {P : α → Prop} (a : α) (h : P a) :
    restrict P a = some ⟨a, h⟩ := (restrict_eq_some_iff _ _).2 rfl

theorem restrict_eq_none_iff {α : Type*} {P : α → Prop} (a : α) :
    restrict P a = none ↔ ¬ P a := by
  classical
  unfold restrict
  by_cases h : P a <;> simp [h]

theorem bind_restrict_eq_some_iff {α : Type*} {P : α → Prop} (o : Option α) (b : {a // P a}) :
    o.bind (restrict P) = some b ↔ o = some b.1 := by
  cases o with
  | none => simp
  | some a => rw [Option.bind_some, restrict_eq_some_iff, Option.some.injEq, eq_comm]

theorem bind_restrict_eq_none_iff {α : Type*} {P : α → Prop} (o : Option α) :
    o.bind (restrict P) = none ↔ ∀ a, o = some a → ¬ P a := by
  cases o with
  | none => simp
  | some a => simp [restrict_eq_none_iff]

theorem mem_filterMap_restrict {α : Type*} {P : α → Prop} (l : List α) (b : {a // P a}) :
    b ∈ l.filterMap (restrict P) ↔ b.1 ∈ l := by
  simp only [List.mem_filterMap, restrict_eq_some_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro h; exact ⟨b.1, h, rfl⟩

theorem nodup_filterMap_restrict {α : Type*} {P : α → Prop} {l : List α} (h : l.Nodup) :
    (l.filterMap (restrict P)).Nodup :=
  h.filterMap fun a a' b hb hb' => by
    rw [Option.mem_def, restrict_eq_some_iff] at hb hb'
    exact hb.symm.trans hb'

theorem map_val_filterMap_restrict {α : Type*} {P : α → Prop} (l : List α) (h : ∀ a ∈ l, P a) :
    (l.filterMap (restrict P)).map Subtype.val = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, restrict_of_mem a (h a (List.mem_cons_self))]
    simp only [List.map_cons]
    rw [ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem map_val_filterMap_restrict_sublist {α : Type*} {P : α → Prop} (l : List α) :
    ((l.filterMap (restrict P)).map Subtype.val).Sublist l := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a l ih =>
    rw [List.filterMap_cons]
    cases h : restrict P a with
    | none => exact ih.cons a
    | some b =>
      rw [restrict_eq_some_iff] at h
      simp only [List.map_cons, h]
      exact ih.cons_cons a

/-- *Section 2.* The **subgraph** `Γ'` of `Γ` given by a set of nodes `P` and a set of
edges `Q`: "Thus if an end of an edge `e ∈ Γ'₁` is attached in `Γ` to a node outside
`Γ'₀` then, in `Γ'`, it is attached to an outer node of its own."  It inherits the
orientations and the orderings of `inn(x)`, `out(x)` ("polarized"). -/
noncomputable def sub (P : N → Prop) (Q : E → Prop) : PGraph {x // P x} {e // Q e} where
  src e := (Γ.src e.1).bind (restrict P)
  tgt e := (Γ.tgt e.1).bind (restrict P)
  ins x := (Γ.ins x.1).filterMap (restrict Q)
  outs x := (Γ.outs x.1).filterMap (restrict Q)
  ins_nodup x := nodup_filterMap_restrict (Γ.ins_nodup _)
  outs_nodup x := nodup_filterMap_restrict (Γ.outs_nodup _)
  mem_ins x e := by rw [mem_filterMap_restrict, bind_restrict_eq_some_iff, Γ.mem_ins]
  mem_outs x e := by rw [mem_filterMap_restrict, bind_restrict_eq_some_iff, Γ.mem_outs]
  acyclic x h := by
    refine Γ.acyclic x.1 (transGen_map Subtype.val (fun a b hab => ?_) h)
    obtain ⟨e, he₁, he₂⟩ := hab
    exact ⟨e.1, (bind_restrict_eq_some_iff _ _).1 he₁, (bind_restrict_eq_some_iff _ _).1 he₂⟩

variable {Γ}

theorem sub_src_eq_some_iff {P : N → Prop} {Q : E → Prop} (e : {e // Q e}) (x : {x // P x}) :
    (Γ.sub P Q).src e = some x ↔ Γ.src e.1 = some x.1 := bind_restrict_eq_some_iff _ _

theorem sub_tgt_eq_some_iff {P : N → Prop} {Q : E → Prop} (e : {e // Q e}) (x : {x // P x}) :
    (Γ.sub P Q).tgt e = some x ↔ Γ.tgt e.1 = some x.1 := bind_restrict_eq_some_iff _ _

theorem sub_src_eq_none_iff {P : N → Prop} {Q : E → Prop} (e : {e // Q e}) :
    (Γ.sub P Q).src e = none ↔ ∀ x, Γ.src e.1 = some x → ¬ P x := bind_restrict_eq_none_iff _

theorem sub_tgt_eq_none_iff {P : N → Prop} {Q : E → Prop} (e : {e // Q e}) :
    (Γ.sub P Q).tgt e = none ↔ ∀ x, Γ.tgt e.1 = some x → ¬ P x := bind_restrict_eq_none_iff _

/-- *Section 2.* "in particular, `e` is pinned in `Γ'` if and only if both `e(0)` and
`e(1)` belong to `Γ'₀`". -/
theorem sub_isPinned_iff {P : N → Prop} {Q : E → Prop} (e : {e // Q e}) :
    (Γ.sub P Q).IsPinned e ↔
      (∃ x, Γ.src e.1 = some x ∧ P x) ∧ (∃ y, Γ.tgt e.1 = some y ∧ P y) := by
  unfold IsPinned
  rw [Ne, Ne, sub_src_eq_none_iff, sub_tgt_eq_none_iff]
  simp only [not_forall, not_not, exists_prop]

/-- *Section 2.* "... and loose in `Γ'` if and only if neither does". -/
theorem sub_isLoose_iff {P : N → Prop} {Q : E → Prop} (e : {e // Q e}) :
    (Γ.sub P Q).IsLoose e ↔
      (∀ x, Γ.src e.1 = some x → ¬ P x) ∧ (∀ y, Γ.tgt e.1 = some y → ¬ P y) := by
  unfold IsLoose
  rw [sub_src_eq_none_iff, sub_tgt_eq_none_iff]

/-- *Section 2.* "Any subgraph `Γ' ⊆ Γ` inherits ... the total orderings of
`inn_Γ'(x) ⊆ inn_Γ(x)`". -/
theorem sub_ins_sublist {P : N → Prop} {Q : E → Prop} (x : {x // P x}) :
    (((Γ.sub P Q).ins x).map Subtype.val).Sublist (Γ.ins x.1) :=
  map_val_filterMap_restrict_sublist _

/-- *Section 2.* "... and `out_Γ'(x) ⊆ out_Γ(x)`". -/
theorem sub_outs_sublist {P : N → Prop} {Q : E → Prop} (x : {x // P x}) :
    (((Γ.sub P Q).outs x).map Subtype.val).Sublist (Γ.outs x.1) :=
  map_val_filterMap_restrict_sublist _

theorem sub_ins_map_val {P : N → Prop} {Q : E → Prop} (x : {x // P x})
    (h : ∀ e ∈ Γ.ins x.1, Q e) : ((Γ.sub P Q).ins x).map Subtype.val = Γ.ins x.1 :=
  map_val_filterMap_restrict _ h

theorem sub_outs_map_val {P : N → Prop} {Q : E → Prop} (x : {x // P x})
    (h : ∀ e ∈ Γ.outs x.1, Q e) : ((Γ.sub P Q).outs x).map Subtype.val = Γ.outs x.1 :=
  map_val_filterMap_restrict _ h

/-! ### Layers -/

variable (Γ)

/-- The nodes of the layer `Γ[L, M]`: those in `M ∖ L`. -/
abbrev LayerNode (_Γ : PGraph N E) (L M : Set N) (x : N) : Prop := x ∈ M ∧ x ∉ L

/-- The edges of the layer `Γ[L, M]`: source outer or in `M`, target outer or not in
`L`.  For `L ⊆ M` these are the pinned edges with both ends in `M ∖ L` and the edges
cut by `L` or by `M` (`mem_layerEdge_iff`). -/
abbrev LayerEdge (L M : Set N) (e : E) : Prop := Γ.SrcIn M e ∧ Γ.TgtIn Lᶜ e

/-- *Section 2.* The **layer** `Γ[L, M]` for levels `L ⊆ M`: "the subgraph of `Γ` such
that its inner nodes are those in `M ∖ L`, its pinned edges are those `e ∈ Γ₁` with
`e(0), e(1) ∈ M ∖ L`, its loose and half-loose edges are those in `cut(L) ∪ cut(M)`". -/
noncomputable def layer (L M : Set N) :
    PGraph {x // Γ.LayerNode L M x} {e // Γ.LayerEdge L M e} :=
  Γ.sub (Γ.LayerNode L M) (Γ.LayerEdge L M)

/-- The edges of `Γ[L, M]`, as described in the paper (for `L ⊆ M`). -/
theorem mem_layerEdge_iff {L M : Set N} (hLM : L ⊆ M) (e : E) :
    Γ.LayerEdge L M e ↔
      (∃ x y, Γ.src e = some x ∧ Γ.tgt e = some y ∧ Γ.LayerNode L M x ∧ Γ.LayerNode L M y) ∨
        Γ.Cut L e ∨ Γ.Cut M e := by
  unfold LayerEdge Cut SrcIn TgtIn
  constructor
  · rintro ⟨hs, ht⟩
    by_cases hL : ∀ x, Γ.src e = some x → x ∈ L
    · exact Or.inr (Or.inl ⟨hL, ht⟩)
    · simp only [not_forall] at hL
      obtain ⟨x, hx, hxL⟩ := hL
      by_cases hM : ∀ y, Γ.tgt e = some y → y ∈ Mᶜ
      · exact Or.inr (Or.inr ⟨hs, hM⟩)
      · simp only [not_forall, Set.mem_compl_iff, not_not] at hM
        obtain ⟨y, hy, hyM⟩ := hM
        exact Or.inl ⟨x, y, hx, hy, ⟨hs x hx, hxL⟩, ⟨hyM, ht y hy⟩⟩
  · rintro (⟨x, y, hx, hy, hxl, hyl⟩ | ⟨hs, ht⟩ | ⟨hs, ht⟩)
    · refine ⟨fun x' hx' => ?_, fun y' hy' => ?_⟩
      · rw [hx] at hx'; cases hx'; exact hxl.1
      · rw [hy] at hy'; cases hy'; exact hyl.2
    · exact ⟨fun x hx => hLM (hs x hx), ht⟩
    · exact ⟨hs, fun y hy hyL => ht y hy (hLM hyL)⟩

/-- *Section 2.* "`cut(L) = dom(Γ[L, M])`". -/
theorem layer_isDom_iff {L M : Set N} (e : {e // Γ.LayerEdge L M e}) :
    (Γ.layer L M).IsDom e ↔ Γ.Cut L e.1 := by
  unfold IsDom layer
  rw [sub_src_eq_none_iff]
  obtain ⟨hs, ht⟩ := e.2
  constructor
  · intro h
    refine ⟨fun x hx => ?_, ht⟩
    by_contra hxL
    exact h x hx ⟨hs x hx, hxL⟩
  · rintro ⟨hL, -⟩ x hx ⟨-, hxL⟩
    exact hxL (hL x hx)

/-- *Section 2.* "`cut(M) = cod(Γ[L, M])`". -/
theorem layer_isCod_iff {L M : Set N} (e : {e // Γ.LayerEdge L M e}) :
    (Γ.layer L M).IsCod e ↔ Γ.Cut M e.1 := by
  unfold IsCod layer
  rw [sub_tgt_eq_none_iff]
  obtain ⟨hs, ht⟩ := e.2
  constructor
  · intro h
    refine ⟨hs, fun y hy hyM => ?_⟩
    exact h y hy ⟨hyM, ht y hy⟩
  · rintro ⟨-, hM⟩ y hy ⟨hyM, -⟩
    exact hM y hy hyM

/-- *Section 2.* "the loose edges are exactly those in `cut(L) ∩ cut(M)`". -/
theorem layer_isLoose_iff {L M : Set N} (e : {e // Γ.LayerEdge L M e}) :
    (Γ.layer L M).IsLoose e ↔ Γ.Cut L e.1 ∧ Γ.Cut M e.1 := by
  unfold IsLoose
  exact and_congr (Γ.layer_isDom_iff e) (Γ.layer_isCod_iff e)

/-- *Section 2.* "`dom(Γ) = dom(Γ[∅, L])`". -/
theorem layer_empty_isDom_iff (L : Set N) (e : {e // Γ.LayerEdge ∅ L e}) :
    (Γ.layer ∅ L).IsDom e ↔ Γ.IsDom e.1 := by
  rw [Γ.layer_isDom_iff, cut_empty_iff]

/-- *Section 2.* "`cod(Γ) = cod(Γ[L, Γ̇])`". -/
theorem layer_univ_isCod_iff (L : Set N) (e : {e // Γ.LayerEdge L Set.univ e}) :
    (Γ.layer L Set.univ).IsCod e ↔ Γ.IsCod e.1 := by
  rw [Γ.layer_isCod_iff, cut_univ_iff]

/-- Every edge at a node of a layer between levels belongs to the layer. -/
theorem layerEdge_of_mem_ins {L M : Set N} (hM : Γ.IsLevel M) {x : N}
    (hx : Γ.LayerNode L M x) {e : E} (he : e ∈ Γ.ins x) : Γ.LayerEdge L M e := by
  rw [Γ.mem_ins] at he
  refine ⟨fun z hz => hM z x (Γ.lt_of_edge hz he) hx.1, fun y hy => ?_⟩
  rw [he] at hy; cases hy; exact hx.2

theorem layerEdge_of_mem_outs {L M : Set N} (hL : Γ.IsLevel L) {x : N}
    (hx : Γ.LayerNode L M x) {e : E} (he : e ∈ Γ.outs x) : Γ.LayerEdge L M e := by
  rw [Γ.mem_outs] at he
  refine ⟨fun z hz => ?_, fun y hy hyL => hx.2 (hL x y (Γ.lt_of_edge he hy) hyL)⟩
  rw [he] at hz; cases hz; exact hx.1

end PGraph

/-! ### Enumerations of the edges of a subgraph -/

namespace Enumeration

variable {E : Type u₂} {P : E → Prop}

/-- An enumeration of edges satisfying `P`, read in a subtype `{e // Q e}` containing
them, as an enumeration of a predicate `R` on the subtype that corresponds to `P`. -/
def lift (o : Enumeration P) {Q : E → Prop} (hPQ : ∀ e, P e → Q e) (R : {e // Q e} → Prop)
    (hR : ∀ e, R e ↔ P e.1) : Enumeration R where
  list := o.list.pmap Subtype.mk fun e he => hPQ e (o.mem_of_mem he)
  nodup := o.nodup.pmap fun _ _ _ _ h => congrArg Subtype.val h
  mem_iff e := by
    rw [List.mem_pmap, hR, ← o.mem_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro h; exact ⟨e.1, h, rfl⟩

theorem lift_map_val (o : Enumeration P) {Q : E → Prop} (hPQ : ∀ e, P e → Q e)
    (R : {e // Q e} → Prop) (hR : ∀ e, R e ↔ P e.1) :
    (o.lift hPQ R hR).list.map Subtype.val = o.list := by
  simp [lift, List.map_pmap]

end Enumeration

/-! ### Restricted valuations and anchored layers -/

namespace Valuation

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

/-- *Section 2 (used in Remark 2.4 and in Section 3).* The restriction of a valuation to a subgraph
that contains all the edges at each of its nodes. -/
noncomputable def restrict {Γ : PGraph N E} (v : Valuation G Γ.ins Γ.outs) (P : N → Prop)
    (Q : E → Prop) (hins : ∀ x, P x → ∀ e ∈ Γ.ins x, Q e)
    (houts : ∀ x, P x → ∀ e ∈ Γ.outs x, Q e) :
    Valuation G (Γ.sub P Q).ins (Γ.sub P Q).outs where
  v₀ e := v.v₀ e.1
  v₁ x := v.v₁ x.1
  s_v₁ x := by
    rw [v.s_v₁, ← PGraph.sub_ins_map_val x (hins x.1 x.2), List.map_map]
    rfl
  t_v₁ x := by
    rw [v.t_v₁, ← PGraph.sub_outs_map_val x (houts x.1 x.2), List.map_map]
    rfl

end Valuation

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

/-- *Remark 2.4.* The layer `Γ[L, M]` of an anchored diagram between levels `L ⊆ M`,
with its induced valuation, anchored by chosen total orderings `oL` of `cut(L)` and
`oM` of `cut(M)`. -/
noncomputable def layerD (Γ : Diagram G N E) {L M : Set N} (hL : Γ.IsLevel L)
    (hM : Γ.IsLevel M) (hLM : L ⊆ M) (oL : Enumeration (Γ.Cut L)) (oM : Enumeration (Γ.Cut M)) :
    Diagram G {x // Γ.LayerNode L M x} {e // Γ.LayerEdge L M e} where
  toPGraph := Γ.layer L M
  dom := (oL.lift (fun e he => ((Γ.mem_layerEdge_iff hLM e).2 (Or.inr (Or.inl he))))
    _ Γ.layer_isDom_iff).list
  cod := (oM.lift (fun e he => ((Γ.mem_layerEdge_iff hLM e).2 (Or.inr (Or.inr he))))
    _ Γ.layer_isCod_iff).list
  dom_nodup := Enumeration.nodup _
  cod_nodup := Enumeration.nodup _
  mem_dom := Enumeration.mem_iff _
  mem_cod := Enumeration.mem_iff _
  val := Γ.val.restrict _ _ (fun _ hx _ he => Γ.layerEdge_of_mem_ins hM hx he)
    (fun _ hx _ he => Γ.layerEdge_of_mem_outs hL hx he)

theorem layerD_dom_map_val (Γ : Diagram G N E) {L M : Set N} (hL : Γ.IsLevel L)
    (hM : Γ.IsLevel M) (hLM : L ⊆ M) (oL : Enumeration (Γ.Cut L)) (oM : Enumeration (Γ.Cut M)) :
    (Γ.layerD hL hM hLM oL oM).dom.map Subtype.val = oL.list := by
  simp [layerD, Enumeration.lift, List.map_pmap]

theorem layerD_cod_map_val (Γ : Diagram G N E) {L M : Set N} (hL : Γ.IsLevel L)
    (hM : Γ.IsLevel M) (hLM : L ⊆ M) (oL : Enumeration (Γ.Cut L)) (oM : Enumeration (Γ.Cut M)) :
    (Γ.layerD hL hM hLM oL oM).cod.map Subtype.val = oM.list := by
  simp [layerD, Enumeration.lift, List.map_pmap]

/-- The domain of `Γ` as an enumeration of `cut(∅)`. -/
def cutEmptyEnum (Γ : Diagram G N E) : Enumeration (Γ.Cut ∅) :=
  ⟨Γ.dom, Γ.dom_nodup, fun e => by rw [Γ.cut_empty_iff]; exact Γ.mem_dom e⟩

/-- The codomain of `Γ` as an enumeration of `cut(Γ̇)`. -/
def cutUnivEnum (Γ : Diagram G N E) : Enumeration (Γ.Cut Set.univ) :=
  ⟨Γ.cod, Γ.cod_nodup, fun e => by rw [Γ.cut_univ_iff]; exact Γ.mem_cod e⟩

end Diagram

end FreeMarkov
