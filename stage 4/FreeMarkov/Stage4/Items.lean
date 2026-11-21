/-
Free Markov categories, Stage 4: the second and third items of Lemma 4.3 from a skeleton
bijection.

"For the second item ... `p` is a concatenation of consumers `e_1, …, e_n`, each preceded by the
edges that lead to it from its origin through duplicates ... Since the skeleton records exactly
the origins of the consumers, the second item follows.  For the third item ... we may assume
that they begin with the same edge in `dom(Γ)` or at the same node, which is live as before.
Now apply the second item to `p` and to `p'`."
-/
module

public import FreeMarkov.Stage4.Skeleton

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄} {Γ : Diagram G.toFreeGraphMonoid N E}
  {Υ : Diagram G.toFreeGraphMonoid N' E'}

theorem ins_length_eq_of_val {x : N} {y : N'} (h : Υ.val.v₁ y = Γ.val.v₁ x) :
    (Υ.ins y).length = (Γ.ins x).length := by
  have h₁ := Γ.val.s_v₁ x
  have h₂ := Υ.val.s_v₁ y
  rw [h, h₁] at h₂
  have := congrArg List.length (FreeMonoid.ofList.injective h₂)
  simpa using this.symm

theorem outs_length_eq_of_val {x : N} {y : N'} (h : Υ.val.v₁ y = Γ.val.v₁ x) :
    (Υ.outs y).length = (Γ.outs x).length := by
  have h₁ := Γ.val.t_v₁ x
  have h₂ := Υ.val.t_v₁ y
  rw [h, h₁] at h₂
  have := congrArg List.length (FreeMonoid.ofList.injective h₂)
  simpa using this.symm

theorem cod_length_eq_of_codWord (h : Γ.codWord = Υ.codWord) : Γ.cod.length = Υ.cod.length := by
  have := congrArg List.length (FreeMonoid.ofList.injective h)
  simpa using this

theorem dom_length_eq_of_domWord (h : Γ.domWord = Υ.domWord) : Γ.dom.length = Υ.dom.length := by
  have := congrArg List.length (FreeMonoid.ofList.injective h)
  simpa using this

theorem exists_getElem?_of_length_eq {l : List E} {l' : List E'} (hl : l.length = l'.length)
    {i : ℕ} {e : E} (h : l[i]? = some e) : ∃ e', l'[i]? = some e' := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.1 h).1
  exact ⟨l'[i]'(hl ▸ hi), List.getElem?_eq_getElem _⟩

/-! ### Symmetry of skeleton bijections -/

theorem OriginsMatch.symm {π : {x // Γ.Live x} ≃ {y // Υ.Live y}} {e : E} {e' : E'}
    (h : OriginsMatch π e e') : OriginsMatch π.symm e' e := by
  refine ⟨fun j => (h.1 j).symm, fun y j => ?_⟩
  have := h.2 (π.symm y) j
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

theorem SkeletonIso.symm {π : {x // Γ.Live x} ≃ {y // Υ.Live y}} (h : SkeletonIso Γ Υ π) :
    SkeletonIso Υ Γ π.symm where
  val_eq y := by
    have := h.val_eq (π.symm y)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  cod_match i e' e h₁ h₂ := (h.cod_match i e e' h₂ h₁).symm
  ins_match y i e' e h₁ h₂ := by
    have := h.ins_match (π.symm y) i e e' h₂ (by rw [Equiv.apply_symm_apply]; exact h₁)
    exact this.symm

theorem SameSkeleton.symm (h : SameSkeleton Γ Υ) : SameSkeleton Υ Γ := by
  obtain ⟨hd, hc, π, hπ⟩ := h
  exact ⟨hd.symm, hc.symm, π.symm, hπ.symm⟩

/-! ### Transport of `Feeds` and of chains of consumers -/

variable {π : {x // Γ.Live x} ≃ {y // Υ.Live y}}

/-- Lift a start or end of `Γ` to `Υ` along `π`. -/
abbrev liftEnd (π : {x // Γ.Live x} ≃ {y // Υ.Live y}) (s : PEnd {x // Γ.Live x}) : PEnd N' :=
  (s.map π).map Subtype.val

theorem feeds_of_skeletonIso (hc : Γ.codWord = Υ.codWord) (h : SkeletonIso Γ Υ π)
    (s t : PEnd {x // Γ.Live x}) (hF : Γ.toAGraph.Feeds Γ.val.IsDup (s.map Subtype.val) (t.map Subtype.val)) :
    Υ.toAGraph.Feeds Υ.val.IsDup (liftEnd π s) (liftEnd π t) := by
  obtain ⟨e, he, q, hq, hqe⟩ := hF
  -- the consumer `e` and its partner `e'`
  obtain ⟨e', he', hm⟩ : ∃ e' ∈ Υ.toAGraph.endEdges (liftEnd π t), OriginsMatch π e e' := by
    cases t with
    | node y =>
      obtain ⟨i, hi⟩ := exists_getElem?_of_mem (show e ∈ Γ.ins y.1 from he)
      obtain ⟨e', he'⟩ := exists_getElem?_of_length_eq (ins_length_eq_of_val (h.val_eq y)).symm hi
      exact ⟨e', List.mem_of_getElem? he', h.ins_match y i e e' hi he'⟩
    | edge j =>
      have hj : Γ.cod[j]? = some e := by simpa [AGraph.endEdges] using he
      obtain ⟨e', he'⟩ := exists_getElem?_of_length_eq (cod_length_eq_of_codWord hc) hj
      exact ⟨e', by simp [AGraph.endEdges, liftEnd, he'], h.cod_match j e e' hj he'⟩
  refine ⟨e', he', ?_⟩
  cases s with
  | node x =>
    obtain ⟨j, hj⟩ := exists_getElem?_of_mem (show q ∈ Γ.outs x.1 from hq)
    obtain ⟨q', hq', hq'e⟩ := (hm.2 x j).1 ⟨q, hj, hqe⟩
    exact ⟨q', List.mem_of_getElem? hq', hq'e⟩
  | edge j =>
    have hj : Γ.dom[j]? = some q := by simpa [AGraph.startEdges] using hq
    obtain ⟨q', hq', hq'e⟩ := (hm.1 j).1 ⟨q, hj, hqe⟩
    exact ⟨q', by simp [AGraph.startEdges, liftEnd, hq'], hq'e⟩

theorem sPath_of_skeletonIso (hc : Γ.codWord = Υ.codWord) (h : SkeletonIso Γ Υ π)
    (s : PEnd {x // Γ.Live x}) {t : PEnd N}
    (hs : Γ.toAGraph.SPath Γ.val.IsDup (s.map Subtype.val) t) :
    ∀ t₀ : PEnd {x // Γ.Live x}, t = t₀.map Subtype.val →
      Υ.toAGraph.SPath Υ.val.IsDup (liftEnd π s) (liftEnd π t₀) := by
  induction hs with
  | feeds hF =>
    rintro t₀ rfl
    exact .feeds (feeds_of_skeletonIso hc h s t₀ hF)
  | @trans y t _ hy hF ih =>
    rintro t₀ rfl
    have ih' := ih (.node ⟨y, hy⟩) rfl
    exact .trans ih' (π ⟨y, hy⟩).2 (feeds_of_skeletonIso hc h (.node ⟨y, hy⟩) t₀ hF)

theorem rootStart_val (s : PEnd {x // Γ.Live x}) :
    PEnd.RootStart Γ.val.IsDup (s.map Subtype.val) := by
  cases s with
  | node x => exact x.2.1
  | edge i => trivial

theorem consumerEnd_val (t : PEnd {x // Γ.Live x}) :
    Γ.toAGraph.ConsumerEnd Γ.val.IsDup (t.map Subtype.val) := by
  cases t with
  | node x => exact x.2
  | edge i => trivial

/-- Transport of directed paths between live nodes and edges of the domain and codomain. -/
theorem hasPath_of_skeletonIso (hc : Γ.codWord = Υ.codWord) (h : SkeletonIso Γ Υ π)
    (s t : PEnd {x // Γ.Live x}) (hp : Γ.toAGraph.HasPath (s.map Subtype.val) (t.map Subtype.val)) :
    Υ.toAGraph.HasPath (liftEnd π s) (liftEnd π t) := by
  rw [AGraph.hasPath_iff_dPath] at hp ⊢
  rw [AGraph.dPath_iff_sPath (rootStart_val s) (consumerEnd_val t)] at hp
  have h₁ : liftEnd π s = (s.map π).map Subtype.val := rfl
  rw [AGraph.dPath_iff_sPath (h₁ ▸ rootStart_val (s.map π)) (consumerEnd_val (t.map π))]
  exact sPath_of_skeletonIso hc h s hp t rfl

/-- **Lemma 4.3, second item, from a skeleton bijection.** "For all live nodes `x`, `y` of `Γ`,
there is a directed path in `Γ` from `x` to `y` if and only if there is one in `Υ` from `π(x)`
to `π(y)`, and the same holds for the directed paths that begin with the `i`-th edge in the
domain instead of beginning at `x`, `π(x)`, or end with the `j`-th edge in the codomain instead
of ending at `y`, `π(y)`." -/
theorem hasPath_iff_of_skeletonIso (hc : Γ.codWord = Υ.codWord) (h : SkeletonIso Γ Υ π)
    (s t : PEnd {x // Γ.Live x}) :
    Γ.toAGraph.HasPath (s.map Subtype.val) (t.map Subtype.val) ↔
      Υ.toAGraph.HasPath (liftEnd π s) (liftEnd π t) := by
  refine ⟨hasPath_of_skeletonIso hc h s t, fun hp => ?_⟩
  have := hasPath_of_skeletonIso hc.symm h.symm (s.map π) (t.map π) hp
  simpa [liftEnd, PEnd.map_map, Function.comp_def] using this

/-- Transport of splitter paths. -/
theorem hasSplitter_of_skeletonIso [Finite E] [Finite E'] (hc : Γ.codWord = Υ.codWord)
    (h : SkeletonIso Γ Υ π) (t t' : PEnd {x // Γ.Live x})
    (hp : Γ.toAGraph.HasSplitter (t.map Subtype.val) (t'.map Subtype.val)) :
    Υ.toAGraph.HasSplitter (liftEnd π t) (liftEnd π t') := by
  rw [AGraph.hasSplitter_iff Γ.dupCond (consumerEnd_val t)] at hp
  rw [AGraph.hasSplitter_iff Υ.dupCond (consumerEnd_val (t.map π))]
  obtain ⟨s, hs, h₁, h₂⟩ := hp
  -- lift the common start to the live nodes
  obtain ⟨s₀, rfl⟩ : ∃ s₀ : PEnd {x // Γ.Live x}, s = s₀.map Subtype.val := by
    cases s with
    | node x => exact ⟨.node ⟨x, hs x rfl⟩, rfl⟩
    | edge i => exact ⟨.edge i, rfl⟩
  refine ⟨liftEnd π s₀, fun y hy => ?_, ?_, ?_⟩
  · cases s₀ with
    | node x =>
      simp only [liftEnd, PEnd.map_node, PEnd.node.injEq] at hy
      exact hy ▸ (π x).2
    | edge i => cases hy
  · rw [← AGraph.hasPath_iff_dPath] at h₁ ⊢
    exact hasPath_of_skeletonIso hc h s₀ t h₁
  · rw [← AGraph.hasPath_iff_dPath] at h₂ ⊢
    exact hasPath_of_skeletonIso hc h s₀ t' h₂

/-- **Lemma 4.3, third item, from a skeleton bijection.** "The same holds for the splitter paths
between two ends each of which is a live node or an edge in the codomain." -/
theorem hasSplitter_iff_of_skeletonIso [Finite E] [Finite E'] (hc : Γ.codWord = Υ.codWord)
    (h : SkeletonIso Γ Υ π) (t t' : PEnd {x // Γ.Live x}) :
    Γ.toAGraph.HasSplitter (t.map Subtype.val) (t'.map Subtype.val) ↔
      Υ.toAGraph.HasSplitter (liftEnd π t) (liftEnd π t') := by
  refine ⟨hasSplitter_of_skeletonIso hc h t t', fun hp => ?_⟩
  have := hasSplitter_of_skeletonIso hc.symm h.symm (t.map π) (t'.map π) hp
  simpa [liftEnd, PEnd.map_map, Function.comp_def] using this

end Diagram

end FreeMarkov
