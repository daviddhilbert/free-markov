/-
Free Markov categories, Stage 1: the operations on diagrams that assemble them into
`F_s(G)` (Section 2): gluing (composition), disjoint union (monoidal product),
node-free diagrams of a permutation (identities and symmetries), one-node diagrams
(generators); their invariance under isomorphism, and the induced operations on
isomorphism classes.

*Section 2.* "If `cod(Γ, v) = dom(Ω, w)` then `[Ω, w] ∘ [Γ, v]` is represented by the
diagram obtained from the disjoint union of `Γ` and `Ω` by identifying the outer
nodes in `cod(Γ)` with those in `dom(Ω)` in the given order and then removing them,
so that each pair of edges thus matched becomes a single edge. The monoidal product
`[Γ, v] ⊗ [Ω, w]` is represented by the disjoint union of `Γ` and `Ω`, with the
orderings of the domains, and of the codomains, concatenated. The identities and the
symmetries are represented by diagrams without inner nodes, where the orderings of
the domain and the codomain differ by the permutation in question."

Gluing is defined for polarized graphs along an arbitrary bijection
`m : cod(Γ) → dom(Ω)` (the surgeries of Section 3 glue along such bijections); the
composition of anchored graphs is the case where `m` matches the two orderings
position by position.  In the glued graph an edge of `Ω` whose source is outer is
identified with the edge of `Γ` it is matched with, so its edges are those of `Γ`
and those of `Ω` with an inner source.
-/
module

public import FreeMarkov.Stage1.Diagram

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace FreeMarkov

open Relation

theorem not_transGen_of_forall_not {α : Type u₁} {r : α → α → Prop} (h : ∀ a b, ¬ r a b)
    {a b : α} : ¬ TransGen r a b := by
  intro hab
  cases hab with
  | single h' => exact h _ _ h'
  | tail _ h' => exact h _ _ h'

/-! ### Disjoint union -/

namespace PGraph

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}

/-- The disjoint union of two polarized graphs. -/
def tensor (Γ : PGraph N E) (Ω : PGraph N' E') : PGraph (N ⊕ N') (E ⊕ E') where
  src := Sum.elim (fun e => (Γ.src e).map .inl) (fun e => (Ω.src e).map .inr)
  tgt := Sum.elim (fun e => (Γ.tgt e).map .inl) (fun e => (Ω.tgt e).map .inr)
  ins := Sum.elim (fun x => (Γ.ins x).map .inl) (fun y => (Ω.ins y).map .inr)
  outs := Sum.elim (fun x => (Γ.outs x).map .inl) (fun y => (Ω.outs y).map .inr)
  ins_nodup x := by
    cases x with
    | inl x => exact (Γ.ins_nodup x).map Sum.inl_injective
    | inr y => exact (Ω.ins_nodup y).map Sum.inr_injective
  outs_nodup x := by
    cases x with
    | inl x => exact (Γ.outs_nodup x).map Sum.inl_injective
    | inr y => exact (Ω.outs_nodup y).map Sum.inr_injective
  mem_ins x e := by
    cases x <;> cases e <;> simp [Γ.mem_ins, Ω.mem_ins]
  mem_outs x e := by
    cases x <;> cases e <;> simp [Γ.mem_outs, Ω.mem_outs]
  acyclic := by
    have key : ∀ a b, TransGen (EdgeAdj (Sum.elim (fun e => (Γ.src e).map Sum.inl)
        (fun e => (Ω.src e).map Sum.inr)) (Sum.elim (fun e => (Γ.tgt e).map Sum.inl)
        (fun e => (Ω.tgt e).map Sum.inr))) a b →
        (∀ x y, a = .inl x → b = .inl y → TransGen Γ.Adj x y) ∧
        (∀ x y, a = .inr x → b = .inr y → TransGen Ω.Adj x y) ∧
        (∀ x y, a = .inl x → b = .inr y → False) ∧ (∀ x y, a = .inr x → b = .inl y → False) := by
      intro a b h
      induction h with
      | single hab =>
        obtain ⟨e, he₁, he₂⟩ := hab
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro x y rfl rfl <;> cases e <;> simp at he₁ he₂
        · exact .single ⟨_, he₁, he₂⟩
        · exact .single ⟨_, he₁, he₂⟩
      | tail _ hbc ih =>
        obtain ⟨e, he₁, he₂⟩ := hbc
        obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := ih
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro x y rfl rfl <;> cases e <;> simp at he₁ he₂
        all_goals first
          | (obtain ⟨z, hz, rfl⟩ := he₁; exact (ih₁ x z rfl rfl).tail ⟨_, hz, he₂⟩)
          | (obtain ⟨z, hz, rfl⟩ := he₁; exact (ih₂ x z rfl rfl).tail ⟨_, hz, he₂⟩)
          | (obtain ⟨z, hz, rfl⟩ := he₁; exact ih₃ x z rfl rfl)
          | (obtain ⟨z, hz, rfl⟩ := he₁; exact ih₄ x z rfl rfl)
    intro x hx
    cases x with
    | inl x => exact Γ.acyclic x ((key _ _ hx).1 x x rfl rfl)
    | inr x => exact Ω.acyclic x ((key _ _ hx).2.1 x x rfl rfl)

end PGraph

namespace AGraph

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}

/-- The disjoint union of two anchored graphs, with the orderings of the domains, and
of the codomains, concatenated. -/
def tensor (Γ : AGraph N E) (Ω : AGraph N' E') : AGraph (N ⊕ N') (E ⊕ E') where
  toPGraph := Γ.toPGraph.tensor Ω.toPGraph
  dom := Γ.dom.map .inl ++ Ω.dom.map .inr
  cod := Γ.cod.map .inl ++ Ω.cod.map .inr
  dom_nodup := by
    refine List.nodup_append.2 ⟨Γ.dom_nodup.map Sum.inl_injective,
      Ω.dom_nodup.map Sum.inr_injective, ?_⟩
    simp
  cod_nodup := by
    refine List.nodup_append.2 ⟨Γ.cod_nodup.map Sum.inl_injective,
      Ω.cod_nodup.map Sum.inr_injective, ?_⟩
    simp
  mem_dom e := by
    cases e <;> simp [PGraph.tensor, Γ.mem_dom, Ω.mem_dom]
  mem_cod e := by
    cases e <;> simp [PGraph.tensor, Γ.mem_cod, Ω.mem_cod]

end AGraph

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

/-- *Section 2.* The disjoint union of two diagrams: it represents `[Γ, v] ⊗ [Ω, w]`. -/
def tensor (Γ : Diagram G N E) (Ω : Diagram G N' E') : Diagram G (N ⊕ N') (E ⊕ E') where
  toAGraph := Γ.toAGraph.tensor Ω.toAGraph
  val :=
    { v₀ := Sum.elim Γ.val.v₀ Ω.val.v₀
      v₁ := Sum.elim Γ.val.v₁ Ω.val.v₁
      s_v₁ := fun x => by
        cases x <;> simp [AGraph.tensor, PGraph.tensor, Γ.val.s_v₁, Ω.val.s_v₁, Function.comp_def]
      t_v₁ := fun x => by
        cases x <;> simp [AGraph.tensor, PGraph.tensor, Γ.val.t_v₁, Ω.val.t_v₁, Function.comp_def] }

@[simp] theorem tensor_domWord (Γ : Diagram G N E) (Ω : Diagram G N' E') :
    (Γ.tensor Ω).domWord = Γ.domWord * Ω.domWord := by
  simp [domWord, tensor, AGraph.tensor, Function.comp_def]

@[simp] theorem tensor_codWord (Γ : Diagram G N E) (Ω : Diagram G N' E') :
    (Γ.tensor Ω).codWord = Γ.codWord * Ω.codWord := by
  simp [codWord, tensor, AGraph.tensor, Function.comp_def]

end Diagram

/-! ### Gluing -/

namespace PGraph

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}
  {Γ : PGraph N E} {Ω : PGraph N' E'} (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e})

/-- The edges of `Ω` with an inner source; together with the edges of `Γ` they are
the edges of the glued graph. -/
abbrev InnerSrc (Ω : PGraph N' E') : Type u₄ := {e : E' // Ω.src e ≠ none}

/-- Where an edge of `Ω` goes in the glued graph: a domain edge of `Ω` becomes the
codomain edge of `Γ` it is matched with. -/
noncomputable def glueIn (e : E') : E ⊕ Ω.InnerSrc := by
  classical
  exact if h : Ω.src e = none then .inl (m.symm ⟨e, h⟩).1 else .inr ⟨e, h⟩

/-- The target of an edge of `Γ` in the glued graph. -/
noncomputable def glueTgt (e : E) : Option (N ⊕ N') := by
  classical
  exact if h : Γ.tgt e = none then (Ω.tgt (m ⟨e, h⟩).1).map .inr else (Γ.tgt e).map .inl

theorem glueIn_of_eq_none {e : E'} (h : Ω.src e = none) : glueIn m e = .inl (m.symm ⟨e, h⟩).1 := by
  simp [glueIn, h]

theorem glueIn_of_ne_none {e : E'} (h : Ω.src e ≠ none) : glueIn m e = .inr ⟨e, h⟩ := by
  simp [glueIn, h]

theorem glueIn_eq_inl_iff (e : E') (a : E) :
    glueIn m e = .inl a ↔ ∃ h : Γ.tgt a = none, (m ⟨a, h⟩).1 = e := by
  by_cases h : Ω.src e = none
  · rw [glueIn_of_eq_none m h, Sum.inl.injEq]
    constructor
    · rintro rfl
      exact ⟨(m.symm ⟨e, h⟩).2, by simp⟩
    · rintro ⟨ha, rfl⟩
      simp
  · rw [glueIn_of_ne_none m h]
    simp only [reduceCtorEq, false_iff, not_exists]
    rintro ha rfl
    exact h (m ⟨a, ha⟩).2

theorem glueIn_eq_inr_iff (e : E') (b : Ω.InnerSrc) : glueIn m e = .inr b ↔ b.1 = e := by
  by_cases h : Ω.src e = none
  · rw [glueIn_of_eq_none m h]
    simp only [reduceCtorEq, false_iff]
    rintro rfl
    exact b.2 h
  · rw [glueIn_of_ne_none m h, Sum.inr.injEq]
    constructor
    · rintro rfl; rfl
    · rintro rfl; rfl

theorem glueIn_injective : Function.Injective (glueIn m) := by
  intro e e' hee'
  by_cases h : Ω.src e = none
  · rw [glueIn_of_eq_none m h, eq_comm, glueIn_eq_inl_iff] at hee'
    obtain ⟨_, he⟩ := hee'
    rw [← he]
    simp
  · rw [glueIn_of_ne_none m h, eq_comm, glueIn_eq_inr_iff] at hee'
    exact hee'

theorem glueTgt_eq_some_inl_iff (e : E) (x : N) :
    glueTgt m e = some (.inl x) ↔ Γ.tgt e = some x := by
  by_cases h : Γ.tgt e = none
  · simp [glueTgt, h]
  · simp [glueTgt, h]

theorem glueTgt_eq_some_inr_iff (e : E) (y : N') :
    glueTgt m e = some (.inr y) ↔ ∃ h : Γ.tgt e = none, Ω.tgt (m ⟨e, h⟩).1 = some y := by
  by_cases h : Γ.tgt e = none
  · simp [glueTgt, h]
  · simp [glueTgt, h]

theorem glueTgt_eq_none_iff (e : E) :
    glueTgt m e = none ↔ ∃ h : Γ.tgt e = none, Ω.tgt (m ⟨e, h⟩).1 = none := by
  by_cases h : Γ.tgt e = none
  · simp [glueTgt, h]
  · simp [glueTgt, h]

/-- *Section 2.* **Gluing** `Γ` and `Ω` along a bijection `m : cod(Γ) → dom(Ω)`:
"the diagram obtained from the disjoint union of `Γ` and `Ω` by identifying the outer
nodes in `cod(Γ)` with those in `dom(Ω)` ... so that each pair of edges thus matched
becomes a single edge". -/
noncomputable def glue : PGraph (N ⊕ N') (E ⊕ Ω.InnerSrc) where
  src := Sum.elim (fun e => (Γ.src e).map .inl) (fun e => (Ω.src e.1).map .inr)
  tgt := Sum.elim (glueTgt m) (fun e => (Ω.tgt e.1).map .inr)
  ins := Sum.elim (fun x => (Γ.ins x).map .inl) (fun y => (Ω.ins y).map (glueIn m))
  outs := Sum.elim (fun x => (Γ.outs x).map .inl) (fun y => (Ω.outs y).map (glueIn m))
  ins_nodup x := by
    cases x with
    | inl x => exact (Γ.ins_nodup x).map Sum.inl_injective
    | inr y => exact (Ω.ins_nodup y).map (glueIn_injective m)
  outs_nodup x := by
    cases x with
    | inl x => exact (Γ.outs_nodup x).map Sum.inl_injective
    | inr y => exact (Ω.outs_nodup y).map (glueIn_injective m)
  mem_ins x e := by
    cases x with
    | inl x =>
      cases e with
      | inl a => simp [glueTgt_eq_some_inl_iff, Γ.mem_ins]
      | inr b => simp
    | inr y =>
      cases e with
      | inl a =>
        simp only [Sum.elim_inr, Sum.elim_inl, List.mem_map, glueIn_eq_inl_iff,
          glueTgt_eq_some_inr_iff, Ω.mem_ins]
        constructor
        · rintro ⟨e, he, h, rfl⟩
          exact ⟨h, he⟩
        · rintro ⟨h, he⟩
          exact ⟨_, he, h, rfl⟩
      | inr b =>
        simp only [Sum.elim_inr, List.mem_map, glueIn_eq_inr_iff, Ω.mem_ins]
        constructor
        · rintro ⟨e, he, rfl⟩
          simp [he]
        · intro h
          refine ⟨b.1, ?_, rfl⟩
          simpa using h
  mem_outs x e := by
    cases x with
    | inl x =>
      cases e with
      | inl a => simp [Γ.mem_outs]
      | inr b => simp
    | inr y =>
      cases e with
      | inl a =>
        simp only [Sum.elim_inr, Sum.elim_inl, List.mem_map, glueIn_eq_inl_iff, Ω.mem_outs]
        simp only [Option.map_eq_some_iff, reduceCtorEq, and_false, exists_false, iff_false,
          not_exists, not_and]
        rintro e he h rfl
        rw [(m ⟨a, h⟩).2] at he
        cases he
      | inr b =>
        simp only [Sum.elim_inr, List.mem_map, glueIn_eq_inr_iff, Ω.mem_outs]
        constructor
        · rintro ⟨e, he, rfl⟩
          simp [he]
        · intro h
          refine ⟨b.1, ?_, rfl⟩
          simpa using h
  acyclic := by
    -- No edge goes from a node of `Ω` back to a node of `Γ`, so a circuit stays in
    -- one of the two graphs.
    set src' : E ⊕ Ω.InnerSrc → Option (N ⊕ N') :=
      Sum.elim (fun e => (Γ.src e).map .inl) (fun e => (Ω.src e.1).map .inr)
    set tgt' : E ⊕ Ω.InnerSrc → Option (N ⊕ N') :=
      Sum.elim (glueTgt m) (fun e => (Ω.tgt e.1).map .inr)
    have adj_ll : ∀ x y, EdgeAdj src' tgt' (.inl x) (.inl y) → Γ.Adj x y := by
      rintro x y ⟨e, he₁, he₂⟩
      cases e with
      | inl a =>
        simp only [src', tgt', Sum.elim_inl, Option.map_eq_some_iff, Sum.inl.injEq,
          exists_eq_right] at he₁ he₂
        exact ⟨a, he₁, (glueTgt_eq_some_inl_iff m a y).1 he₂⟩
      | inr b => simp [src'] at he₁
    have adj_rr : ∀ x y, EdgeAdj src' tgt' (.inr x) (.inr y) → Ω.Adj x y := by
      rintro x y ⟨e, he₁, he₂⟩
      cases e with
      | inl a => simp [src'] at he₁
      | inr b =>
        simp only [src', tgt', Sum.elim_inr, Option.map_eq_some_iff, Sum.inr.injEq,
          exists_eq_right] at he₁ he₂
        exact ⟨b.1, he₁, he₂⟩
    have adj_rl : ∀ x y, ¬ EdgeAdj src' tgt' (.inr x) (.inl y) := by
      rintro x y ⟨e, he₁, he₂⟩
      cases e with
      | inl a => simp [src'] at he₁
      | inr b => simp [tgt'] at he₂
    have key : ∀ a b, TransGen (EdgeAdj src' tgt') a b →
        (∀ x y, a = .inl x → b = .inl y → TransGen Γ.Adj x y) ∧
        (∀ x y, a = .inr x → b = .inr y → TransGen Ω.Adj x y) ∧
        (∀ x y, a = .inr x → b = .inl y → False) := by
      intro a b h
      induction h with
      | single hab =>
        refine ⟨?_, ?_, ?_⟩ <;> rintro x y rfl rfl
        · exact .single (adj_ll x y hab)
        · exact .single (adj_rr x y hab)
        · exact adj_rl x y hab
      | @tail b c _ hbc ih =>
        obtain ⟨ih₁, ih₂, ih₃⟩ := ih
        refine ⟨?_, ?_, ?_⟩ <;> rintro x y rfl rfl
        · cases b with
          | inl z => exact (ih₁ x z rfl rfl).tail (adj_ll z y hbc)
          | inr z => exact (adj_rl z y hbc).elim
        · cases b with
          | inl z => exact (ih₃ x z rfl rfl).elim
          | inr z => exact (ih₂ x z rfl rfl).tail (adj_rr z y hbc)
        · cases b with
          | inl z => exact ih₃ x z rfl rfl
          | inr z => exact adj_rl z y hbc
    intro x hx
    cases x with
    | inl x => exact Γ.acyclic x ((key _ _ hx).1 x x rfl rfl)
    | inr x => exact Ω.acyclic x ((key _ _ hx).2.1 x x rfl rfl)

@[simp] theorem glue_src_inl (a : E) : (glue m).src (.inl a) = (Γ.src a).map .inl := rfl
@[simp] theorem glue_src_inr (b : Ω.InnerSrc) : (glue m).src (.inr b) = (Ω.src b.1).map .inr := rfl
@[simp] theorem glue_tgt_inl (a : E) : (glue m).tgt (.inl a) = glueTgt m a := rfl
@[simp] theorem glue_tgt_inr (b : Ω.InnerSrc) : (glue m).tgt (.inr b) = (Ω.tgt b.1).map .inr := rfl
@[simp] theorem glue_ins_inl (x : N) : (glue m).ins (.inl x) = (Γ.ins x).map .inl := rfl
@[simp] theorem glue_ins_inr (y : N') : (glue m).ins (.inr y) = (Ω.ins y).map (glueIn m) := rfl
@[simp] theorem glue_outs_inl (x : N) : (glue m).outs (.inl x) = (Γ.outs x).map .inl := rfl
@[simp] theorem glue_outs_inr (y : N') : (glue m).outs (.inr y) = (Ω.outs y).map (glueIn m) := rfl

end PGraph

namespace AGraph

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}

/-- The bijection `cod(Γ) → dom(Ω)` matching the orderings position by position. -/
noncomputable def matching (Γ : AGraph N E) (Ω : AGraph N' E')
    (h : Γ.cod.length = Ω.dom.length) : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e} :=
  Γ.codEnum.matching Ω.domEnum h

/-- *Section 2.* **Gluing** of anchored graphs, `cod(Γ)` to `dom(Ω)` in the given
order; the domain is that of `Γ`, the codomain that of `Ω`. -/
noncomputable def glue (Γ : AGraph N E) (Ω : AGraph N' E') (h : Γ.cod.length = Ω.dom.length) :
    AGraph (N ⊕ N') (E ⊕ Ω.InnerSrc) where
  toPGraph := PGraph.glue (Γ.matching Ω h)
  dom := Γ.dom.map .inl
  cod := Ω.cod.map (PGraph.glueIn (Γ.matching Ω h))
  dom_nodup := Γ.dom_nodup.map Sum.inl_injective
  cod_nodup := Ω.cod_nodup.map (PGraph.glueIn_injective _)
  mem_dom e := by
    cases e with
    | inl a => simp [Γ.mem_dom]
    | inr b => simpa using b.2
  mem_cod e := by
    cases e with
    | inl a =>
      simp only [List.mem_map, PGraph.glueIn_eq_inl_iff, PGraph.glue_tgt_inl,
        PGraph.glueTgt_eq_none_iff, Ω.mem_cod]
      constructor
      · rintro ⟨e, he, h, rfl⟩
        exact ⟨h, he⟩
      · rintro ⟨h, he⟩
        exact ⟨_, he, h, rfl⟩
    | inr b =>
      simp only [List.mem_map, PGraph.glueIn_eq_inr_iff, Ω.mem_cod, PGraph.glue_tgt_inr,
        Option.map_eq_none_iff]
      constructor
      · rintro ⟨e, he, rfl⟩
        exact he
      · intro h
        exact ⟨b.1, h, rfl⟩

end AGraph

namespace Valuation

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄} {Γ : PGraph N E} {Ω : PGraph N' E'}

theorem glueIn_v₀ (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e}) (v : Valuation G Γ.ins Γ.outs)
    (w : Valuation G Ω.ins Ω.outs) (hm : ∀ c, w.v₀ (m c).1 = v.v₀ c.1) (e : E') :
    Sum.elim v.v₀ (fun b : Ω.InnerSrc => w.v₀ b.1) (PGraph.glueIn m e) = w.v₀ e := by
  by_cases h : Ω.src e = none
  · rw [PGraph.glueIn_of_eq_none m h, Sum.elim_inl, ← hm, Equiv.apply_symm_apply]
  · rw [PGraph.glueIn_of_ne_none m h, Sum.elim_inr]

/-- The valuation of a glued graph, from valuations of the two pieces that agree on
the matched edges. -/
noncomputable def glue (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e}) (v : Valuation G Γ.ins Γ.outs)
    (w : Valuation G Ω.ins Ω.outs) (hm : ∀ c, w.v₀ (m c).1 = v.v₀ c.1) :
    Valuation G (PGraph.glue m).ins (PGraph.glue m).outs where
  v₀ := Sum.elim v.v₀ (fun b => w.v₀ b.1)
  v₁ := Sum.elim v.v₁ w.v₁
  s_v₁ x := by
    cases x with
    | inl x => simp [v.s_v₁, Function.comp_def]
    | inr y =>
      simp only [Sum.elim_inr, PGraph.glue_ins_inr, List.map_map, w.s_v₁]
      congr 1
      exact List.map_congr_left fun e _ => (glueIn_v₀ m v w hm e).symm
  t_v₁ x := by
    cases x with
    | inl x => simp [v.t_v₁, Function.comp_def]
    | inr y =>
      simp only [Sum.elim_inr, PGraph.glue_outs_inr, List.map_map, w.t_v₁]
      congr 1
      exact List.map_congr_left fun e _ => (glueIn_v₀ m v w hm e).symm

end Valuation

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

theorem length_eq_of_codWord_eq {Γ : Diagram G N E} {Ω : Diagram G N' E'}
    (h : Γ.codWord = Ω.domWord) : Γ.cod.length = Ω.dom.length := by
  have := congrArg (fun a => (FreeMonoid.toList a).length) h
  simpa [codWord, domWord] using this

theorem map_eq_of_codWord_eq {Γ : Diagram G N E} {Ω : Diagram G N' E'}
    (h : Γ.codWord = Ω.domWord) : Γ.cod.map Γ.val.v₀ = Ω.dom.map Ω.val.v₀ :=
  FreeMonoid.ofList.injective h

theorem matching_v₀ {Γ : Diagram G N E} {Ω : Diagram G N' E'} (h : Γ.codWord = Ω.domWord)
    (c : {e // Γ.IsCod e}) :
    Ω.val.v₀ (Γ.matching Ω.toAGraph (length_eq_of_codWord_eq h) c).1 = Γ.val.v₀ c.1 :=
  Enumeration.matching_spec _ _ _ _ _ (map_eq_of_codWord_eq h) c

/-- *Section 2.* **Gluing** of diagrams: if `cod(Γ, v) = dom(Ω, w)`, the glued diagram
represents `[Ω, w] ∘ [Γ, v]`. -/
noncomputable def glue (Γ : Diagram G N E) (Ω : Diagram G N' E') (h : Γ.codWord = Ω.domWord) :
    Diagram G (N ⊕ N') (E ⊕ Ω.InnerSrc) where
  toAGraph := Γ.toAGraph.glue Ω.toAGraph (length_eq_of_codWord_eq h)
  val := Valuation.glue _ Γ.val Ω.val (matching_v₀ h)

@[simp] theorem glue_domWord (Γ : Diagram G N E) (Ω : Diagram G N' E')
    (h : Γ.codWord = Ω.domWord) : (Γ.glue Ω h).domWord = Γ.domWord := by
  simp [domWord, glue, AGraph.glue, Valuation.glue, Function.comp_def]

@[simp] theorem glue_codWord (Γ : Diagram G N E) (Ω : Diagram G N' E')
    (h : Γ.codWord = Ω.domWord) : (Γ.glue Ω h).codWord = Ω.codWord := by
  simp only [codWord, glue, AGraph.glue, Valuation.glue, List.map_map]
  congr 1
  exact List.map_congr_left fun e _ => Valuation.glueIn_v₀ _ _ _ (matching_v₀ h) e

end Diagram

end FreeMarkov
