/-
Free Markov categories, Stage 7: tools for comparing classes of diagrams through embeddings.

Stage 4's embeddings `PEmb D X` (injective maps of nodes and edges carrying ordered inputs,
outputs and labels) are completed here by

* the identity and the composite of embeddings, and the inclusions of the two pieces of a
  gluing and of a disjoint union;
* the numbers of nodes and edges of glued and disjoint diagrams;
* the criterion `PEmb.mk_eq`: an embedding between diagrams with as many nodes and edges, which
  carries the domain and codomain orderings to those of the target, is an isomorphism, so the
  two diagrams have the same class.

No cited result is used.
-/
module

public import FreeMarkov.Stage4.Embed

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace FreeMarkov

open Relation

/-! ### Counting -/

theorem Enumeration.card_eq_length {E : Type u₂} {P : E → Prop} (o : Enumeration P) :
    Nat.card {e // P e} = o.list.length :=
  Nat.card_eq_of_equiv_fin o.equivFin

theorem card_subtype_add_card_not {E : Type u₂} [Finite E] (p : E → Prop) :
    Nat.card {e // p e} + Nat.card {e // ¬ p e} = Nat.card E := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl p)

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

section Card

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}

theorem card_dom_add_innerSrc (Ω : Diagram G N' E') [Finite E'] :
    Ω.dom.length + Nat.card Ω.InnerSrc = Nat.card E' := by
  rw [show Ω.dom.length = Nat.card {e // Ω.IsDom e} from Ω.domEnum.card_eq_length.symm]
  exact card_subtype_add_card_not _

/-- The number of edges of a glued diagram. -/
theorem card_glue_edges (Γ : Diagram G N E) (Ω : Diagram G N' E') [Finite E] [Finite E']
    (_h : Γ.codWord = Ω.domWord) :
    Nat.card (E ⊕ Ω.InnerSrc) + Ω.dom.length = Nat.card E + Nat.card E' := by
  rw [Nat.card_sum, ← Ω.card_dom_add_innerSrc]
  omega

theorem cod_length_eq_dom_length {Γ : Diagram G N E} {Ω : Diagram G N' E'}
    (h : Γ.codWord = Ω.domWord) : Γ.cod.length = Ω.dom.length :=
  length_eq_of_codWord_eq h

theorem card_dom_le (Ω : Diagram G N' E') [Finite E'] : Ω.dom.length ≤ Nat.card E' := by
  have := Ω.card_dom_add_innerSrc
  omega

theorem card_cod_le (Ω : Diagram G N' E') [Finite E'] : Ω.cod.length ≤ Nat.card E' := by
  rw [show Ω.cod.length = Nat.card {e // Ω.IsCod e} from Ω.codEnum.card_eq_length.symm]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

end Card

namespace PEmb

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄} {N'' : Type u₅}
  {E'' : Type u₆}

/-- The identity embedding. -/
def refl (X : Diagram G N E) : PEmb X X where
  ιN := id
  ιE := id
  injN := Function.injective_id
  injE := Function.injective_id
  ins _ := (List.map_id _).symm
  outs _ := (List.map_id _).symm
  v₀ _ := rfl
  v₁ _ := rfl

/-- The composite of two embeddings. -/
def comp {D : Diagram G N E} {X : Diagram G N' E'} {Y : Diagram G N'' E''} (e : PEmb D X)
    (f : PEmb X Y) : PEmb D Y where
  ιN := f.ιN ∘ e.ιN
  ιE := f.ιE ∘ e.ιE
  injN := f.injN.comp e.injN
  injE := f.injE.comp e.injE
  ins z := by simp only [Function.comp_apply, f.ins, e.ins, List.map_map]
  outs z := by simp only [Function.comp_apply, f.outs, e.outs, List.map_map]
  v₀ d := by simp only [Function.comp_apply, f.v₀, e.v₀]
  v₁ z := by simp only [Function.comp_apply, f.v₁, e.v₁]

/-- An embedding that is bijective and carries the anchoring to the anchoring is an
isomorphism. -/
noncomputable def toIso {D : Diagram G N E} {X : Diagram G N' E'} (e : PEmb D X)
    (hN : Function.Bijective e.ιN) (hE : Function.Bijective e.ιE) (hdom : D.dom.map e.ιE = X.dom)
    (hcod : D.cod.map e.ιE = X.cod) : D.Iso X where
  eN := Equiv.ofBijective _ hN
  eE := Equiv.ofBijective _ hE
  ins_map z := e.ins z
  outs_map z := e.outs z
  dom_map := hdom.symm
  cod_map := hcod.symm
  v₀_map d := e.v₀ d
  v₁_map z := e.v₁ z

/-- **Comparison by embeddings.** An embedding between diagrams with as many nodes and as many
edges, carrying the domain and codomain orderings to those of the target, identifies their
classes. -/
theorem mk_eq {D : Diagram G N E} {X : Diagram G N' E'} [Finite N] [Finite E] [Finite N']
    [Finite E'] (e : PEmb D X) (hN : Nat.card N' ≤ Nat.card N) (hE : Nat.card E' ≤ Nat.card E)
    (hdom : D.dom.map e.ιE = X.dom) (hcod : D.cod.map e.ιE = X.cod) :
    DClass.mk D = DClass.mk X :=
  DClass.mk_eq_mk (e.toIso (e.injN.bijective_of_nat_card_le hN)
    (e.injE.bijective_of_nat_card_le hE) hdom hcod)

/-! ### Inclusions of the pieces -/

section Glue

variable (Γ : Diagram G N E) (Ω : Diagram G N' E') (h : Γ.codWord = Ω.domWord)

/-- The edge map of the second piece into a gluing. -/
noncomputable abbrev gIn {Γ : Diagram G N E} {Ω : Diagram G N' E'} (h : Γ.codWord = Ω.domWord) :
    E' → E ⊕ Ω.InnerSrc :=
  PGraph.glueIn (Γ.toAGraph.matching Ω.toAGraph (length_eq_of_codWord_eq h))

/-- The first piece of a gluing embeds into it. -/
def glueL : PEmb Γ (Γ.glue Ω h) where
  ιN := Sum.inl
  ιE := Sum.inl
  injN := Sum.inl_injective
  injE := Sum.inl_injective
  ins _ := rfl
  outs _ := rfl
  v₀ _ := rfl
  v₁ _ := rfl

/-- The second piece of a gluing embeds into it. -/
noncomputable def glueR : PEmb Ω (Γ.glue Ω h) where
  ιN := Sum.inr
  ιE := gIn h
  injN := Sum.inr_injective
  injE := PGraph.glueIn_injective _
  ins _ := rfl
  outs _ := rfl
  v₀ d := Valuation.glueIn_v₀ _ Γ.val Ω.val (matching_v₀ h) d
  v₁ _ := rfl

/-- The domain edges of the second piece are glued to the codomain edges of the first, in
order. -/
theorem dom_map_gIn : Ω.dom.map (gIn h) = Γ.cod.map Sum.inl := by
  have hl : Γ.cod.length = Ω.dom.length := length_eq_of_codWord_eq h
  refine List.ext_getElem (by simp [hl]) fun i h₁ h₂ => ?_
  have hi : i < Γ.cod.length := by simpa using h₂
  have hi' : i < Ω.dom.length := by simpa using h₁
  rw [List.getElem_map, List.getElem_map]
  have hd : Ω.src Ω.dom[i] = none := (Ω.mem_dom _).1 (List.getElem_mem _)
  dsimp only [gIn]
  rw [PGraph.glueIn_of_eq_none _ hd, Sum.inl.injEq]
  have key := Enumeration.matching_getElem Γ.toAGraph.codEnum Ω.toAGraph.domEnum hl i hi
  have e₁ : (Γ.toAGraph.matching Ω.toAGraph hl) ⟨Γ.cod[i], Γ.toAGraph.codEnum.mem_of_mem
      (List.getElem_mem _)⟩ = ⟨Ω.dom[i], hd⟩ := Subtype.ext key
  rw [← e₁, Equiv.symm_apply_apply]

theorem glueL_dom : Γ.dom.map (glueL Γ Ω h).ιE = (Γ.glue Ω h).dom := rfl

theorem glueR_cod : Ω.cod.map (glueR Γ Ω h).ιE = (Γ.glue Ω h).cod := rfl

end Glue

section Tensor

variable (Γ : Diagram G N E) (Ω : Diagram G N' E')

/-- The first factor of a disjoint union embeds into it. -/
def tensorL : PEmb Γ (Γ.tensor Ω) where
  ιN := Sum.inl
  ιE := Sum.inl
  injN := Sum.inl_injective
  injE := Sum.inl_injective
  ins _ := rfl
  outs _ := rfl
  v₀ _ := rfl
  v₁ _ := rfl

/-- The second factor of a disjoint union embeds into it. -/
def tensorR : PEmb Ω (Γ.tensor Ω) where
  ιN := Sum.inr
  ιE := Sum.inr
  injN := Sum.inr_injective
  injE := Sum.inr_injective
  ins _ := rfl
  outs _ := rfl
  v₀ _ := rfl
  v₁ _ := rfl

end Tensor

/-! ### Gluing embeddings, with disjointness derived from sources -/

variable {NX : Type u₇} {EX : Type u₈} {X : Diagram G NX EX}

theorem src_eq_some {D : Diagram G N E} (e : PEmb D X) {d : E} {z : N} (h : D.src d = some z) :
    X.src (e.ιE d) = some (e.ιN z) := by
  rw [← X.mem_outs, e.outs]
  exact List.mem_map_of_mem ((D.mem_outs z d).2 h)

theorem tgt_eq_some {D : Diagram G N E} (e : PEmb D X) {d : E} {z : N} (h : D.tgt d = some z) :
    X.tgt (e.ιE d) = some (e.ιN z) := by
  rw [← X.mem_ins, e.ins]
  exact List.mem_map_of_mem ((D.mem_ins z d).2 h)

variable {Γ : Diagram G N E} {Ω : Diagram G N' E'}

/-- Gluing two embeddings; the edges are disjoint as soon as no domain edge of the first piece
goes to a node of the second. -/
noncomputable def glueS (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (h : Γ.codWord = Ω.domWord)
    (hc : Γ.cod.map e₁.ιE = Ω.dom.map e₂.ιE) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hdom : ∀ d, Γ.src d = none → ∀ z, X.src (e₁.ιE d) ≠ some (e₂.ιN z)) :
    PEmb (Γ.glue Ω h) X :=
  glue e₁ e₂ h hc hN fun d d' hdd => by
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 d'.2
    have h₂ := e₂.src_eq_some hz
    cases hds : Γ.src d with
    | none => exact hdom d hds z (hdd ▸ h₂)
    | some z₁ =>
      have h₁ := e₁.src_eq_some hds
      rw [hdd, h₂, Option.some.injEq] at h₁
      exact hN _ _ h₁.symm

theorem glueS_dom (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (h : Γ.codWord = Ω.domWord)
    (hc : Γ.cod.map e₁.ιE = Ω.dom.map e₂.ιE) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hdom : ∀ d, Γ.src d = none → ∀ z, X.src (e₁.ιE d) ≠ some (e₂.ιN z)) :
    (Γ.glue Ω h).dom.map (glueS e₁ e₂ h hc hN hdom).ιE = Γ.dom.map e₁.ιE :=
  glue_dom _ _ _ _ _ _

theorem glueS_cod (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (h : Γ.codWord = Ω.domWord)
    (hc : Γ.cod.map e₁.ιE = Ω.dom.map e₂.ιE) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hdom : ∀ d, Γ.src d = none → ∀ z, X.src (e₁.ιE d) ≠ some (e₂.ιN z)) :
    (Γ.glue Ω h).cod.map (glueS e₁ e₂ h hc hN hdom).ιE = Ω.cod.map e₂.ιE :=
  glue_cod _ _ _ _ _ _

end PEmb

end Diagram

end FreeMarkov
