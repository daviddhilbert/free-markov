/-
Free Markov categories, Stage 2: Definition 3.4 (templates, symmetric sets of templates,
`T`-surgeries, `T`-equivalence) and the relation `S_T` on the classes of diagrams.

A template `((Ω, u) / (Λ, w), α, β)` has its four types in a universe `u`.  `T`-equivalence
is defined, as in the paper, by chains of `T`-surgeries; the diagrams of a chain are
represented on `Fin` types (design decision D3), which is harmless because a
`T`-surgery step is invariant under isomorphisms on both sides (`TStep.iso_left`,
`TStep.iso_right`).  `S_T` is `T`-equivalence read on classes ("we may treat
`T`-equivalence as an equivalence relation on each hom-set of `F_s(G)`").
-/
module

public import FreeMarkov.Stage2.Lemma33

@[expose] public section

universe u w v u₁ u₂ u₃ u₄ u₅ u₆

namespace FreeMarkov

open Relation

variable {S : Type w}

/-- The empty diagram. -/
def PDiagram.empty (G : FreeGraphMonoid.{w, v} S) : PDiagram G PEmpty.{u + 1} PEmpty.{u + 1} where
  src e := e.elim
  tgt e := e.elim
  ins x := x.elim
  outs x := x.elim
  ins_nodup x := x.elim
  outs_nodup x := x.elim
  mem_ins x := x.elim
  mem_outs x := x.elim
  acyclic x := x.elim
  val := ⟨fun e => e.elim, fun x => x.elim, fun x => x.elim, fun x => x.elim⟩

/-- **Templates** (Section 3, the text before Lemma 3.3; used in Definition 3.4). A template `((Ω, u) / (Λ, w), α, β)`: two diagrams
`(Ω, u)`, `(Λ, w)` that are not anchored, with bijections `α : dom(Λ) → dom(Ω)` and
`β : cod(Λ) → cod(Ω)` along which the labels agree ("`u`, `w` are compatible with
respect to `α` and `β`"). -/
structure Template (G : FreeGraphMonoid.{w, v} S) where
  /-- The nodes of `Ω`. -/
  NΩ : Type u
  /-- The edges of `Ω`. -/
  EΩ : Type u
  /-- The nodes of `Λ`. -/
  NΛ : Type u
  /-- The edges of `Λ`. -/
  EΛ : Type u
  [finNΩ : Finite NΩ]
  [finEΩ : Finite EΩ]
  [finNΛ : Finite NΛ]
  [finEΛ : Finite EΛ]
  /-- The diagram `(Ω, u)` that is cut out. -/
  Ω : PDiagram G NΩ EΩ
  /-- The diagram `(Λ, w)` that is grafted. -/
  Λ : PDiagram G NΛ EΛ
  /-- `α : dom(Λ) → dom(Ω)`. -/
  α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}
  /-- `β : cod(Λ) → cod(Ω)`. -/
  β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}
  hα : ∀ e, Ω.val.v₀ (α e).1 = Λ.val.v₀ e.1
  hβ : ∀ e, Ω.val.v₀ (β e).1 = Λ.val.v₀ e.1

attribute [instance] Template.finNΩ Template.finEΩ Template.finNΛ Template.finEΛ

namespace Template

variable {G : FreeGraphMonoid.{w, v} S}

/-- The reversed template `((Λ, w) / (Ω, u), α⁻¹, β⁻¹)`. -/
def symm (τ : Template.{u} G) : Template.{u} G where
  NΩ := τ.NΛ
  EΩ := τ.EΛ
  NΛ := τ.NΩ
  EΛ := τ.EΩ
  Ω := τ.Λ
  Λ := τ.Ω
  α := τ.α.symm
  β := τ.β.symm
  hα := Diagram.symm_v₀ τ.α τ.hα
  hβ := Diagram.symm_v₀' τ.β τ.hβ

variable (G) in
/-- The empty template: "`Λ = Ω = ∅`". -/
def empty : Template.{u} G where
  NΩ := PEmpty
  EΩ := PEmpty
  NΛ := PEmpty
  EΛ := PEmpty
  Ω := PDiagram.empty G
  Λ := PDiagram.empty G
  α := Equiv.refl _
  β := Equiv.refl _
  hα _ := rfl
  hβ _ := rfl

end Template

/-- **Definition 3.4.** A set `T` of templates is **symmetric** and contains the empty
one: "if `((Ω, u) / (Λ, w), α, β)` is in `T` then `((Λ, w) / (Ω, u), α⁻¹, β⁻¹)` is also in
`T`". -/
structure Template.IsSymmetric {G : FreeGraphMonoid.{w, v} S} (T : Set (Template.{u} G)) :
    Prop where
  empty_mem : Template.empty G ∈ T
  symm_mem : ∀ τ ∈ T, τ.symm ∈ T

namespace Diagram

variable {G : FreeGraphMonoid.{w, v} S}

/-- **Definition 3.4.** A **`T`-surgery** step: the result of a surgery on `Γ` with a
template in `T` is isomorphic to `Υ`. -/
def TStep (T : Set (Template.{u} G)) {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}
    (Γ : Diagram G N E) (Υ : Diagram G N' E') : Prop :=
  ∃ τ ∈ T, ∃ (A : Subgraph N E) (hA : Γ.IsNormal A) (φ : τ.Ω.Iso (Γ.subD A hA.edge_at)),
    Nonempty ((Γ.surgery τ.α τ.β τ.hα τ.hβ hA φ).Iso Υ)

variable {T : Set (Template.{u} G)} {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}
  {N'' : Type u₅} {E'' : Type u₆} {Γ : Diagram G N E} {Υ : Diagram G N' E'}

theorem TStep.iso_right (h : TStep T Γ Υ) {Υ' : Diagram G N'' E''} (i : Υ.Iso Υ') :
    TStep T Γ Υ' := by
  obtain ⟨τ, hτ, A, hA, φ, ⟨j⟩⟩ := h
  exact ⟨τ, hτ, A, hA, φ, ⟨j.trans i⟩⟩

theorem TStep.iso_left (h : TStep T Γ Υ) {Γ' : Diagram G N'' E''} (i : Γ.Iso Γ') :
    TStep T Γ' Υ := by
  obtain ⟨τ, hτ, A, hA, φ, ⟨j⟩⟩ := h
  obtain ⟨A', hA', φ', ⟨k⟩⟩ :=
    Γ.surgeryAt_of_iso hA.sharpLayer φ τ.α τ.β τ.hα τ.hβ i
  exact ⟨τ, hτ, A', hA', φ', ⟨k.symm.trans j⟩⟩

theorem isNormal_empty (Γ : Diagram G N E) : Γ.IsNormal (Subgraph.empty N E) := by
  refine PGraph.isNormal_of_layer (L := ∅) (M := ∅) Γ.isLevel_empty Γ.isLevel_empty
    ⟨fun _ h => h.elim, fun _ h => h.elim⟩ ?_
  refine Subgraph.ext ?_ ?_
  · funext x
    exact propext ⟨fun h => h.1, fun h => h.elim⟩
  · funext e
    refine propext ⟨fun h => (h.2 ⟨fun x _ hx => hx.1, fun x _ hx => hx.1⟩).elim, fun h => h.1.elim⟩

/-- The empty diagram is isomorphic to the empty subgraph. -/
def emptyIso (Γ : Diagram G N E) (h : Γ.EdgeAt (Subgraph.empty N E)) :
    (PDiagram.empty.{u} G).Iso (Γ.subD (Subgraph.empty N E) h) where
  eN := @Equiv.equivOfIsEmpty _ _ _ ⟨fun x => x.2⟩
  eE := @Equiv.equivOfIsEmpty _ _ _ ⟨fun x => x.2⟩
  ins_map x := x.elim
  outs_map x := x.elim
  v₀_map e := e.elim
  v₁_map x := x.elim

/-- "If the template is empty, that is, if `Λ = Ω = ∅`, then `Γ^Ω_Λ = Γ`": for diagrams,
an isomorphism of diagrams. -/
noncomputable def surgery_empty_iso (Γ : Diagram G N E) :
    (Γ.surgery (Template.empty.{u} G).α (Template.empty.{u} G).β (Template.empty.{u} G).hα
      (Template.empty.{u} G).hβ (isNormal_empty Γ) (emptyIso Γ _)).Iso Γ :=
  Γ.surgeryAt_iso_self _ _ _ _ _ _ (PDiagram.Iso.refl _) (fun d => d.1.elim) (fun d => d.1.elim)

theorem TStep.of_iso (h0 : Template.empty G ∈ T) (i : Γ.Iso Υ) : TStep T Γ Υ :=
  ⟨_, h0, _, isNormal_empty Γ, emptyIso Γ _, ⟨(surgery_empty_iso Γ).trans i⟩⟩

theorem TStep.symm (hT : ∀ τ ∈ T, τ.symm ∈ T) (h : TStep T Γ Υ) : TStep T Υ Γ := by
  obtain ⟨τ, hτ, A, hA, φ, ⟨j⟩⟩ := h
  obtain ⟨A', hA', φ', ⟨k⟩⟩ := Γ.surgeryAt_reverse hA.sharpLayer φ τ.α τ.β τ.hα τ.hβ
  exact TStep.iso_left (Γ := Γ.surgery τ.α τ.β τ.hα τ.hβ hA φ)
    ⟨τ.symm, hT τ hτ, A', hA', φ', ⟨k⟩⟩ j

theorem TStep.domWord_eq (h : TStep T Γ Υ) : Υ.domWord = Γ.domWord := by
  obtain ⟨τ, -, A, hA, φ, ⟨j⟩⟩ := h
  rw [j.domWord_eq]
  exact surgeryAt_domWord _ _ _ _ _ _ _

theorem TStep.codWord_eq (h : TStep T Γ Υ) : Υ.codWord = Γ.codWord := by
  obtain ⟨τ, -, A, hA, φ, ⟨j⟩⟩ := h
  rw [j.codWord_eq]
  exact surgeryAt_codWord _ _ _ _ _ _ _

end Diagram

open Diagram

variable {G : FreeGraphMonoid.{w, v} S}

/-- **Definition 3.4.** Two anchored diagrams `Γ`, `Υ` are **`T`-equivalent** if there is a
sequence of anchored diagrams `(Γ = Γ₁, …, Γₙ = Υ)` such that, for each `i`, there is a
`T`-surgery on `Γᵢ` whose result is isomorphic to `Γᵢ₊₁` (diagrams on `Fin` types, D3). -/
def TEquiv (T : Set (Template.{u} G)) : FinDiag G → FinDiag G → Prop :=
  ReflTransGen fun Γ Υ => TStep T Γ.2 Υ.2

namespace TEquiv

variable {T : Set (Template.{u} G)}

theorem iso_left (h0 : Template.empty G ∈ T) {a b a' : FinDiag G} (h : TEquiv T a b)
    (i : a.2.Iso a'.2) : TEquiv T a' b := by
  rcases h.cases_head with rfl | ⟨c, hac, hcb⟩
  · exact ReflTransGen.single (TStep.of_iso h0 i.symm)
  · exact ReflTransGen.head (hac.iso_left i) hcb

theorem iso_right (h0 : Template.empty G ∈ T) {a b b' : FinDiag G} (h : TEquiv T a b)
    (i : b.2.Iso b'.2) : TEquiv T a b' := by
  rcases h.cases_tail with rfl | ⟨c, hac, hcb⟩
  · exact ReflTransGen.single (TStep.of_iso h0 i)
  · exact ReflTransGen.tail hac (hcb.iso_right i)

theorem symm (hT : ∀ τ ∈ T, τ.symm ∈ T) {a b : FinDiag G} (h : TEquiv T a b) : TEquiv T b a := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (hbc.symm hT) ih

theorem domWord_eq {a b : FinDiag G} (h : TEquiv T a b) : b.2.domWord = a.2.domWord := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact hbc.domWord_eq.trans ih

theorem codWord_eq {a b : FinDiag G} (h : TEquiv T a b) : b.2.codWord = a.2.codWord := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact hbc.codWord_eq.trans ih

end TEquiv

/-- **`S_T`** (after Definition 3.4): `T`-equivalence as a relation on the isomorphism
classes, i.e. on the morphisms of `F_s(G)`. -/
def SRel (T : Set (Template.{u} G)) (c d : DClass G) : Prop :=
  ∃ Γ Υ : FinDiag G, Quotient.mk _ Γ = c ∧ Quotient.mk _ Υ = d ∧ TEquiv T Γ Υ

namespace SRel

variable {T : Set (Template.{u} G)}

/-- "If `[Γ] = [Υ]`, `[Γ'] = [Υ']`, and `Γ ⇝_T Γ'` then clearly `Υ ⇝_T Υ'`." -/
theorem mk_iff (h0 : Template.empty G ∈ T) (Γ Υ : FinDiag G) :
    SRel T (Quotient.mk _ Γ) (Quotient.mk _ Υ) ↔ TEquiv T Γ Υ := by
  constructor
  · rintro ⟨Γ', Υ', hΓ, hΥ, h⟩
    obtain ⟨i⟩ := (Quotient.exact hΓ : Nonempty (Γ'.2.Iso Γ.2))
    obtain ⟨j⟩ := (Quotient.exact hΥ : Nonempty (Υ'.2.Iso Υ.2))
    exact (h.iso_left h0 i).iso_right h0 j
  · intro h
    exact ⟨Γ, Υ, rfl, rfl, h⟩

theorem refl (c : DClass G) : SRel T c c := by
  obtain ⟨Γ, rfl⟩ := Quotient.exists_rep c
  exact ⟨Γ, Γ, rfl, rfl, ReflTransGen.refl⟩

theorem symm (hT : ∀ τ ∈ T, τ.symm ∈ T) {c d : DClass G} (h : SRel T c d) : SRel T d c := by
  obtain ⟨Γ, Υ, hΓ, hΥ, h⟩ := h
  exact ⟨Υ, Γ, hΥ, hΓ, h.symm hT⟩

theorem trans (h0 : Template.empty G ∈ T) {c d e : DClass G} (h : SRel T c d)
    (h' : SRel T d e) : SRel T c e := by
  obtain ⟨Γ, Υ, rfl, rfl, h⟩ := h
  obtain ⟨Υ', Θ, hΥ, rfl, h'⟩ := h'
  obtain ⟨i⟩ := (Quotient.exact hΥ : Nonempty (Υ'.2.Iso Υ.2))
  exact ⟨Γ, Θ, rfl, rfl, h.trans (h'.iso_left h0 i)⟩

/-- `S_T` is an equivalence relation (for a symmetric set of templates containing the
empty one). -/
theorem equivalence (hT : Template.IsSymmetric T) : Equivalence (SRel T) :=
  ⟨refl, symm hT.symm_mem, trans hT.empty_mem⟩

theorem dom_eq {c d : DClass G} (h : SRel T c d) : d.dom = c.dom := by
  obtain ⟨Γ, Υ, rfl, rfl, h⟩ := h
  exact h.domWord_eq

theorem cod_eq {c d : DClass G} (h : SRel T c d) : d.cod = c.cod := by
  obtain ⟨Γ, Υ, rfl, rfl, h⟩ := h
  exact h.codWord_eq

theorem of_tStep {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄} [Finite N]
    [Finite E] [Finite N'] [Finite E'] {Γ : Diagram G N E} {Υ : Diagram G N' E'}
    (h : TStep T Γ Υ) : SRel T (DClass.mk Γ) (DClass.mk Υ) :=
  ⟨⟨(Nat.card N, Nat.card E), Γ.toFin⟩, ⟨(Nat.card N', Nat.card E'), Υ.toFin⟩, rfl, rfl,
    ReflTransGen.single ((h.iso_left Γ.isoToFin).iso_right Υ.isoToFin)⟩

end SRel

end FreeMarkov
