/-
Free Markov categories, Stage 2: the statements of Section 3 about graphs without
valuations.

"In particular, if there is an isomorphism `Λ → Ω` of polarized graphs that induces `α`
and `β` then `Γ^Ω_Λ` is isomorphic to `Γ` (as anchored polarized graphs). If the template
is empty, that is, if `Λ = Ω = ∅`, then `Γ^Ω_Λ = Γ`."

These are deduced from the corresponding statements for diagrams by equipping every
graph with its *shape valuation* in a fixed free graph monoid (each node labelled by the
numbers of its inputs and outputs); isomorphisms of graphs are then isomorphisms of
diagrams, and the surgery on the valued diagram has the surgery on the graph as its
underlying anchored graph.
-/
module

public import FreeMarkov.Stage2.Templates

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅ u₆

namespace FreeMarkov

/-- The free graph monoid over one letter whose arrows are all pairs of words: every
polarized graph has a canonical valuation in it. -/
def shapeGM : FreeGraphMonoid.{0, 0} Unit where
  A := FreeMonoid Unit × FreeMonoid Unit
  s := Prod.fst
  t := Prod.snd

namespace PGraph

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}

/-- The shape valuation: every edge labelled by the letter, every node by the words of
the lengths of its inputs and outputs. -/
def shapeVal (Γ : PGraph N E) : Valuation shapeGM Γ.ins Γ.outs where
  v₀ _ := ()
  v₁ x := (FreeMonoid.ofList ((Γ.ins x).map fun _ => ()),
    FreeMonoid.ofList ((Γ.outs x).map fun _ => ()))
  s_v₁ _ := rfl
  t_v₁ _ := rfl

/-- A polarized graph with its shape valuation. -/
abbrev shape (Γ : PGraph N E) : PDiagram shapeGM N E := ⟨Γ, Γ.shapeVal⟩

/-- An isomorphism of graphs is an isomorphism of their shapes. -/
def Iso.shape {Γ : PGraph N E} {Γ' : PGraph N' E'} (i : Γ.Iso Γ') : Γ.shape.Iso Γ'.shape where
  toPIso := i
  v₀_map _ := rfl
  v₁_map x := by
    change (FreeMonoid.ofList ((Γ'.ins (i.eN x)).map _), FreeMonoid.ofList ((Γ'.outs (i.eN x)).map _)) = _
    rw [i.ins_map, i.outs_map, List.map_map, List.map_map]
    rfl

end PGraph

namespace AGraph

variable {N : Type u₁} {E : Type u₂}

/-- An anchored graph with its shape valuation. -/
abbrev shape (Γ : AGraph N E) : Diagram shapeGM N E := ⟨Γ, Γ.toPGraph.shapeVal⟩

variable (Γ : AGraph N E) {A : Subgraph N E} (V : Γ.ValidLayer A)
  {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PGraph NΩ EΩ} {NΛ : Type u₅} {EΛ : Type u₆}
  {Λ : PGraph NΛ EΛ} (φ : Ω.Iso (Γ.sub A.node A.edge))
  (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e})

/-- `φ` as an isomorphism of diagrams with the shape valuations. -/
def shapeSubIso : Ω.shape.Iso (Γ.shape.subD A V.edgeAt) where
  toPIso := φ
  v₀_map _ := rfl
  v₁_map z := by
    change (FreeMonoid.ofList ((Γ.ins (φ.eN z).1).map _), FreeMonoid.ofList ((Γ.outs (φ.eN z).1).map _)) = _
    rw [← PGraph.sub_ins_map_val (φ.eN z) fun e he =>
        V.edgeAt _ (φ.eN z).2 e (Or.inr ((Γ.mem_ins _ e).1 he)),
      ← PGraph.sub_outs_map_val (φ.eN z) fun e he =>
        V.edgeAt _ (φ.eN z).2 e (Or.inl ((Γ.mem_outs _ e).1 he))]
    rw [show (Γ.sub A.node A.edge).ins (φ.eN z) = (Ω.ins z).map φ.eE from φ.ins_map z,
      show (Γ.sub A.node A.edge).outs (φ.eN z) = (Ω.outs z).map φ.eE from φ.outs_map z]
    simp only [List.map_map]
    rfl

theorem surgeryAt_shape :
    (Γ.shape.surgeryAt (Ω := Ω.shape) (Λ := Λ.shape) V (Γ.shapeSubIso V φ) α β (fun _ => rfl)
      (fun _ => rfl)).toAGraph = Γ.surgeryAt V φ α β := rfl

/-- "If there is an isomorphism `Λ → Ω` of polarized graphs that induces `α` and `β`
then `Γ^Ω_Λ` is isomorphic to `Γ` (as anchored polarized graphs)." -/
noncomputable def surgeryAt_iso_self (ψ : Λ.Iso Ω) (hψα : ∀ d, (α d).1 = ψ.eE d.1)
    (hψβ : ∀ d, (β d).1 = ψ.eE d.1) : (Γ.surgeryAt V φ α β).Iso Γ :=
  Γ.surgeryAt_shape V φ α β ▸ (Γ.shape.surgeryAt_iso_self (Ω := Ω.shape) (Λ := Λ.shape) V
    (Γ.shapeSubIso V φ) α β (fun _ => rfl) (fun _ => rfl) ψ.shape hψα hψβ).toAIso

/-- The surgery of the paper: "if there is an isomorphism `Λ → Ω` of polarized graphs that
induces `α` and `β` then `Γ^Ω_Λ` is isomorphic to `Γ`". -/
noncomputable def surgery_iso_self (hA : Γ.IsNormal A) (ψ : Λ.Iso Ω)
    (hψα : ∀ d, (α d).1 = ψ.eE d.1) (hψβ : ∀ d, (β d).1 = ψ.eE d.1) :
    (Γ.surgery hA φ α β).Iso Γ :=
  Γ.surgeryAt_iso_self hA.sharpLayer φ α β ψ hψα hψβ

/-- The empty polarized graph. -/
def emptyGraph : PGraph PEmpty.{u₃ + 1} PEmpty.{u₃ + 1} := (PDiagram.empty.{u₃} shapeGM).toPGraph

/-- "If the template is empty, that is, if `Λ = Ω = ∅`, then `Γ^Ω_Λ = Γ`" (up to
isomorphism of anchored graphs; the empty subgraph is normal, and `φ` is the unique
isomorphism). -/
noncomputable def surgery_empty_iso :
    (Γ.surgery (Diagram.isNormal_empty Γ.shape)
      (Diagram.emptyIso.{u₃} Γ.shape (Diagram.isNormal_empty Γ.shape).edge_at).toPIso
      (Equiv.refl {e // emptyGraph.{u₃}.IsDom e}) (Equiv.refl {e // emptyGraph.{u₃}.IsCod e})).Iso Γ :=
  Γ.surgery_iso_self _ _ _ (Diagram.isNormal_empty Γ.shape) (PGraph.Iso.refl _)
    (fun d => d.1.elim) (fun d => d.1.elim)

end AGraph

end FreeMarkov
