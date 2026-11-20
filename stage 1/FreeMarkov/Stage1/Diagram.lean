/-
Free Markov categories, Stage 1: valuations, diagrams, isomorphisms of diagrams,
and isomorphism classes of diagrams (Definition 2.1; design decisions D1, D3).

Classes of diagrams are taken through representatives whose nodes and edges are
`Fin n` and `Fin m` (D3): `DClass G` is the quotient of such diagrams by
isomorphism, so it lives in the universe of `G`, and `DClass.mk Γ` is the class of
a diagram `Γ` on arbitrary finite types in any universe.
-/
module

public import FreeMarkov.Stage1.Graph
public import Mathlib.SetTheory.Cardinal.NatCard

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u v'

namespace FreeMarkov

open CategoryTheory

/-- *Definition 2.1 (second half).* A **valuation** `v : Γ → G` of a polarized graph
with ordered inputs `ins` and outputs `outs` in a free graph monoid `G` over `S`:
"the valuation `v : Γ → (G, S, g)` mapping the edges and nodes into the alphabet `S`
and the set `A(G)` of arrows, respectively; that is, ... `v₁(x)` is an arrow of `G`
from the word `v₀(a₁) ⋯ v₀(aₙ)` to the word `v₀(b₁) ⋯ v₀(bₘ)` (the empty word if
`n = 0`, respectively `m = 0`)". -/
structure Valuation {S : Type w} (G : FreeGraphMonoid.{w, v} S) {N : Type u₁} {E : Type u₂}
    (ins outs : N → List E) where
  /-- The labels of the edges. -/
  v₀ : E → S
  /-- The labels of the nodes. -/
  v₁ : N → G.A
  s_v₁ (x : N) : G.s (v₁ x) = FreeMonoid.ofList ((ins x).map v₀)
  t_v₁ (x : N) : G.t (v₁ x) = FreeMonoid.ofList ((outs x).map v₀)

/-- *Definition 2.1.* An anchored **diagram** `(Γ, v)` in a free graph monoid `G`: an
anchored polarized progressive graph with a valuation in `G`. -/
structure Diagram {S : Type w} (G : FreeGraphMonoid.{w, v} S) (N : Type u₁) (E : Type u₂)
    extends AGraph N E where
  /-- The valuation. -/
  val : Valuation G ins outs

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄} {N'' : Type u₅} {E'' : Type u₆}

/-- *Definition 2.1.* The **domain** of an anchored diagram: the word of the labels of
the domain edges, in the given order. -/
def domWord (Γ : Diagram G N E) : FreeMonoid S := FreeMonoid.ofList (Γ.dom.map Γ.val.v₀)

/-- *Definition 2.1.* The **codomain** of an anchored diagram. -/
def codWord (Γ : Diagram G N E) : FreeMonoid S := FreeMonoid.ofList (Γ.cod.map Γ.val.v₀)

/-- *Definition 2.1.* "An **isomorphism of diagrams** `Γ → Ω` is an isomorphism of the
graphs that is compatible with the valuations in the obvious way. If the graphs are
anchored then the isomorphism is required to preserve the anchoring too." -/
structure Iso (Γ : Diagram G N E) (Γ' : Diagram G N' E') extends
    toAIso : AGraph.Iso Γ.toAGraph Γ'.toAGraph where
  v₀_map (e : E) : Γ'.val.v₀ (eE e) = Γ.val.v₀ e
  v₁_map (x : N) : Γ'.val.v₁ (eN x) = Γ.val.v₁ x

namespace Iso

variable {Γ : Diagram G N E} {Γ' : Diagram G N' E'} {Γ'' : Diagram G N'' E''}

/-- The identity isomorphism. -/
def refl (Γ : Diagram G N E) : Γ.Iso Γ where
  toAIso := AGraph.Iso.refl _
  v₀_map _ := rfl
  v₁_map _ := rfl

/-- The inverse isomorphism. -/
def symm (i : Γ.Iso Γ') : Γ'.Iso Γ where
  toAIso := i.toAIso.symm
  v₀_map e := by
    change Γ.val.v₀ (i.eE.symm e) = _
    rw [← i.v₀_map, Equiv.apply_symm_apply]
  v₁_map x := by
    change Γ.val.v₁ (i.eN.symm x) = _
    rw [← i.v₁_map, Equiv.apply_symm_apply]

/-- The composite isomorphism. -/
def trans (i : Γ.Iso Γ') (k : Γ'.Iso Γ'') : Γ.Iso Γ'' where
  toAIso := i.toAIso.trans k.toAIso
  v₀_map e := by
    change Γ''.val.v₀ (k.eE (i.eE e)) = _
    rw [k.v₀_map, i.v₀_map]
  v₁_map x := by
    change Γ''.val.v₁ (k.eN (i.eN x)) = _
    rw [k.v₁_map, i.v₁_map]

theorem domWord_eq (i : Γ.Iso Γ') : Γ'.domWord = Γ.domWord := by
  unfold domWord
  rw [i.dom_map, List.map_map]
  exact congrArg FreeMonoid.ofList (List.map_congr_left fun e _ => i.v₀_map e)

theorem codWord_eq (i : Γ.Iso Γ') : Γ'.codWord = Γ.codWord := by
  unfold codWord
  rw [i.cod_map, List.map_map]
  exact congrArg FreeMonoid.ofList (List.map_congr_left fun e _ => i.v₀_map e)

end Iso

/-- The diagram obtained by renaming nodes and edges along bijections. -/
def transport (Γ : Diagram G N E) (eN : N ≃ N') (eE : E ≃ E') : Diagram G N' E' where
  toAGraph := Γ.toAGraph.transport eN eE
  val :=
    { v₀ := fun e => Γ.val.v₀ (eE.symm e)
      v₁ := fun x => Γ.val.v₁ (eN.symm x)
      s_v₁ := fun x => by
        rw [Γ.val.s_v₁]
        simp [AGraph.transport, PGraph.transport, Function.comp_def]
      t_v₁ := fun x => by
        rw [Γ.val.t_v₁]
        simp [AGraph.transport, PGraph.transport, Function.comp_def] }

/-- A diagram is isomorphic to its transport. -/
def isoTransport (Γ : Diagram G N E) (eN : N ≃ N') (eE : E ≃ E') : Γ.Iso (Γ.transport eN eE) where
  toAIso := Γ.toAGraph.isoTransport eN eE
  v₀_map e := by simp [transport, AGraph.isoTransport, PGraph.isoTransport]
  v₁_map x := by simp [transport, AGraph.isoTransport, PGraph.isoTransport]

/-- The representative of a diagram on `Fin n` nodes and `Fin m` edges (D3). -/
noncomputable def toFin (Γ : Diagram G N E) [Finite N] [Finite E] :
    Diagram G (Fin (Nat.card N)) (Fin (Nat.card E)) :=
  Γ.transport (Finite.equivFin N) (Finite.equivFin E)

/-- A diagram is isomorphic to its `Fin` representative. -/
noncomputable def isoToFin (Γ : Diagram G N E) [Finite N] [Finite E] : Γ.Iso Γ.toFin :=
  Γ.isoTransport _ _

/-- A diagram whose nodes and edges are `Fin n` and `Fin m`. -/
def FinDiag (G : FreeGraphMonoid.{w, v} S) : Type (max w v) :=
  Σ p : ℕ × ℕ, Diagram G (Fin p.1) (Fin p.2)

/-- Isomorphism of diagrams, as a setoid on `Fin` representatives. -/
def isoSetoid (G : FreeGraphMonoid.{w, v} S) : Setoid (FinDiag G) where
  r Γ Δ := Nonempty (Γ.2.Iso Δ.2)
  iseqv := ⟨fun Γ => ⟨Iso.refl Γ.2⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨k⟩ => ⟨i.trans k⟩⟩

end Diagram

open Diagram

/-- *Section 2.* The **isomorphism classes** `[Γ, v]` of anchored diagrams in `G`
(through `Fin` representatives, design decision D3). -/
def DClass {S : Type w} (G : FreeGraphMonoid.{w, v} S) : Type (max w v) :=
  Quotient (Diagram.isoSetoid G)

namespace DClass

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

/-- The isomorphism class `[Γ, v]` of a diagram on arbitrary finite types. -/
noncomputable def mk (Γ : Diagram G N E) [Finite N] [Finite E] : DClass G :=
  Quotient.mk _ ⟨(_, _), Γ.toFin⟩

theorem mk_eq_mk_iff (Γ : Diagram G N E) [Finite N] [Finite E] (Γ' : Diagram G N' E')
    [Finite N'] [Finite E'] : mk Γ = mk Γ' ↔ Nonempty (Γ.Iso Γ') := by
  constructor
  · intro h
    obtain ⟨i⟩ := (Quotient.exact h : Nonempty (Γ.toFin.Iso Γ'.toFin))
    exact ⟨Γ.isoToFin.trans (i.trans Γ'.isoToFin.symm)⟩
  · rintro ⟨i⟩
    exact Quotient.sound ⟨Γ.isoToFin.symm.trans (i.trans Γ'.isoToFin)⟩

/-- Isomorphic diagrams have the same class. -/
theorem mk_eq_mk {Γ : Diagram G N E} [Finite N] [Finite E] {Γ' : Diagram G N' E'}
    [Finite N'] [Finite E'] (i : Γ.Iso Γ') : mk Γ = mk Γ' :=
  (mk_eq_mk_iff Γ Γ').2 ⟨i⟩

theorem mk_fin (Γ : FinDiag G) : Quotient.mk (Diagram.isoSetoid G) Γ = mk Γ.2 :=
  Quotient.sound ⟨Γ.2.isoToFin⟩

/-- Every class is the class of a diagram. -/
theorem exists_eq_mk (c : DClass G) :
    ∃ (n m : ℕ) (Γ : Diagram G (Fin n) (Fin m)), c = mk Γ := by
  induction c using Quotient.inductionOn with
  | h Γ => exact ⟨_, _, Γ.2, mk_fin Γ⟩

/-- Induction on classes. -/
theorem ind {P : DClass G → Prop} (h : ∀ (n m : ℕ) (Γ : Diagram G (Fin n) (Fin m)), P (mk Γ))
    (c : DClass G) : P c := by
  obtain ⟨n, m, Γ, rfl⟩ := exists_eq_mk c
  exact h n m Γ

/-- The domain word of a class. -/
def dom (c : DClass G) : FreeMonoid S :=
  Quotient.lift (fun Γ : FinDiag G => Γ.2.domWord) (fun a b h => (show Nonempty (a.2.Iso b.2) from h).elim fun i => i.domWord_eq.symm) c

/-- The codomain word of a class. -/
def cod (c : DClass G) : FreeMonoid S :=
  Quotient.lift (fun Γ : FinDiag G => Γ.2.codWord) (fun a b h => (show Nonempty (a.2.Iso b.2) from h).elim fun i => i.codWord_eq.symm) c

@[simp] theorem dom_mk (Γ : Diagram G N E) [Finite N] [Finite E] : (mk Γ).dom = Γ.domWord :=
  Γ.isoToFin.domWord_eq

@[simp] theorem cod_mk (Γ : Diagram G N E) [Finite N] [Finite E] : (mk Γ).cod = Γ.codWord :=
  Γ.isoToFin.codWord_eq

end DClass

/-- The isomorphism classes of anchored diagrams in `G` from the word `a` to the word
`b`: the morphisms `a → b` of `F_s(G)` (Section 2). -/
def DHom {S : Type w} (G : FreeGraphMonoid.{w, v} S) (a b : FreeMonoid S) : Type (max w v) :=
  {c : DClass G // c.dom = a ∧ c.cod = b}

namespace DHom

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

@[ext] theorem ext {a b : FreeMonoid S} {f g : DHom G a b} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

/-- The class of a diagram, as a morphism from its domain to its codomain. -/
noncomputable def mk {N : Type u₁} {E : Type u₂} (Γ : Diagram G N E) [Finite N] [Finite E] :
    DHom G Γ.domWord Γ.codWord :=
  ⟨DClass.mk Γ, by simp, by simp⟩

end DHom

/-! ### Diagrams in a symmetric strict monoidal category -/

/-- The object `⊗ᵢ aᵢ` of a strict monoidal category for a word `a₁ ⋯ aₙ` of objects
(the unit `1` for the empty word). -/
def evalWord {C : Type u} [Monoid C] (a : FreeMonoid C) : C := FreeMonoid.lift id a

/-- *Definition 2.1 (first half).* A **valuation** `v : Γ → C` of a polarized graph in
a symmetric strict monoidal category `C`: "a pair of functions `v₁ : Γ₀ → C₁`,
`v₀ : Γ₁ → C₀` such that, for every node `x ∈ Γ₀` with `inn(x) = (a₁, …, aₙ)` and
`out(x) = (b₁, …, bₘ)`, `v₁(x)` is of the form `⊗ᵢ v₀(aᵢ) → ⊗ᵢ v₀(bᵢ)`; here if
`n = 0` or `m = 0` then the monoidal product in question is just the monoidal unit". -/
structure CValuation (C : Type u) [Monoid C] [Category.{v'} C] {N : Type u₁} {E : Type u₂}
    (ins outs : N → List E) where
  /-- The objects labelling the edges. -/
  v₀ : E → C
  /-- The morphisms labelling the nodes. -/
  v₁ (x : N) : evalWord (FreeMonoid.ofList ((ins x).map v₀)) ⟶
    evalWord (FreeMonoid.ofList ((outs x).map v₀))

/-- *Definition 2.1.* An anchored diagram `(Γ, v)` in a symmetric strict monoidal
category `C`. -/
structure CDiagram (C : Type u) [Monoid C] [Category.{v'} C] (N : Type u₁) (E : Type u₂)
    extends AGraph N E where
  /-- The valuation. -/
  val : CValuation C ins outs

namespace CDiagram

variable {C : Type u} [Monoid C] [Category.{v'} C] {N : Type u₁} {E : Type u₂}

/-- *Definition 2.1.* "If `Γ` is anchored then the domain `dom(Γ, v)` of `(Γ, v)` is the
object `⊗_{eᵢ ∈ dom(Γ)} v₀(eᵢ)`, where the monoidal product is taken with respect to
the ordering on `dom(Γ)`". -/
def domObj (Γ : CDiagram C N E) : C := evalWord (FreeMonoid.ofList (Γ.dom.map Γ.val.v₀))

/-- *Definition 2.1.* The codomain `cod(Γ, v)`. -/
def codObj (Γ : CDiagram C N E) : C := evalWord (FreeMonoid.ofList (Γ.cod.map Γ.val.v₀))

end CDiagram

/-- The free graph monoid `G_C` of a strict monoidal category `C` (PLAN.md, Section 2):
alphabet the objects of `C`, arrows `a₁⋯aₙ → b₁⋯bₘ` the morphisms
`⊗ᵢ aᵢ → ⊗ⱼ bⱼ`. -/
def graphOf (C : Type u) [Monoid C] [Category.{v'} C] : FreeGraphMonoid.{u, max u v'} C where
  A := Σ a b : FreeMonoid C, (evalWord a ⟶ evalWord b)
  s f := f.1
  t f := f.2.1

namespace CDiagram

variable {C : Type u} [Monoid C] [Category.{v'} C] {N : Type u₁} {E : Type u₂}

/-- A diagram in `C` is a diagram in the free graph monoid `G_C`. -/
def toFree (Γ : CDiagram C N E) : Diagram (graphOf C) N E where
  toAGraph := Γ.toAGraph
  val :=
    { v₀ := Γ.val.v₀
      v₁ := fun x => ⟨_, _, Γ.val.v₁ x⟩
      s_v₁ := fun _ => rfl
      t_v₁ := fun _ => rfl }

@[simp] theorem toFree_domWord (Γ : CDiagram C N E) :
    Γ.toFree.domWord = FreeMonoid.ofList (Γ.dom.map Γ.val.v₀) := rfl

@[simp] theorem toFree_codWord (Γ : CDiagram C N E) :
    Γ.toFree.codWord = FreeMonoid.ofList (Γ.cod.map Γ.val.v₀) := rfl

end CDiagram

end FreeMarkov
