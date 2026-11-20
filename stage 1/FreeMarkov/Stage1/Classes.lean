/-
Free Markov categories, Stage 1: invariance of gluing and disjoint union under
isomorphism; node-free and one-node diagrams; the operations on isomorphism classes
(the data of `F_s(G)`, Section 2).
-/
module

public import FreeMarkov.Stage1.Operations
public import Mathlib.Basic.Finite.Sum

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace FreeMarkov

open Relation

/-! ### Invariance under isomorphism -/

namespace PGraph.Iso

variable {N₁ : Type u₁} {E₁ : Type u₂} {N₂ : Type u₃} {E₂ : Type u₄} {N₃ : Type u₅}
  {E₃ : Type u₆} {N₄ : Type u₇} {E₄ : Type u₈}
  {Γ : PGraph N₁ E₁} {Γ' : PGraph N₂ E₂} {Ω : PGraph N₃ E₃} {Ω' : PGraph N₄ E₄}

/-- Disjoint union is invariant under isomorphism. -/
def tensor (i : Γ.Iso Γ') (k : Ω.Iso Ω') : (Γ.tensor Ω).Iso (Γ'.tensor Ω') where
  eN := Equiv.sumCongr i.eN k.eN
  eE := Equiv.sumCongr i.eE k.eE
  ins_map x := by
    cases x <;> simp [PGraph.tensor, i.ins_map, k.ins_map, Function.comp_def]
  outs_map x := by
    cases x <;> simp [PGraph.tensor, i.outs_map, k.outs_map, Function.comp_def]

/-- An isomorphism maps codomain edges to codomain edges. -/
def codMap (i : Γ.Iso Γ') (c : {e // Γ.IsCod e}) : {e // Γ'.IsCod e} :=
  ⟨i.eE c.1, by simp only [IsCod]; rw [i.tgt_map, c.2]; rfl⟩

/-- An isomorphism maps edges with an inner source to edges with an inner source. -/
def innerSrcEquiv (k : Ω.Iso Ω') : Ω.InnerSrc ≃ Ω'.InnerSrc :=
  k.eE.subtypeEquiv fun e => by rw [k.src_map]; simp

theorem glueIn_map (i : Γ.Iso Γ') (k : Ω.Iso Ω') (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e})
    (m' : {e // Γ'.IsCod e} ≃ {e // Ω'.IsDom e}) (hm : ∀ c, (m' (i.codMap c)).1 = k.eE (m c).1)
    (e : E₃) :
    PGraph.glueIn m' (k.eE e) = Equiv.sumCongr i.eE k.innerSrcEquiv (PGraph.glueIn m e) := by
  by_cases h : Ω.src e = none
  · have h' : Ω'.src (k.eE e) = none := by rw [k.src_map, h]; rfl
    rw [PGraph.glueIn_of_eq_none m h, PGraph.glueIn_of_eq_none m' h']
    simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.inl.injEq]
    have : m' (i.codMap (m.symm ⟨e, h⟩)) = ⟨k.eE e, h'⟩ :=
      Subtype.ext (by rw [hm]; simp)
    rw [← this, Equiv.symm_apply_apply]
    rfl
  · have h' : Ω'.src (k.eE e) ≠ none := by rw [k.src_map]; simpa using h
    rw [PGraph.glueIn_of_ne_none m h, PGraph.glueIn_of_ne_none m' h']
    rfl

/-- Gluing is invariant under isomorphisms compatible with the matchings. -/
noncomputable def glue (i : Γ.Iso Γ') (k : Ω.Iso Ω') (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e})
    (m' : {e // Γ'.IsCod e} ≃ {e // Ω'.IsDom e}) (hm : ∀ c, (m' (i.codMap c)).1 = k.eE (m c).1) :
    (PGraph.glue m).Iso (PGraph.glue m') where
  eN := Equiv.sumCongr i.eN k.eN
  eE := Equiv.sumCongr i.eE k.innerSrcEquiv
  ins_map x := by
    cases x with
    | inl x => simp [i.ins_map, Function.comp_def]
    | inr y =>
      simp only [Equiv.sumCongr_apply, Sum.map_inr, PGraph.glue_ins_inr, k.ins_map,
        List.map_map]
      exact List.map_congr_left fun e _ => glueIn_map i k m m' hm e
  outs_map x := by
    cases x with
    | inl x => simp [i.outs_map, Function.comp_def]
    | inr y =>
      simp only [Equiv.sumCongr_apply, Sum.map_inr, PGraph.glue_outs_inr, k.outs_map,
        List.map_map]
      exact List.map_congr_left fun e _ => glueIn_map i k m m' hm e

end PGraph.Iso

namespace AGraph.Iso

variable {N₁ : Type u₁} {E₁ : Type u₂} {N₂ : Type u₃} {E₂ : Type u₄} {N₃ : Type u₅}
  {E₃ : Type u₆} {N₄ : Type u₇} {E₄ : Type u₈}
  {Γ : AGraph N₁ E₁} {Γ' : AGraph N₂ E₂} {Ω : AGraph N₃ E₃} {Ω' : AGraph N₄ E₄}

/-- Disjoint union of anchored graphs is invariant under isomorphism. -/
def tensor (i : Γ.Iso Γ') (k : Ω.Iso Ω') : (Γ.tensor Ω).Iso (Γ'.tensor Ω') where
  toIso := i.toIso.tensor k.toIso
  dom_map := by
    simp [AGraph.tensor, PGraph.Iso.tensor, i.dom_map, k.dom_map, Function.comp_def]
  cod_map := by
    simp [AGraph.tensor, PGraph.Iso.tensor, i.cod_map, k.cod_map, Function.comp_def]

theorem matching_map (i : Γ.Iso Γ') (k : Ω.Iso Ω') (h : Γ.cod.length = Ω.dom.length)
    (h' : Γ'.cod.length = Ω'.dom.length) (c : {e // Γ.IsCod e}) :
    (Γ'.matching Ω' h' (i.codMap c)).1 = k.eE (Γ.matching Ω h c).1 :=
  Enumeration.matching_map Γ.codEnum Ω.domEnum Γ'.codEnum Ω'.domEnum h h' i.eE k.eE
    i.cod_map k.dom_map c _

/-- Gluing of anchored graphs is invariant under isomorphism. -/
noncomputable def glue (i : Γ.Iso Γ') (k : Ω.Iso Ω') (h : Γ.cod.length = Ω.dom.length)
    (h' : Γ'.cod.length = Ω'.dom.length) : (Γ.glue Ω h).Iso (Γ'.glue Ω' h') where
  toIso := i.toIso.glue k.toIso _ _ (matching_map i k h h')
  dom_map := by
    simp [AGraph.glue, PGraph.Iso.glue, i.dom_map, Function.comp_def]
  cod_map := by
    simp only [AGraph.glue, PGraph.Iso.glue, k.cod_map, List.map_map]
    exact List.map_congr_left fun e _ =>
      PGraph.Iso.glueIn_map i.toIso k.toIso _ _ (matching_map i k h h') e

end AGraph.Iso

namespace Diagram.Iso

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N₁ : Type u₁} {E₁ : Type u₂}
  {N₂ : Type u₃} {E₂ : Type u₄} {N₃ : Type u₅} {E₃ : Type u₆} {N₄ : Type u₇} {E₄ : Type u₈}
  {Γ : Diagram G N₁ E₁} {Γ' : Diagram G N₂ E₂} {Ω : Diagram G N₃ E₃} {Ω' : Diagram G N₄ E₄}

/-- Disjoint union of diagrams is invariant under isomorphism. -/
def tensor (i : Γ.Iso Γ') (k : Ω.Iso Ω') : (Γ.tensor Ω).Iso (Γ'.tensor Ω') where
  toAIso := i.toAIso.tensor k.toAIso
  v₀_map e := by
    cases e <;> simp [Diagram.tensor, AGraph.Iso.tensor, PGraph.Iso.tensor, i.v₀_map, k.v₀_map]
  v₁_map x := by
    cases x <;> simp [Diagram.tensor, AGraph.Iso.tensor, PGraph.Iso.tensor, i.v₁_map, k.v₁_map]

/-- Gluing of diagrams is invariant under isomorphism. -/
noncomputable def glue (i : Γ.Iso Γ') (k : Ω.Iso Ω') (h : Γ.codWord = Ω.domWord)
    (h' : Γ'.codWord = Ω'.domWord) : (Γ.glue Ω h).Iso (Γ'.glue Ω' h') where
  toAIso := i.toAIso.glue k.toAIso _ _
  v₀_map e := by
    cases e with
    | inl a => exact i.v₀_map a
    | inr b => exact k.v₀_map b.1
  v₁_map x := by
    cases x with
    | inl a => exact i.v₁_map a
    | inr b => exact k.v₁_map b

end Diagram.Iso

/-! ### Node-free diagrams -/

namespace PGraph

/-- The polarized graph without nodes on the edges `E`: every edge is loose. -/
def nodeFree (E : Type u₂) : PGraph Empty E where
  src _ := none
  tgt _ := none
  ins x := x.elim
  outs x := x.elim
  ins_nodup x := x.elim
  outs_nodup x := x.elim
  mem_ins x := x.elim
  mem_outs x := x.elim
  acyclic x := x.elim

end PGraph

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-- *Section 2.* A **node-free diagram**: no inner nodes, every edge loose, with
orderings `d` of the domain and `c` of the codomain (each a duplicate-free list of all
edges); they differ by a permutation. -/
def nodeFree {E : Type u₂} (v₀ : E → S) (d c : List E) (hd : d.Nodup) (hd' : ∀ e, e ∈ d)
    (hc : c.Nodup) (hc' : ∀ e, e ∈ c) : Diagram G Empty E where
  toPGraph := PGraph.nodeFree E
  dom := d
  cod := c
  dom_nodup := hd
  cod_nodup := hc
  mem_dom e := iff_of_true (hd' e) rfl
  mem_cod e := iff_of_true (hc' e) rfl
  val :=
    { v₀ := v₀
      v₁ := fun x => x.elim
      s_v₁ := fun x => x.elim
      t_v₁ := fun x => x.elim }

/-- The length of a word. -/
abbrev wlen (a : FreeMonoid S) : ℕ := (FreeMonoid.toList a).length

/-- The labelling of the positions of a word by its letters. -/
def letters (a : FreeMonoid S) (i : Fin (wlen a)) : S := (FreeMonoid.toList a)[(i : ℕ)]

theorem ofList_map_letters (a : FreeMonoid S) :
    FreeMonoid.ofList ((List.finRange (wlen a)).map (letters a)) = a :=
  (congrArg FreeMonoid.ofList (List.map_getElem_finRange (FreeMonoid.toList a))).trans
    (FreeMonoid.ofList_toList a)

/-- *Section 2.* The node-free diagram representing the identity on the word `a`. -/
def idD (G : FreeGraphMonoid.{w, v} S) (a : FreeMonoid S) : Diagram G Empty (Fin (wlen a)) :=
  nodeFree (letters a) (List.finRange _) (List.finRange _) (List.nodup_finRange _)
    (List.mem_finRange) (List.nodup_finRange _) (List.mem_finRange)

@[simp] theorem idD_domWord (a : FreeMonoid S) : (idD G a).domWord = a := ofList_map_letters a

@[simp] theorem idD_codWord (a : FreeMonoid S) : (idD G a).codWord = a := ofList_map_letters a

/-- *Section 2.* The node-free diagram of a permutation `π` of the positions of the
word `a`: the domain is ordered as the positions, the codomain as their images
under `π`.  Its codomain is the word `a` permuted by `π`. -/
def permD (G : FreeGraphMonoid.{w, v} S) (a : FreeMonoid S) (π : Equiv.Perm (Fin (wlen a))) :
    Diagram G Empty (Fin (wlen a)) :=
  nodeFree (letters a) (List.finRange _) ((List.finRange _).map π) (List.nodup_finRange _)
    (List.mem_finRange) ((List.nodup_finRange _).map π.injective)
    (fun e => List.mem_map.2 ⟨π.symm e, List.mem_finRange _, by simp⟩)

@[simp] theorem permD_domWord (a : FreeMonoid S) (π : Equiv.Perm (Fin (wlen a))) :
    (permD G a π).domWord = a := ofList_map_letters a

theorem permD_codWord (a : FreeMonoid S) (π : Equiv.Perm (Fin (wlen a))) :
    (permD G a π).codWord = FreeMonoid.ofList ((List.finRange _).map (letters a ∘ π)) := by
  simp [permD, nodeFree, codWord, List.map_map]

/-- The domain ordering of the symmetry diagram. -/
def braidDom (a b : FreeMonoid S) : List (Fin (wlen a) ⊕ Fin (wlen b)) :=
  (List.finRange _).map .inl ++ (List.finRange _).map .inr

/-- The codomain ordering of the symmetry diagram. -/
def braidCod (a b : FreeMonoid S) : List (Fin (wlen a) ⊕ Fin (wlen b)) :=
  (List.finRange _).map .inr ++ (List.finRange _).map .inl

/-- *Section 2.* The node-free diagram representing the symmetry `σ_{a,b}`. -/
def braidD (G : FreeGraphMonoid.{w, v} S) (a b : FreeMonoid S) :
    Diagram G Empty (Fin (wlen a) ⊕ Fin (wlen b)) :=
  nodeFree (Sum.elim (letters a) (letters b)) (braidDom a b) (braidCod a b)
    (List.nodup_append.2 ⟨(List.nodup_finRange _).map Sum.inl_injective,
      (List.nodup_finRange _).map Sum.inr_injective, by simp⟩)
    (fun e => by cases e <;> simp [braidDom])
    (List.nodup_append.2 ⟨(List.nodup_finRange _).map Sum.inr_injective,
      (List.nodup_finRange _).map Sum.inl_injective, by simp⟩)
    (fun e => by cases e <;> simp [braidCod])

@[simp] theorem braidD_domWord (a b : FreeMonoid S) : (braidD G a b).domWord = a * b := by
  simp only [braidD, nodeFree, domWord, braidDom, List.map_append, List.map_map, Sum.elim_comp_inl,
    Sum.elim_comp_inr]
  rw [FreeMonoid.ofList_append]
  exact congrArg₂ (· * ·) (ofList_map_letters a) (ofList_map_letters b)

@[simp] theorem braidD_codWord (a b : FreeMonoid S) : (braidD G a b).codWord = b * a := by
  simp only [braidD, nodeFree, codWord, braidCod, List.map_append, List.map_map, Sum.elim_comp_inl,
    Sum.elim_comp_inr]
  rw [FreeMonoid.ofList_append]
  exact congrArg₂ (· * ·) (ofList_map_letters b) (ofList_map_letters a)

/-! ### One-node diagrams -/

end Diagram

namespace PGraph

/-- The polarized graph with one node, `n` inputs and `m` outputs. -/
def oneNode (n m : ℕ) : PGraph Unit (Fin n ⊕ Fin m) where
  src := Sum.elim (fun _ => none) (fun _ => some ())
  tgt := Sum.elim (fun _ => some ()) (fun _ => none)
  ins _ := (List.finRange n).map .inl
  outs _ := (List.finRange m).map .inr
  ins_nodup _ := (List.nodup_finRange n).map Sum.inl_injective
  outs_nodup _ := (List.nodup_finRange m).map Sum.inr_injective
  mem_ins x e := by cases e <;> simp
  mem_outs x e := by cases e <;> simp
  acyclic _ := not_transGen_of_forall_not fun _ _ ⟨e, h₁, h₂⟩ => by cases e <;> simp at h₁ h₂

end PGraph

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-- *Section 2.* The **one-node diagram** of an arrow `x` of `G`: one node labelled
`x`, whose inputs and outputs are the domain and the codomain, labelled by the letters
of the source and target words of `x`.  It represents the generator `x` of `F_s(G)`. -/
def oneNode (x : G.A) : Diagram G Unit (Fin (wlen (G.s x)) ⊕ Fin (wlen (G.t x))) where
  toPGraph := PGraph.oneNode _ _
  dom := (List.finRange _).map .inl
  cod := (List.finRange _).map .inr
  dom_nodup := (List.nodup_finRange _).map Sum.inl_injective
  cod_nodup := (List.nodup_finRange _).map Sum.inr_injective
  mem_dom e := by cases e <;> simp [PGraph.oneNode]
  mem_cod e := by cases e <;> simp [PGraph.oneNode]
  val :=
    { v₀ := Sum.elim (letters (G.s x)) (letters (G.t x))
      v₁ := fun _ => x
      s_v₁ := fun _ => by
        simp only [PGraph.oneNode, List.map_map]
        exact (ofList_map_letters _).symm
      t_v₁ := fun _ => by
        simp only [PGraph.oneNode, List.map_map]
        exact (ofList_map_letters _).symm }

@[simp] theorem oneNode_domWord (x : G.A) : (oneNode x).domWord = G.s x := by
  simp only [domWord, oneNode, List.map_map]
  exact ofList_map_letters _

@[simp] theorem oneNode_codWord (x : G.A) : (oneNode x).codWord = G.t x := by
  simp only [codWord, oneNode, List.map_map]
  exact ofList_map_letters _

end Diagram

/-! ### Operations on isomorphism classes -/

namespace DClass

open Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

/-- *Section 2.* The monoidal product of classes, represented by disjoint union. -/
noncomputable def tensor (c d : DClass G) : DClass G :=
  Quotient.lift₂ (fun Γ Δ : FinDiag G => mk (Γ.2.tensor Δ.2))
    (fun _ _ _ _ h h' => (show Nonempty (Iso _ _) from h).elim fun i =>
      (show Nonempty (Iso _ _) from h').elim fun k => mk_eq_mk (i.tensor k)) c d

theorem mk_tensor (Γ : Diagram G N E) [Finite N] [Finite E] (Δ : Diagram G N' E')
    [Finite N'] [Finite E'] : (mk Γ).tensor (mk Δ) = mk (Γ.tensor Δ) :=
  mk_eq_mk (Γ.isoToFin.symm.tensor Δ.isoToFin.symm)

/-- *Section 2.* The composite of classes, represented by gluing; it is meaningful when
the codomain of the first is the domain of the second (otherwise it is the first
class, by convention). -/
noncomputable def comp (c d : DClass G) : DClass G := by
  classical
  exact Quotient.lift₂
    (fun Γ Δ : FinDiag G => if h : Γ.2.codWord = Δ.2.domWord then mk (Γ.2.glue Δ.2 h) else mk Γ.2)
    (fun a b a' b' h h' => (show Nonempty (Iso _ _) from h).elim fun i =>
      (show Nonempty (Iso _ _) from h').elim fun k => by
        have e₁ : a'.2.codWord = a.2.codWord := i.codWord_eq
        have e₂ : b'.2.domWord = b.2.domWord := k.domWord_eq
        by_cases hab : a.2.codWord = b.2.domWord
        · rw [dite_eq_left hab, dite_eq_left (by rw [e₁, e₂]; exact hab)]
          exact mk_eq_mk (i.glue k _ _)
        · rw [dite_eq_right hab, dite_eq_right (by rw [e₁, e₂]; exact hab)]
          exact mk_eq_mk i) c d

theorem mk_comp (Γ : Diagram G N E) [Finite N] [Finite E] (Δ : Diagram G N' E')
    [Finite N'] [Finite E'] (h : Γ.codWord = Δ.domWord) :
    (mk Γ).comp (mk Δ) = mk (Γ.glue Δ h) := by
  classical
  have h' : Γ.toFin.codWord = Δ.toFin.domWord := by
    rw [Γ.isoToFin.codWord_eq, Δ.isoToFin.domWord_eq, h]
  change (if h : Γ.toFin.codWord = Δ.toFin.domWord then mk (Γ.toFin.glue Δ.toFin h)
    else mk Γ.toFin) = _
  rw [dite_eq_left h']
  exact mk_eq_mk (Γ.isoToFin.symm.glue Δ.isoToFin.symm _ _)

theorem dom_tensor (c d : DClass G) : (c.tensor d).dom = c.dom * d.dom := by
  induction c using ind with
  | h _ _ Γ => induction d using ind with
    | h _ _ Δ => rw [mk_tensor]; simp

theorem cod_tensor (c d : DClass G) : (c.tensor d).cod = c.cod * d.cod := by
  induction c using ind with
  | h _ _ Γ => induction d using ind with
    | h _ _ Δ => rw [mk_tensor]; simp

theorem dom_comp {c d : DClass G} (h : c.cod = d.dom) : (c.comp d).dom = c.dom := by
  induction c using ind with
  | h _ _ Γ => induction d using ind with
    | h _ _ Δ =>
      simp only [cod_mk, dom_mk] at h
      rw [mk_comp _ _ h]; simp

theorem cod_comp {c d : DClass G} (h : c.cod = d.dom) : (c.comp d).cod = d.cod := by
  induction c using ind with
  | h _ _ Γ => induction d using ind with
    | h _ _ Δ =>
      simp only [cod_mk, dom_mk] at h
      rw [mk_comp _ _ h]; simp

end DClass

namespace DHom

open Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-- *Section 2.* Composition in `F_s(G)`: gluing. `f.comp g` is "`g ∘ f`". -/
noncomputable def comp {a b c : FreeMonoid S} (f : DHom G a b) (g : DHom G b c) : DHom G a c :=
  ⟨f.1.comp g.1, by rw [DClass.dom_comp (f.2.2.trans g.2.1.symm), f.2.1],
    by rw [DClass.cod_comp (f.2.2.trans g.2.1.symm), g.2.2]⟩

/-- *Section 2.* The monoidal product in `F_s(G)`: disjoint union. -/
noncomputable def tensor {a b c d : FreeMonoid S} (f : DHom G a b) (g : DHom G c d) :
    DHom G (a * c) (b * d) :=
  ⟨f.1.tensor g.1, by rw [DClass.dom_tensor, f.2.1, g.2.1],
    by rw [DClass.cod_tensor, f.2.2, g.2.2]⟩

/-- *Section 2.* The identity of `F_s(G)` on the word `a`: a node-free diagram. -/
noncomputable def id (G : FreeGraphMonoid.{w, v} S) (a : FreeMonoid S) : DHom G a a :=
  ⟨DClass.mk (idD G a), by simp, by simp⟩

/-- *Section 2.* The symmetry `σ_{a,b}` of `F_s(G)`: a node-free diagram. -/
noncomputable def braid (G : FreeGraphMonoid.{w, v} S) (a b : FreeMonoid S) :
    DHom G (a * b) (b * a) :=
  ⟨DClass.mk (braidD G a b), by simp, by simp⟩

/-- The generator of `F_s(G)` given by an arrow `x` of `G`: the class of its one-node
diagram. -/
noncomputable def gen (x : G.A) : DHom G (G.s x) (G.t x) :=
  ⟨DClass.mk (oneNode x), by simp, by simp⟩

@[simp] theorem comp_val {a b c : FreeMonoid S} (f : DHom G a b) (g : DHom G b c) :
    (f.comp g).1 = f.1.comp g.1 := rfl

@[simp] theorem tensor_val {a b c d : FreeMonoid S} (f : DHom G a b) (g : DHom G c d) :
    (f.tensor g).1 = f.1.tensor g.1 := rfl

end DHom

end FreeMarkov
