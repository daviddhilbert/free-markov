/-
Free Markov categories, Stage 2: tools for the surgery of Section 3.

* `PDiagram`: a polarized graph with a valuation, not anchored (the graphs `Ω`, `Λ` of
  a template and the subgraphs `Γ'` of Section 3 are of this kind), with isomorphisms.
* Enumerations: transport along a bijection, images, existence for finite types; a
  bijection carrying one ordering to another is the position-by-position matching.
* `Λ ⊎ R` (`addLoose`): a graph with a set `R` of loose edges added; the induced
  bijections `dom(Λ ⊎ R) → dom(Ω ⊎ R)` from `α : dom(Λ) → dom(Ω)`.
* The codomain of a glued graph is that of its second piece (`glueCodEquiv`).
* The three-piece gluing `three m₁ m₂` of `A`, `K`, `C` along bijections
  `m₁ : cod(A) → dom(K)`, `m₂ : cod(K) → dom(C)` ("more precisely" paragraph of
  Section 3), with the maps `rA`, `rK`, `rC` sending the edges of the pieces to the
  edges of the glued graph, and its anchored and valued versions.
* The comparison principle `PGraph.Iso.ofProj`: two graphs are isomorphic when both
  map injectively onto the same sets with the same ordered inputs and outputs.  All
  the isomorphisms of Section 3 are obtained this way.
-/
module

public import FreeMarkov.Stage2.Normal

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀

namespace FreeMarkov

open Relation

/-! ### Diagrams that are not anchored -/

/-- A polarized graph with a valuation in a free graph monoid, not anchored: the
diagrams `(Ω, u)`, `(Λ, w)` of a template and `(Γ', v')` of Section 3. -/
structure PDiagram {S : Type w} (G : FreeGraphMonoid.{w, v} S) (N : Type u₁) (E : Type u₂)
    extends PGraph N E where
  /-- The valuation. -/
  val : Valuation G ins outs

/-- An isomorphism of diagrams that are not anchored (Definition 2.1). -/
structure PDiagram.Iso {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
    {N' : Type u₃} {E' : Type u₄} (Γ : PDiagram G N E) (Γ' : PDiagram G N' E') extends
    toPIso : PGraph.Iso Γ.toPGraph Γ'.toPGraph where
  v₀_map (e : E) : Γ'.val.v₀ (eE e) = Γ.val.v₀ e
  v₁_map (x : N) : Γ'.val.v₁ (eN x) = Γ.val.v₁ x

namespace PDiagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄} {N'' : Type u₅} {E'' : Type u₆}

namespace Iso

variable {Γ : PDiagram G N E} {Γ' : PDiagram G N' E'} {Γ'' : PDiagram G N'' E''}

/-- The identity isomorphism. -/
def refl (Γ : PDiagram G N E) : Γ.Iso Γ where
  toPIso := PGraph.Iso.refl _
  v₀_map _ := rfl
  v₁_map _ := rfl

/-- The inverse isomorphism. -/
def symm (i : Γ.Iso Γ') : Γ'.Iso Γ where
  toPIso := i.toPIso.symm
  v₀_map e := by
    change Γ.val.v₀ (i.eE.symm e) = _
    rw [← i.v₀_map, Equiv.apply_symm_apply]
  v₁_map x := by
    change Γ.val.v₁ (i.eN.symm x) = _
    rw [← i.v₁_map, Equiv.apply_symm_apply]

/-- The composite isomorphism. -/
def trans (i : Γ.Iso Γ') (k : Γ'.Iso Γ'') : Γ.Iso Γ'' where
  toPIso := i.toPIso.trans k.toPIso
  v₀_map e := by
    change Γ''.val.v₀ (k.eE (i.eE e)) = _
    rw [k.v₀_map, i.v₀_map]
  v₁_map x := by
    change Γ''.val.v₁ (k.eN (i.eN x)) = _
    rw [k.v₁_map, i.v₁_map]

end Iso

/-- Anchoring a diagram by total orderings of its domain and codomain. -/
def anchor (Γ : PDiagram G N E) (d : Enumeration Γ.IsDom) (c : Enumeration Γ.IsCod) :
    Diagram G N E where
  toAGraph := AGraph.ofPGraph Γ.toPGraph d c
  val := Γ.val

end PDiagram

/-- An anchored diagram, forgetting the anchoring. -/
abbrev Diagram.toPDiagram {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
    (Γ : Diagram G N E) : PDiagram G N E := ⟨Γ.toPGraph, Γ.val⟩

/-! ### Enumerations -/

namespace Enumeration

variable {E : Type u₂} {E' : Type u₃} {P : E → Prop} {P' : E' → Prop}

/-- The same ordering, for an equivalent predicate. -/
def congr (o : Enumeration P) {Q : E → Prop} (h : ∀ e, P e ↔ Q e) : Enumeration Q :=
  ⟨o.list, o.nodup, fun e => (o.mem_iff e).trans (h e)⟩

/-- The enumerated elements, as elements of the subtype. -/
def sub (o : Enumeration P) : List {e // P e} := o.list.pmap Subtype.mk fun _ h => o.mem_of_mem h

theorem sub_map_val (o : Enumeration P) : o.sub.map Subtype.val = o.list := by
  simp [sub, List.map_pmap]

theorem mem_sub (o : Enumeration P) (x : {e // P e}) : x ∈ o.sub := by
  rw [sub, List.mem_pmap]
  exact ⟨x.1, (o.mem_iff x.1).2 x.2, rfl⟩

theorem nodup_sub (o : Enumeration P) : o.sub.Nodup := by
  have := o.nodup
  rw [← o.sub_map_val] at this
  exact this.of_map _

/-- The ordering transported along a bijection `σ`. -/
def mapEquiv (o : Enumeration P) (σ : {e // P e} ≃ {e' // P' e'}) : Enumeration P' where
  list := (o.sub.map σ).map Subtype.val
  nodup := (o.nodup_sub.map σ.injective).map Subtype.val_injective
  mem_iff e := by
    simp only [List.map_map, List.mem_map, Function.comp_apply]
    constructor
    · rintro ⟨x, -, rfl⟩
      exact (σ x).2
    · intro h
      exact ⟨σ.symm ⟨e, h⟩, o.mem_sub _, by simp⟩

theorem mapEquiv_length (o : Enumeration P) (σ : {e // P e} ≃ {e' // P' e'}) :
    (o.mapEquiv σ).list.length = o.list.length := by
  simp [mapEquiv, ← o.sub_map_val]

/-- A bijection that carries one ordering to another is the position-by-position
matching. -/
theorem matching_mapEquiv (o : Enumeration P) (σ : {e // P e} ≃ {e' // P' e'})
    (h : o.list.length = (o.mapEquiv σ).list.length) : o.matching (o.mapEquiv σ) h = σ := by
  ext x
  obtain ⟨i, hi, hx⟩ := List.getElem_of_mem ((o.mem_iff x.1).2 x.2)
  have hx' : x = ⟨o.list[i], o.mem_of_mem (List.getElem_mem _)⟩ := Subtype.ext hx.symm
  rw [hx', matching_getElem]
  simp only [mapEquiv, List.getElem_map]
  congr 2
  refine Subtype.ext ?_
  have : (o.sub[i]'(by rw [← o.sub_map_val] at hi; simpa using hi)).1 = o.list[i] := by
    have := congrArg (fun l => l[i]?) o.sub_map_val
    simp only [List.getElem?_map] at this
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem] at this
    · simpa using this
  exact this

/-- The image of an ordering under an injective map. -/
def image (o : Enumeration P) (f : E → E') (hf : Function.Injective f) (Q : E' → Prop)
    (hQ : ∀ e', Q e' ↔ ∃ e, P e ∧ f e = e') : Enumeration Q where
  list := o.list.map f
  nodup := o.nodup.map hf
  mem_iff e' := by
    rw [List.mem_map, hQ]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, o.mem_of_mem he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, (o.mem_iff e).2 he, rfl⟩

/-- An ordering of a set followed by an ordering of a disjoint set. -/
def append (o : Enumeration P) {Q : E → Prop} (o' : Enumeration Q) (h : ∀ e, P e → ¬ Q e) :
    Enumeration fun e => P e ∨ Q e where
  list := o.list ++ o'.list
  nodup := List.nodup_append.2 ⟨o.nodup, o'.nodup, fun a ha b hb hab => by
    subst hab
    exact h a (o.mem_of_mem ha) (o'.mem_of_mem hb)⟩
  mem_iff e := by rw [List.mem_append, o.mem_iff, o'.mem_iff]

/-- Every set of elements of a finite type has an ordering. -/
noncomputable def ofFinite [Finite E] (P : E → Prop) : Enumeration P where
  list := (List.finRange (Nat.card {e // P e})).map fun i => ((Finite.equivFin _).symm i).1
  nodup := (List.nodup_finRange _).map (by
    intro i j h
    exact (Finite.equivFin {e // P e}).symm.injective (Subtype.ext h))
  mem_iff e := by
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Finite.equivFin _).symm i).2
    · intro h
      exact ⟨Finite.equivFin _ ⟨e, h⟩, by simp⟩

end Enumeration

/-! ### Adding loose edges -/

namespace PGraph

variable {N : Type u₁} {E : Type u₂}

/-- `Λ ⊎ R`: the graph `Λ` with the elements of `R` added as loose edges. -/
def addLoose (Λ : PGraph N E) (R : Type u₃) : PGraph N (E ⊕ R) where
  src := Sum.elim Λ.src fun _ => none
  tgt := Sum.elim Λ.tgt fun _ => none
  ins x := (Λ.ins x).map .inl
  outs x := (Λ.outs x).map .inl
  ins_nodup x := (Λ.ins_nodup x).map Sum.inl_injective
  outs_nodup x := (Λ.outs_nodup x).map Sum.inl_injective
  mem_ins x e := by cases e <;> simp [Λ.mem_ins]
  mem_outs x e := by cases e <;> simp [Λ.mem_outs]
  acyclic x h := by
    refine Λ.acyclic x (transGen_map id (fun a b hab => ?_) h)
    obtain ⟨e, he₁, he₂⟩ := hab
    cases e with
    | inl d => exact ⟨d, he₁, he₂⟩
    | inr r => simp at he₁

variable (Λ : PGraph N E) (R : Type u₃)

@[simp] theorem addLoose_src_inl (d : E) : (Λ.addLoose R).src (.inl d) = Λ.src d := rfl
@[simp] theorem addLoose_src_inr (r : R) : (Λ.addLoose R).src (.inr r) = none := rfl
@[simp] theorem addLoose_tgt_inl (d : E) : (Λ.addLoose R).tgt (.inl d) = Λ.tgt d := rfl
@[simp] theorem addLoose_tgt_inr (r : R) : (Λ.addLoose R).tgt (.inr r) = none := rfl
@[simp] theorem addLoose_ins (x : N) : (Λ.addLoose R).ins x = (Λ.ins x).map .inl := rfl
@[simp] theorem addLoose_outs (x : N) : (Λ.addLoose R).outs x = (Λ.outs x).map .inl := rfl

/-- `dom(Λ ⊎ R) = dom(Λ) ⊎ R`. -/
def addLooseDom : {e // (Λ.addLoose R).IsDom e} ≃ {e // Λ.IsDom e} ⊕ R where
  toFun e := match e with
    | ⟨.inl d, h⟩ => .inl ⟨d, h⟩
    | ⟨.inr r, _⟩ => .inr r
  invFun := Sum.elim (fun d => ⟨.inl d.1, d.2⟩) (fun r => ⟨.inr r, rfl⟩)
  left_inv := by rintro ⟨d | r, h⟩ <;> rfl
  right_inv := by rintro (d | r) <;> rfl

/-- `cod(Λ ⊎ R) = cod(Λ) ⊎ R`. -/
def addLooseCod : {e // (Λ.addLoose R).IsCod e} ≃ {e // Λ.IsCod e} ⊕ R where
  toFun e := match e with
    | ⟨.inl d, h⟩ => .inl ⟨d, h⟩
    | ⟨.inr r, _⟩ => .inr r
  invFun := Sum.elim (fun d => ⟨.inl d.1, d.2⟩) (fun r => ⟨.inr r, rfl⟩)
  left_inv := by rintro ⟨d | r, h⟩ <;> rfl
  right_inv := by rintro (d | r) <;> rfl

variable {Λ R} {N' : Type u₄} {E' : Type u₅} {Ω : PGraph N' E'}

/-- The bijection `dom(Λ ⊎ R) → dom(Ω ⊎ R)` given by `α` and the identity on `R`. -/
def liftDom (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (R : Type u₃) :
    {e // (Λ.addLoose R).IsDom e} ≃ {e // (Ω.addLoose R).IsDom e} :=
  (Λ.addLooseDom R).trans ((Equiv.sumCongr α (Equiv.refl R)).trans (Ω.addLooseDom R).symm)

/-- The bijection `cod(Λ ⊎ R) → cod(Ω ⊎ R)` given by `β` and the identity on `R`. -/
def liftCod (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}) (R : Type u₃) :
    {e // (Λ.addLoose R).IsCod e} ≃ {e // (Ω.addLoose R).IsCod e} :=
  (Λ.addLooseCod R).trans ((Equiv.sumCongr β (Equiv.refl R)).trans (Ω.addLooseCod R).symm)

@[simp] theorem liftDom_inl (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (d : E)
    (h : (Λ.addLoose R).IsDom (.inl d)) : (liftDom α R ⟨.inl d, h⟩).1 = .inl (α ⟨d, h⟩).1 := rfl

@[simp] theorem liftDom_inr (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (r : R)
    (h : (Λ.addLoose R).IsDom (.inr r)) : (liftDom α R ⟨.inr r, h⟩).1 = .inr r := rfl

@[simp] theorem liftCod_inl (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}) (d : E)
    (h : (Λ.addLoose R).IsCod (.inl d)) : (liftCod β R ⟨.inl d, h⟩).1 = .inl (β ⟨d, h⟩).1 := rfl

@[simp] theorem liftCod_inr (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}) (r : R)
    (h : (Λ.addLoose R).IsCod (.inr r)) : (liftCod β R ⟨.inr r, h⟩).1 = .inr r := rfl

theorem liftDom_symm (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) :
    (liftDom α R).symm = liftDom α.symm R := by
  ext ⟨d | r, h⟩ <;> rfl

theorem liftCod_symm (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}) :
    (liftCod β R).symm = liftCod β.symm R := by
  ext ⟨d | r, h⟩ <;> rfl

end PGraph

namespace Valuation

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

/-- The valuation of `Λ ⊎ R`: `w` on `Λ` and the labels `r` on `R`. -/
def addLoose {Λ : PGraph N E} (w : Valuation G Λ.ins Λ.outs) {R : Type u₃} (r : R → S) :
    Valuation G (Λ.addLoose R).ins (Λ.addLoose R).outs where
  v₀ := Sum.elim w.v₀ r
  v₁ := w.v₁
  s_v₁ x := by simp [w.s_v₁, Function.comp_def]
  t_v₁ x := by simp [w.t_v₁, Function.comp_def]

end Valuation

namespace PDiagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

/-- `(Λ ⊎ R, w ⊎ r)`. -/
abbrev addLoose (Λ : PDiagram G N E) {R : Type u₃} (r : R → S) : PDiagram G N (E ⊕ R) :=
  ⟨Λ.toPGraph.addLoose R, Λ.val.addLoose r⟩

end PDiagram

/-! ### The codomain of a glued graph -/

namespace PGraph

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}
  {Γ : PGraph N E} {Ω : PGraph N' E'}

theorem glue_tgt_glueIn (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e}) (e : E') :
    (PGraph.glue m).tgt (glueIn m e) = (Ω.tgt e).map .inr := by
  by_cases h : Ω.src e = none
  · rw [glueIn_of_eq_none m h, glue_tgt_inl]
    unfold glueTgt
    rw [dite_eq_left (m.symm ⟨e, h⟩).2]
    simp
  · rw [glueIn_of_ne_none m h, glue_tgt_inr]

theorem glue_src_glueIn_of_ne (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e}) {e : E'}
    (h : Ω.src e ≠ none) : (PGraph.glue m).src (glueIn m e) = (Ω.src e).map .inr := by
  rw [glueIn_of_ne_none m h, glue_src_inr]

/-- The codomain of the glued graph is the codomain of the second piece. -/
noncomputable def glueCodEquiv (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e}) :
    {e // Ω.IsCod e} ≃ {e // (PGraph.glue m).IsCod e} :=
  Equiv.ofBijective (fun e => ⟨glueIn m e.1, by
      change (PGraph.glue m).tgt _ = none
      rw [glue_tgt_glueIn, e.2]; rfl⟩)
    ⟨fun a b h => Subtype.ext (glueIn_injective m (congrArg Subtype.val h)), by
      rintro ⟨e | b, he⟩
      · change glueTgt m e = none at he
        obtain ⟨h, h'⟩ := (glueTgt_eq_none_iff m e).1 he
        refine ⟨⟨(m ⟨e, h⟩).1, h'⟩, Subtype.ext ?_⟩
        change glueIn m _ = _
        rw [glueIn_of_eq_none m (m ⟨e, h⟩).2]
        simp
      · change (Ω.tgt b.1).map Sum.inr = none at he
        refine ⟨⟨b.1, by simpa using he⟩, Subtype.ext ?_⟩
        change glueIn m _ = _
        rw [glueIn_of_ne_none m b.2]⟩

@[simp] theorem glueCodEquiv_val (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e})
    (e : {e // Ω.IsCod e}) : (glueCodEquiv m e).1 = glueIn m e.1 := rfl

/-! ### The three-piece gluing -/

variable {NA : Type u₁} {EA : Type u₂} {NK : Type u₃} {EK : Type u₄} {NC : Type u₅}
  {EC : Type u₆} {A : PGraph NA EA} {K : PGraph NK EK} {C : PGraph NC EC}

/-- The bijection `cod(A ∪ K) → dom(C)` given by `m₂ : cod(K) → dom(C)`. -/
noncomputable def threeMatch (m₁ : {e // A.IsCod e} ≃ {e // K.IsDom e})
    (m₂ : {e // K.IsCod e} ≃ {e // C.IsDom e}) :
    {e // (PGraph.glue m₁).IsCod e} ≃ {e // C.IsDom e} :=
  (glueCodEquiv m₁).symm.trans m₂

/-- **The three-piece gluing** ("more precisely" paragraph of Section 3): the graph
obtained from the disjoint union of `A`, `K`, `C` by gluing `cod(A)` to `dom(K)` along
`m₁` and `cod(K)` to `dom(C)` along `m₂`, in the same way as in the composition of
`F_s(G)`. -/
noncomputable def three (m₁ : {e // A.IsCod e} ≃ {e // K.IsDom e})
    (m₂ : {e // K.IsCod e} ≃ {e // C.IsDom e}) :
    PGraph ((NA ⊕ NK) ⊕ NC) ((EA ⊕ K.InnerSrc) ⊕ C.InnerSrc) :=
  PGraph.glue (threeMatch m₁ m₂)

variable (m₁ : {e // A.IsCod e} ≃ {e // K.IsDom e}) (m₂ : {e // K.IsCod e} ≃ {e // C.IsDom e})

/-- An edge of `A` as an edge of the three-piece gluing. -/
def rA (a : EA) : (EA ⊕ K.InnerSrc) ⊕ C.InnerSrc := .inl (.inl a)

/-- An edge of `K` as an edge of the three-piece gluing (a domain edge of `K` is
identified with the edge of `A` it is glued to). -/
noncomputable def rK (k : EK) : (EA ⊕ K.InnerSrc) ⊕ C.InnerSrc := .inl (glueIn m₁ k)

/-- An edge of `C` as an edge of the three-piece gluing. -/
noncomputable def rC (c : EC) : (EA ⊕ K.InnerSrc) ⊕ C.InnerSrc := glueIn (threeMatch m₁ m₂) c

variable {m₁ m₂}

theorem three_ins_A (x : NA) : (three m₁ m₂).ins (.inl (.inl x)) = (A.ins x).map (rA (K := K) (C := C)) := by
  simp [three, rA, List.map_map, Function.comp_def]

theorem three_ins_K (y : NK) : (three m₁ m₂).ins (.inl (.inr y)) = (K.ins y).map (rK (C := C) m₁) := by
  simp [three, rK, List.map_map, Function.comp_def]

theorem three_ins_C (z : NC) : (three m₁ m₂).ins (.inr z) = (C.ins z).map (rC m₁ m₂) := by
  simp [three, rC]

theorem three_outs_A (x : NA) : (three m₁ m₂).outs (.inl (.inl x)) = (A.outs x).map (rA (K := K) (C := C)) := by
  simp [three, rA, List.map_map, Function.comp_def]

theorem three_outs_K (y : NK) : (three m₁ m₂).outs (.inl (.inr y)) = (K.outs y).map (rK (C := C) m₁) := by
  simp [three, rK, List.map_map, Function.comp_def]

theorem three_outs_C (z : NC) : (three m₁ m₂).outs (.inr z) = (C.outs z).map (rC m₁ m₂) := by
  simp [three, rC]

theorem rK_of_src_eq_none {k : EK} (h : K.src k = none) :
    rK (C := C) m₁ k = rA (m₁.symm ⟨k, h⟩).1 := by
  simp [rK, rA, glueIn_of_eq_none m₁ h]

theorem rK_of_src_ne_none {k : EK} (h : K.src k ≠ none) :
    rK (C := C) m₁ k = .inl (.inr ⟨k, h⟩) := by
  simp [rK, glueIn_of_ne_none m₁ h]

theorem rC_of_src_eq_none {c : EC} (h : C.src c = none) :
    rC m₁ m₂ c = rK m₁ (m₂.symm ⟨c, h⟩).1 := by
  rw [rC, glueIn_of_eq_none _ h]
  rfl

theorem rC_of_src_ne_none {c : EC} (h : C.src c ≠ none) : rC m₁ m₂ c = .inr ⟨c, h⟩ := by
  rw [rC, glueIn_of_ne_none _ h]

theorem rA_injective : Function.Injective (rA (EA := EA) (K := K) (C := C)) := by
  intro a b h
  simpa [rA] using h

theorem rK_injective : Function.Injective (rK (C := C) m₁) := by
  intro a b h
  exact glueIn_injective m₁ (Sum.inl_injective h)

theorem rC_injective : Function.Injective (rC m₁ m₂) := glueIn_injective _

theorem eq_of_rA_eq_rK {a : EA} {k : EK} (h : rA a = rK (C := C) m₁ k) :
    ∃ hk : K.src k = none, a = (m₁.symm ⟨k, hk⟩).1 := by
  by_cases hk : K.src k = none
  · rw [rK_of_src_eq_none hk] at h
    exact ⟨hk, rA_injective h⟩
  · rw [rK_of_src_ne_none hk] at h
    simp [rA] at h

theorem eq_of_rK_eq_rC {k : EK} {c : EC} (h : rK m₁ k = rC m₁ m₂ c) :
    ∃ hc : C.src c = none, k = (m₂.symm ⟨c, hc⟩).1 := by
  by_cases hc : C.src c = none
  · rw [rC_of_src_eq_none hc] at h
    exact ⟨hc, rK_injective h⟩
  · rw [rC_of_src_ne_none hc] at h
    simp [rK] at h

theorem rA_ne_rC_of_src_ne_none {a : EA} {c : EC} (hc : C.src c ≠ none) :
    rA (K := K) a ≠ rC m₁ m₂ c := by
  rw [rC_of_src_ne_none hc]
  simp [rA]

theorem rK_ne_rC_of_src_ne_none {k : EK} {c : EC} (hc : C.src c ≠ none) :
    rK m₁ k ≠ rC m₁ m₂ c := by
  rw [rC_of_src_ne_none hc]
  simp [rK]

/-- Every edge of the three-piece gluing comes from one of the pieces. -/
theorem three_edge_cases (e : (EA ⊕ K.InnerSrc) ⊕ C.InnerSrc) :
    (∃ a, e = rA a) ∨ (∃ k, K.src k ≠ none ∧ e = rK (C := C) m₁ k) ∨
      (∃ c, C.src c ≠ none ∧ e = rC m₁ m₂ c) := by
  rcases e with (a | b) | c
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr (Or.inl ⟨b.1, b.2, (rK_of_src_ne_none b.2).symm⟩)
  · exact Or.inr (Or.inr ⟨c.1, c.2, (rC_of_src_ne_none c.2).symm⟩)

theorem three_src_rA (a : EA) : (three m₁ m₂).src (rA a) = (A.src a).map (.inl ∘ .inl) := by
  simp [three, rA, Function.comp_def]

theorem three_tgt_rC (c : EC) : (three m₁ m₂).tgt (rC m₁ m₂ c) = (C.tgt c).map .inr :=
  glue_tgt_glueIn _ c

/-- The domain of the three-piece gluing is the domain of `A`. -/
theorem three_isDom_iff (e : (EA ⊕ K.InnerSrc) ⊕ C.InnerSrc) :
    (three m₁ m₂).IsDom e ↔ ∃ a, A.src a = none ∧ rA a = e := by
  constructor
  · intro h
    rcases e with (a | b) | c
    · exact ⟨a, by simpa [three, IsDom] using h, rfl⟩
    · exfalso
      exact b.2 (by simpa [three, IsDom] using h)
    · exfalso
      exact c.2 (by simpa [three, IsDom] using h)
  · rintro ⟨a, ha, rfl⟩
    change (three m₁ m₂).src (rA a) = none
    rw [three_src_rA, ha]
    rfl

/-- The codomain of the three-piece gluing is the codomain of `C`. -/
theorem three_isCod_iff (e : (EA ⊕ K.InnerSrc) ⊕ C.InnerSrc) :
    (three m₁ m₂).IsCod e ↔ ∃ c, C.tgt c = none ∧ rC m₁ m₂ c = e := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (glueCodEquiv (threeMatch m₁ m₂)).surjective ⟨e, h⟩
    exact ⟨c.1, c.2, congrArg Subtype.val hc⟩
  · rintro ⟨c, hc, rfl⟩
    exact (glueCodEquiv (threeMatch m₁ m₂) ⟨c, hc⟩).2

variable (m₁ m₂)

/-- The anchored three-piece gluing: the domain is that of `A`, the codomain that of
`C`, in the given orderings. -/
noncomputable def threeA (dA : Enumeration A.IsDom) (cC : Enumeration C.IsCod) :
    AGraph ((NA ⊕ NK) ⊕ NC) ((EA ⊕ K.InnerSrc) ⊕ C.InnerSrc) :=
  AGraph.ofPGraph (three m₁ m₂) (dA.image rA rA_injective _ three_isDom_iff)
    (cC.image (rC m₁ m₂) rC_injective _ three_isCod_iff)

theorem threeA_dom (dA : Enumeration A.IsDom) (cC : Enumeration C.IsCod) :
    (threeA m₁ m₂ dA cC).dom = dA.list.map rA := rfl

theorem threeA_cod (dA : Enumeration A.IsDom) (cC : Enumeration C.IsCod) :
    (threeA m₁ m₂ dA cC).cod = cC.list.map (rC m₁ m₂) := rfl

theorem threeA_toPGraph (dA : Enumeration A.IsDom) (cC : Enumeration C.IsCod) :
    (threeA m₁ m₂ dA cC).toPGraph = three m₁ m₂ := rfl

end PGraph

namespace Valuation

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}
  {NA : Type u₁} {EA : Type u₂} {NK : Type u₃} {EK : Type u₄} {NC : Type u₅}
  {EC : Type u₆} {A : PGraph NA EA} {K : PGraph NK EK} {C : PGraph NC EC}
  {m₁ : {e // A.IsCod e} ≃ {e // K.IsDom e}} {m₂ : {e // K.IsCod e} ≃ {e // C.IsDom e}}

theorem threeMatch_v₀ (vA : Valuation G A.ins A.outs) (vK : Valuation G K.ins K.outs)
    (vC : Valuation G C.ins C.outs) (h₁ : ∀ c, vK.v₀ (m₁ c).1 = vA.v₀ c.1)
    (h₂ : ∀ c, vC.v₀ (m₂ c).1 = vK.v₀ c.1) (c : {e // (PGraph.glue m₁).IsCod e}) :
    vC.v₀ (PGraph.threeMatch m₁ m₂ c).1 = (Valuation.glue m₁ vA vK h₁).v₀ c.1 := by
  obtain ⟨k, rfl⟩ := (PGraph.glueCodEquiv m₁).surjective c
  simp only [PGraph.threeMatch, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [h₂]
  exact (glueIn_v₀ m₁ vA vK h₁ k.1).symm

/-- The valuation of the three-piece gluing, from valuations of the pieces that agree
on the glued edges. -/
noncomputable def three (vA : Valuation G A.ins A.outs) (vK : Valuation G K.ins K.outs)
    (vC : Valuation G C.ins C.outs) (h₁ : ∀ c, vK.v₀ (m₁ c).1 = vA.v₀ c.1)
    (h₂ : ∀ c, vC.v₀ (m₂ c).1 = vK.v₀ c.1) :
    Valuation G (PGraph.three m₁ m₂).ins (PGraph.three m₁ m₂).outs :=
  Valuation.glue (PGraph.threeMatch m₁ m₂) (Valuation.glue m₁ vA vK h₁) vC
    (threeMatch_v₀ vA vK vC h₁ h₂)

variable (vA : Valuation G A.ins A.outs) (vK : Valuation G K.ins K.outs)
  (vC : Valuation G C.ins C.outs) (h₁ : ∀ c, vK.v₀ (m₁ c).1 = vA.v₀ c.1)
  (h₂ : ∀ c, vC.v₀ (m₂ c).1 = vK.v₀ c.1)

theorem three_v₀_rA (a : EA) : (three vA vK vC h₁ h₂).v₀ (PGraph.rA a) = vA.v₀ a := rfl

theorem three_v₀_rK (k : EK) : (three vA vK vC h₁ h₂).v₀ (PGraph.rK m₁ k) = vK.v₀ k :=
  glueIn_v₀ m₁ vA vK h₁ k

theorem three_v₀_rC (c : EC) : (three vA vK vC h₁ h₂).v₀ (PGraph.rC m₁ m₂ c) = vC.v₀ c :=
  glueIn_v₀ _ _ vC (threeMatch_v₀ vA vK vC h₁ h₂) c

theorem three_v₁_A (x : NA) : (three vA vK vC h₁ h₂).v₁ (.inl (.inl x)) = vA.v₁ x := rfl

theorem three_v₁_K (y : NK) : (three vA vK vC h₁ h₂).v₁ (.inl (.inr y)) = vK.v₁ y := rfl

theorem three_v₁_C (z : NC) : (three vA vK vC h₁ h₂).v₁ (.inr z) = vC.v₁ z := rfl

end Valuation

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}
  {NA : Type u₁} {EA : Type u₂} {NK : Type u₃} {EK : Type u₄} {NC : Type u₅} {EC : Type u₆}

/-- The anchored and valued three-piece gluing. -/
noncomputable def three (A : PDiagram G NA EA) (K : PDiagram G NK EK) (C : PDiagram G NC EC)
    (m₁ : {e // A.IsCod e} ≃ {e // K.IsDom e}) (m₂ : {e // K.IsCod e} ≃ {e // C.IsDom e})
    (h₁ : ∀ c, K.val.v₀ (m₁ c).1 = A.val.v₀ c.1) (h₂ : ∀ c, C.val.v₀ (m₂ c).1 = K.val.v₀ c.1)
    (dA : Enumeration A.IsDom) (cC : Enumeration C.IsCod) :
    Diagram G ((NA ⊕ NK) ⊕ NC) ((EA ⊕ K.InnerSrc) ⊕ C.InnerSrc) where
  toAGraph := PGraph.threeA m₁ m₂ dA cC
  val := Valuation.three A.val K.val C.val h₁ h₂

end Diagram

/-! ### The comparison principle -/

/-- The element of `β` with the same image as `a`. -/
noncomputable def projChoose {α : Type u₁} {β : Type u₂} {T : Type u₃} (p : α → T) (q : β → T)
    (h : ∀ t, (∃ a, p a = t) ↔ ∃ b, q b = t) (a : α) : β :=
  Classical.choose ((h (p a)).1 ⟨a, rfl⟩)

theorem projChoose_spec {α : Type u₁} {β : Type u₂} {T : Type u₃} (p : α → T) (q : β → T)
    (h : ∀ t, (∃ a, p a = t) ↔ ∃ b, q b = t) (a : α) : q (projChoose p q h a) = p a :=
  Classical.choose_spec ((h (p a)).1 ⟨a, rfl⟩)

/-- The bijection between two types that map injectively onto the same subset of a
third. -/
noncomputable def equivOfProj {α : Type u₁} {β : Type u₂} {T : Type u₃} (p : α → T) (q : β → T)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (h : ∀ t, (∃ a, p a = t) ↔ ∃ b, q b = t) : α ≃ β :=
  Equiv.ofBijective (projChoose p q h)
    ⟨fun a a' haa' => hp (by rw [← projChoose_spec p q h a, ← projChoose_spec p q h a', haa']),
      fun b => by
        obtain ⟨a, ha⟩ := (h (q b)).2 ⟨b, rfl⟩
        exact ⟨a, hq (by rw [projChoose_spec p q h a, ha])⟩⟩

theorem equivOfProj_spec {α : Type u₁} {β : Type u₂} {T : Type u₃} (p : α → T) (q : β → T)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (h : ∀ t, (∃ a, p a = t) ↔ ∃ b, q b = t) (a : α) :
    q (equivOfProj p q hp hq h a) = p a :=
  projChoose_spec p q h a

namespace PGraph.Iso

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄} {TN : Type u₅} {TE : Type u₆}
  {X : PGraph N E} {Y : PGraph N' E'}

/-- **Comparison principle.** If the nodes and edges of `X` and of `Y` map injectively
onto the same sets, compatibly with the ordered inputs and outputs, then `X ≅ Y`. -/
noncomputable def ofProj (pN : N → TN) (pE : E → TE) (qN : N' → TN) (qE : E' → TE)
    (hpN : Function.Injective pN) (hqN : Function.Injective qN)
    (hpE : Function.Injective pE) (hqE : Function.Injective qE)
    (hN : ∀ t, (∃ n, pN n = t) ↔ ∃ n', qN n' = t) (hE : ∀ t, (∃ e, pE e = t) ↔ ∃ e', qE e' = t)
    (hins : ∀ n n', pN n = qN n' → (X.ins n).map pE = (Y.ins n').map qE)
    (houts : ∀ n n', pN n = qN n' → (X.outs n).map pE = (Y.outs n').map qE) : X.Iso Y where
  eN := equivOfProj pN qN hpN hqN hN
  eE := equivOfProj pE qE hpE hqE hE
  ins_map n := by
    refine List.map_injective_iff.2 hqE ?_
    rw [← hins n _ (equivOfProj_spec pN qN hpN hqN hN n).symm, List.map_map]
    exact List.map_congr_left fun e _ => (equivOfProj_spec pE qE hpE hqE hE e).symm
  outs_map n := by
    refine List.map_injective_iff.2 hqE ?_
    rw [← houts n _ (equivOfProj_spec pN qN hpN hqN hN n).symm, List.map_map]
    exact List.map_congr_left fun e _ => (equivOfProj_spec pE qE hpE hqE hE e).symm

theorem ofProj_eN {pN : N → TN} {pE : E → TE} {qN : N' → TN} {qE : E' → TE}
    {hpN : Function.Injective pN} {hqN : Function.Injective qN}
    {hpE : Function.Injective pE} {hqE : Function.Injective qE}
    {hN : ∀ t, (∃ n, pN n = t) ↔ ∃ n', qN n' = t} {hE : ∀ t, (∃ e, pE e = t) ↔ ∃ e', qE e' = t}
    {hins : ∀ n n', pN n = qN n' → (X.ins n).map pE = (Y.ins n').map qE}
    {houts : ∀ n n', pN n = qN n' → (X.outs n).map pE = (Y.outs n').map qE} (n : N) :
    qN ((ofProj pN pE qN qE hpN hqN hpE hqE hN hE hins houts).eN n) = pN n :=
  equivOfProj_spec pN qN hpN hqN hN n

theorem ofProj_eE {pN : N → TN} {pE : E → TE} {qN : N' → TN} {qE : E' → TE}
    {hpN : Function.Injective pN} {hqN : Function.Injective qN}
    {hpE : Function.Injective pE} {hqE : Function.Injective qE}
    {hN : ∀ t, (∃ n, pN n = t) ↔ ∃ n', qN n' = t} {hE : ∀ t, (∃ e, pE e = t) ↔ ∃ e', qE e' = t}
    {hins : ∀ n n', pN n = qN n' → (X.ins n).map pE = (Y.ins n').map qE}
    {houts : ∀ n n', pN n = qN n' → (X.outs n).map pE = (Y.outs n').map qE} (e : E) :
    qE ((ofProj pN pE qN qE hpN hqN hpE hqE hN hE hins houts).eE e) = pE e :=
  equivOfProj_spec pE qE hpE hqE hE e

end PGraph.Iso

namespace AGraph.Iso

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄} {TN : Type u₅} {TE : Type u₆}
  {X : AGraph N E} {Y : AGraph N' E'}

/-- The comparison principle for anchored graphs. -/
noncomputable def ofProj (pN : N → TN) (pE : E → TE) (qN : N' → TN) (qE : E' → TE)
    (hpN : Function.Injective pN) (hqN : Function.Injective qN)
    (hpE : Function.Injective pE) (hqE : Function.Injective qE)
    (hN : ∀ t, (∃ n, pN n = t) ↔ ∃ n', qN n' = t) (hE : ∀ t, (∃ e, pE e = t) ↔ ∃ e', qE e' = t)
    (hins : ∀ n n', pN n = qN n' → (X.ins n).map pE = (Y.ins n').map qE)
    (houts : ∀ n n', pN n = qN n' → (X.outs n).map pE = (Y.outs n').map qE)
    (hdom : X.dom.map pE = Y.dom.map qE) (hcod : X.cod.map pE = Y.cod.map qE) : X.Iso Y where
  toIso := PGraph.Iso.ofProj pN pE qN qE hpN hqN hpE hqE hN hE hins houts
  dom_map := by
    refine List.map_injective_iff.2 hqE ?_
    rw [← hdom, List.map_map]
    exact List.map_congr_left fun e _ => (equivOfProj_spec pE qE hpE hqE hE e).symm
  cod_map := by
    refine List.map_injective_iff.2 hqE ?_
    rw [← hcod, List.map_map]
    exact List.map_congr_left fun e _ => (equivOfProj_spec pE qE hpE hqE hE e).symm

end AGraph.Iso

namespace Diagram.Iso

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄} {TN : Type u₅} {TE : Type u₆}
  {X : Diagram G N E} {Y : Diagram G N' E'}

/-- The comparison principle for diagrams. -/
noncomputable def ofProj (pN : N → TN) (pE : E → TE) (qN : N' → TN) (qE : E' → TE)
    (hpN : Function.Injective pN) (hqN : Function.Injective qN)
    (hpE : Function.Injective pE) (hqE : Function.Injective qE)
    (hN : ∀ t, (∃ n, pN n = t) ↔ ∃ n', qN n' = t) (hE : ∀ t, (∃ e, pE e = t) ↔ ∃ e', qE e' = t)
    (hins : ∀ n n', pN n = qN n' → (X.ins n).map pE = (Y.ins n').map qE)
    (houts : ∀ n n', pN n = qN n' → (X.outs n).map pE = (Y.outs n').map qE)
    (hdom : X.dom.map pE = Y.dom.map qE) (hcod : X.cod.map pE = Y.cod.map qE)
    (hv₀ : ∀ e e', pE e = qE e' → X.val.v₀ e = Y.val.v₀ e')
    (hv₁ : ∀ n n', pN n = qN n' → X.val.v₁ n = Y.val.v₁ n') : X.Iso Y where
  toAIso := AGraph.Iso.ofProj pN pE qN qE hpN hqN hpE hqE hN hE hins houts hdom hcod
  v₀_map e := (hv₀ e _ (equivOfProj_spec pE qE hpE hqE hE e).symm).symm
  v₁_map n := (hv₁ n _ (equivOfProj_spec pN qN hpN hqN hN n).symm).symm

end Diagram.Iso

namespace PDiagram.Iso

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄} {TN : Type u₅} {TE : Type u₆}
  {X : PDiagram G N E} {Y : PDiagram G N' E'}

/-- The comparison principle for diagrams that are not anchored. -/
noncomputable def ofProj (pN : N → TN) (pE : E → TE) (qN : N' → TN) (qE : E' → TE)
    (hpN : Function.Injective pN) (hqN : Function.Injective qN)
    (hpE : Function.Injective pE) (hqE : Function.Injective qE)
    (hN : ∀ t, (∃ n, pN n = t) ↔ ∃ n', qN n' = t) (hE : ∀ t, (∃ e, pE e = t) ↔ ∃ e', qE e' = t)
    (hins : ∀ n n', pN n = qN n' → (X.ins n).map pE = (Y.ins n').map qE)
    (houts : ∀ n n', pN n = qN n' → (X.outs n).map pE = (Y.outs n').map qE)
    (hv₀ : ∀ e e', pE e = qE e' → X.val.v₀ e = Y.val.v₀ e')
    (hv₁ : ∀ n n', pN n = qN n' → X.val.v₁ n = Y.val.v₁ n') : X.Iso Y where
  toPIso := PGraph.Iso.ofProj pN pE qN qE hpN hqN hpE hqE hN hE hins houts
  v₀_map e := (hv₀ e _ (equivOfProj_spec pE qE hpE hqE hE e).symm).symm
  v₁_map n := (hv₁ n _ (equivOfProj_spec pN qN hpN hqN hN n).symm).symm

end PDiagram.Iso

end FreeMarkov

/-! ### The order on the nodes of glued graphs -/

namespace FreeMarkov

open Relation

namespace PGraph

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}
  {Γ : PGraph N E} {Ω : PGraph N' E'}

theorem glue_adj_cases (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e}) {a b : N ⊕ N'}
    (h : (PGraph.glue m).Adj a b) :
    (∃ x y, a = .inl x ∧ b = .inl y ∧ Γ.Adj x y) ∨ (∃ x y, a = .inr x ∧ b = .inr y) ∨
      (∃ x y, a = .inl x ∧ b = .inr y) := by
  obtain ⟨e, he₁, he₂⟩ := h
  rcases e with e | e
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 he₁
    rcases b with y | y
    · exact Or.inl ⟨x, y, rfl, rfl, e, hx, (glueTgt_eq_some_inl_iff m e y).1 he₂⟩
    · exact Or.inr (Or.inr ⟨x, y, rfl, rfl⟩)
  · obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 he₁
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 he₂
    exact Or.inr (Or.inl ⟨x, y, rfl, rfl⟩)

theorem glue_transGen (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e}) {a b : N ⊕ N'}
    (h : TransGen (PGraph.glue m).Adj a b) :
    (∀ x y, a = .inl x → b = .inl y → TransGen Γ.Adj x y) ∧
      (∀ x y, a = .inr x → b = .inl y → False) := by
  induction h with
  | single hab =>
    refine ⟨?_, ?_⟩ <;> rintro x y rfl rfl
    · rcases glue_adj_cases m hab with ⟨x', y', h₁, h₂, h⟩ | ⟨x', y', h₁, h₂⟩ | ⟨x', y', h₁, h₂⟩
      · cases h₁; cases h₂; exact .single h
      · cases h₁
      · cases h₂
    · rcases glue_adj_cases m hab with ⟨x', y', h₁, h₂, h⟩ | ⟨x', y', h₁, h₂⟩ | ⟨x', y', h₁, h₂⟩
      · cases h₁
      · cases h₂
      · cases h₁
  | @tail b c _ hbc ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    refine ⟨?_, ?_⟩ <;> rintro x y rfl rfl
    · rcases glue_adj_cases m hbc with ⟨z, y', h₁, h₂, h⟩ | ⟨z, y', h₁, h₂⟩ | ⟨z, y', h₁, h₂⟩
      · cases h₂; exact (ih₁ x z rfl h₁).tail h
      · cases h₂
      · cases h₂
    · rcases glue_adj_cases m hbc with ⟨z, y', h₁, h₂, h⟩ | ⟨z, y', h₁, h₂⟩ | ⟨z, y', h₁, h₂⟩
      · exact ih₂ x z rfl h₁
      · cases h₂
      · cases h₂

/-- In a glued graph no directed path leads from the second piece back into the
first. -/
theorem glue_not_lt_inr_inl (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e}) (x : N') (y : N) :
    ¬ (PGraph.glue m).Lt (.inr x) (.inl y) := fun h => (glue_transGen m h).2 x y rfl rfl

theorem glue_lt_inl_inl (m : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e}) {x y : N}
    (h : (PGraph.glue m).Lt (.inl x) (.inl y)) : Γ.Lt x y := (glue_transGen m h).1 x y rfl rfl

/-! ### Ends of the edges of a three-piece gluing -/

variable {NA : Type u₁} {EA : Type u₂} {NK : Type u₃} {EK : Type u₄} {NC : Type u₅}
  {EC : Type u₆} {A : PGraph NA EA} {K : PGraph NK EK} {C : PGraph NC EC}
  {m₁ : {e // A.IsCod e} ≃ {e // K.IsDom e}} {m₂ : {e // K.IsCod e} ≃ {e // C.IsDom e}}

theorem three_not_lt_C_left (z : NC) (n : NA ⊕ NK) : ¬ (three m₁ m₂).Lt (.inr z) (.inl n) :=
  glue_not_lt_inr_inl _ z n

theorem three_not_lt_K_A (y : NK) (x : NA) :
    ¬ (three m₁ m₂).Lt (.inl (.inr y)) (.inl (.inl x)) := fun h =>
  glue_not_lt_inr_inl m₁ y x (glue_lt_inl_inl _ h)

theorem three_src_eq_some_K_iff (e : (EA ⊕ K.InnerSrc) ⊕ C.InnerSrc) (y : NK) :
    (three m₁ m₂).src e = some (.inl (.inr y)) ↔ ∃ k, K.src k = some y ∧ rK m₁ k = e := by
  rw [← (three m₁ m₂).mem_outs, three_outs_K, List.mem_map]
  simp only [K.mem_outs]

theorem three_tgt_eq_some_K_iff (e : (EA ⊕ K.InnerSrc) ⊕ C.InnerSrc) (y : NK) :
    (three m₁ m₂).tgt e = some (.inl (.inr y)) ↔ ∃ k, K.tgt k = some y ∧ rK m₁ k = e := by
  rw [← (three m₁ m₂).mem_ins, three_ins_K, List.mem_map]
  simp only [K.mem_ins]

/-- The source of an edge of `K` in the three-piece gluing lies in `A` or `K`. -/
theorem three_src_rK_eq_some {k : EK} {n : (NA ⊕ NK) ⊕ NC}
    (h : (three m₁ m₂).src (rK m₁ k) = some n) : ∃ n', n = .inl n' := by
  by_cases hk : K.src k = none
  · rw [rK_of_src_eq_none hk, three_src_rA] at h
    obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨_, rfl⟩
  · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hk
    rw [(three_src_eq_some_K_iff _ y).2 ⟨k, hy, rfl⟩] at h
    cases h
    exact ⟨_, rfl⟩

/-- The target of an edge of `K` in the three-piece gluing lies in `K` or `C`. -/
theorem three_tgt_rK_eq_some {k : EK} {n : (NA ⊕ NK) ⊕ NC}
    (h : (three m₁ m₂).tgt (rK m₁ k) = some n) : ∀ x, n ≠ .inl (.inl x) := by
  by_cases hk : K.tgt k = none
  · have : rC m₁ m₂ (m₂ ⟨k, hk⟩).1 = rK m₁ k := by
      rw [rC_of_src_eq_none (m₂ ⟨k, hk⟩).2]
      simp
    rw [← this, three_tgt_rC] at h
    obtain ⟨z, -, rfl⟩ := Option.map_eq_some_iff.1 h
    intro x hx
    cases hx
  · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hk
    rw [(three_tgt_eq_some_K_iff _ y).2 ⟨k, hy, rfl⟩] at h
    cases h
    intro x hx
    cases hx

end PGraph

/-! ### Diagram-level facts about the three-piece gluing -/

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}
  {NA : Type u₁} {EA : Type u₂} {NK : Type u₃} {EK : Type u₄} {NC : Type u₅} {EC : Type u₆}
  {PA : PDiagram G NA EA} {K : PDiagram G NK EK} {PC : PDiagram G NC EC}
  {m₁ : {e // PA.IsCod e} ≃ {e // K.IsDom e}} {m₂ : {e // K.IsCod e} ≃ {e // PC.IsDom e}}
  {h₁ : ∀ c, K.val.v₀ (m₁ c).1 = PA.val.v₀ c.1} {h₂ : ∀ c, PC.val.v₀ (m₂ c).1 = K.val.v₀ c.1}
  {dA : Enumeration PA.IsDom} {cC : Enumeration PC.IsCod}

local notation "Y" => Diagram.three PA K PC m₁ m₂ h₁ h₂ dA cC

theorem three_ins_A (x : NA) : (Y).ins (.inl (.inl x)) = (PA.ins x).map PGraph.rA :=
  PGraph.three_ins_A x
theorem three_ins_K (y : NK) : (Y).ins (.inl (.inr y)) = (K.ins y).map (PGraph.rK m₁) :=
  PGraph.three_ins_K y
theorem three_ins_C (z : NC) : (Y).ins (.inr z) = (PC.ins z).map (PGraph.rC m₁ m₂) :=
  PGraph.three_ins_C z
theorem three_outs_A (x : NA) : (Y).outs (.inl (.inl x)) = (PA.outs x).map PGraph.rA :=
  PGraph.three_outs_A x
theorem three_outs_K (y : NK) : (Y).outs (.inl (.inr y)) = (K.outs y).map (PGraph.rK m₁) :=
  PGraph.three_outs_K y
theorem three_outs_C (z : NC) : (Y).outs (.inr z) = (PC.outs z).map (PGraph.rC m₁ m₂) :=
  PGraph.three_outs_C z
theorem three_dom : (Y).dom = dA.list.map PGraph.rA := rfl
theorem three_cod : (Y).cod = cC.list.map (PGraph.rC m₁ m₂) := rfl
theorem three_v₀_rA (a : EA) : (Y).val.v₀ (PGraph.rA a) = PA.val.v₀ a := rfl
theorem three_v₀_rK (k : EK) : (Y).val.v₀ (PGraph.rK m₁ k) = K.val.v₀ k :=
  Valuation.three_v₀_rK _ _ _ h₁ h₂ k
theorem three_v₀_rC (c : EC) : (Y).val.v₀ (PGraph.rC m₁ m₂ c) = PC.val.v₀ c :=
  Valuation.three_v₀_rC _ _ _ h₁ h₂ c
theorem three_v₁_A (x : NA) : (Y).val.v₁ (.inl (.inl x)) = PA.val.v₁ x := rfl
theorem three_v₁_K (y : NK) : (Y).val.v₁ (.inl (.inr y)) = K.val.v₁ y := rfl
theorem three_v₁_C (z : NC) : (Y).val.v₁ (.inr z) = PC.val.v₁ z := rfl
theorem three_toPGraph : (Y).toPGraph = PGraph.three m₁ m₂ := rfl

end Diagram

end FreeMarkov
