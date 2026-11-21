/-
Free Markov categories, Stage 4: embeddings of diagrams assembled from one-node diagrams,
node-free diagrams, disjoint unions and gluings (the diagrams of the Markov templates) into a
diagram `X`, and the surgery they give.

* `PEmb D X`: maps of nodes and edges of `D` into `X`, injective, carrying ordered inputs,
  outputs and labels; constructors `oneNode`, `idD`, `braidD`, `tensor`, `glue`, with the images
  of the domain and codomain orderings.
* `isNormal_of_root`: the image of an embedding with a root through which all its nodes are
  reached, and whose other nodes have all their inputs inside, is a normal subgraph.
* `tStep_of_emb`: a template whose `Ω` embeds as a normal subgraph gives a surgery step with a
  canonical description of its result.
-/
module

public import FreeMarkov.Stage4.Lemma43

@[expose] public section

universe w v u u₁ u₂ u₃ u₄ u₅ u₆

namespace FreeMarkov

open Relation

theorem List.map_finRange_getElem' {α : Type*} (l : List α) (n : ℕ) (h : n = l.length) :
    (List.finRange n).map (fun i => l[i.1]'(h ▸ i.2)) = l := by
  subst h
  exact List.map_getElem_finRange l

theorem List.getElem_eq_of_map_eq' {α β : Type*} {l : List α} {l' : List β} {f : α → β}
    (hv : l.map f = l') (i : ℕ) (hi : i < l.length) (hi' : i < l'.length) : f l[i] = l'[i] := by
  subst hv
  simp

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-- An embedding of `D` into `X`. -/
structure PEmb {N : Type u₁} {E : Type u₂} {NX : Type u₃} {EX : Type u₄}
    (D : Diagram G N E) (X : Diagram G NX EX) where
  ιN : N → NX
  ιE : E → EX
  injN : Function.Injective ιN
  injE : Function.Injective ιE
  ins : ∀ z, X.ins (ιN z) = (D.ins z).map ιE
  outs : ∀ z, X.outs (ιN z) = (D.outs z).map ιE
  v₀ : ∀ d, X.val.v₀ (ιE d) = D.val.v₀ d
  v₁ : ∀ z, X.val.v₁ (ιN z) = D.val.v₁ z

variable {NX : Type u₃} {EX : Type u₄} {X : Diagram G NX EX}

theorem length_ins_eq (X : Diagram G NX EX) (x : NX) :
    (X.ins x).length = wlen (G.s (X.val.v₁ x)) := by
  rw [X.val.s_v₁]
  simp [wlen]

theorem length_outs_eq (X : Diagram G NX EX) (x : NX) :
    (X.outs x).length = wlen (G.t (X.val.v₁ x)) := by
  rw [X.val.t_v₁]
  simp [wlen]

theorem v₀_ins_eq (X : Diagram G NX EX) (x : NX) (i : ℕ) (hi : i < (X.ins x).length)
    (hi' : i < (FreeMonoid.toList (G.s (X.val.v₁ x))).length) :
    X.val.v₀ (X.ins x)[i] = (FreeMonoid.toList (G.s (X.val.v₁ x)))[i] := by
  have h := X.val.s_v₁ x
  have h' : FreeMonoid.toList (G.s (X.val.v₁ x)) = (X.ins x).map X.val.v₀ := by rw [h]; rfl
  simp only [h', List.getElem_map]

theorem v₀_outs_eq (X : Diagram G NX EX) (x : NX) (i : ℕ) (hi : i < (X.outs x).length)
    (hi' : i < (FreeMonoid.toList (G.t (X.val.v₁ x))).length) :
    X.val.v₀ (X.outs x)[i] = (FreeMonoid.toList (G.t (X.val.v₁ x)))[i] := by
  have h := X.val.t_v₁ x
  have h' : FreeMonoid.toList (G.t (X.val.v₁ x)) = (X.outs x).map X.val.v₀ := by rw [h]; rfl
  simp only [h', List.getElem_map]

theorem not_mem_ins_of_mem_outs (X : Diagram G NX EX) {x : NX} {e : EX} (h : e ∈ X.outs x) :
    e ∉ X.ins x := by
  intro h'
  exact X.acyclic x (TransGen.single ⟨e, (X.mem_outs x e).1 h, (X.mem_ins x e).1 h'⟩)

namespace PEmb

/-! ### One-node diagrams -/

/-- The one-node diagram of `f` at a node `x` with `v(x) = f`. -/
def oneNode (x : NX) {f : G.A} (hx : X.val.v₁ x = f) : PEmb (Diagram.oneNode f) X where
  ιN _ := x
  ιE := Sum.elim (fun i => (X.ins x)[i.1]'(by rw [length_ins_eq, hx]; exact i.2))
    (fun j => (X.outs x)[j.1]'(by rw [length_outs_eq, hx]; exact j.2))
  injN _ _ _ := rfl
  injE := by
    rintro (i | i) (j | j) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [(X.ins_nodup x).getElem_inj_iff] at h
      exact congrArg Sum.inl (Fin.ext h)
    · exact (X.not_mem_ins_of_mem_outs (List.getElem_mem _) (h ▸ List.getElem_mem _)).elim
    · exact (X.not_mem_ins_of_mem_outs (h ▸ List.getElem_mem _) (List.getElem_mem _)).elim
    · rw [(X.outs_nodup x).getElem_inj_iff] at h
      exact congrArg Sum.inr (Fin.ext h)
  ins _ := by
    show X.ins x = ((List.finRange _).map Sum.inl).map _
    rw [List.map_map]
    exact (List.map_finRange_getElem' _ _ (by rw [length_ins_eq, hx])).symm
  outs _ := by
    show X.outs x = ((List.finRange _).map Sum.inr).map _
    rw [List.map_map]
    exact (List.map_finRange_getElem' _ _ (by rw [length_outs_eq, hx])).symm
  v₀ := by
    subst hx
    rintro (i | j)
    · exact v₀_ins_eq X x i.1 _ i.2
    · exact v₀_outs_eq X x j.1 _ j.2
  v₁ _ := hx

theorem oneNode_dom (x : NX) {f : G.A} (hx : X.val.v₁ x = f) :
    (Diagram.oneNode f).dom.map (oneNode x hx).ιE = X.ins x := by
  have := (oneNode x hx).ins ()
  exact this.symm

theorem oneNode_cod (x : NX) {f : G.A} (hx : X.val.v₁ x = f) :
    (Diagram.oneNode f).cod.map (oneNode x hx).ιE = X.outs x := by
  have := (oneNode x hx).outs ()
  exact this.symm

/-! ### Node-free diagrams -/

/-- The identity diagram of `a` along a duplicate-free list of edges labelled by `a`. -/
def idD (a : FreeMonoid S) (l : List EX) (hl : l.Nodup) (hv : l.map X.val.v₀ = FreeMonoid.toList a) :
    PEmb (Diagram.idD G a) X where
  ιN := Empty.elim
  ιE i := l[i.1]'(by
    have := congrArg List.length hv
    rw [List.length_map] at this
    rw [this]; exact i.2)
  injN x := x.elim
  injE i j h := Fin.ext ((hl.getElem_inj_iff).1 h)
  ins x := x.elim
  outs x := x.elim
  v₀ i := List.getElem_eq_of_map_eq' hv i.1 _ i.2
  v₁ x := x.elim

theorem idD_dom (a : FreeMonoid S) (l : List EX) (hl : l.Nodup)
    (hv : l.map X.val.v₀ = FreeMonoid.toList a) :
    (Diagram.idD G a).dom.map (idD a l hl hv).ιE = l :=
  List.map_finRange_getElem' l _ (by simp only [wlen, ← hv, List.length_map])

theorem idD_cod (a : FreeMonoid S) (l : List EX) (hl : l.Nodup)
    (hv : l.map X.val.v₀ = FreeMonoid.toList a) :
    (Diagram.idD G a).cod.map (idD a l hl hv).ιE = l :=
  List.map_finRange_getElem' l _ (by simp only [wlen, ← hv, List.length_map])

/-- The symmetry diagram `σ_{a,b}` along two lists of edges labelled by `a` and `b`. -/
def braidD (a b : FreeMonoid S) (l₁ l₂ : List EX) (hl : (l₁ ++ l₂).Nodup)
    (hv₁ : l₁.map X.val.v₀ = FreeMonoid.toList a) (hv₂ : l₂.map X.val.v₀ = FreeMonoid.toList b) :
    PEmb (Diagram.braidD G a b) X where
  ιN := Empty.elim
  ιE := Sum.elim (fun i => l₁[i.1]'(by
      have := congrArg List.length hv₁
      rw [List.length_map] at this
      rw [this]; exact i.2))
    (fun j => l₂[j.1]'(by
      have := congrArg List.length hv₂
      rw [List.length_map] at this
      rw [this]; exact j.2))
  injN x := x.elim
  injE := by
    have h₁ := (List.nodup_append.1 hl).1
    have h₂ := (List.nodup_append.1 hl).2.1
    have h₃ := (List.nodup_append.1 hl).2.2
    rintro (i | i) (j | j) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (Fin.ext ((h₁.getElem_inj_iff).1 h))
    · exact (h₃ _ (List.getElem_mem _) _ (List.getElem_mem _) h).elim
    · exact (h₃ _ (List.getElem_mem _) _ (List.getElem_mem _) h.symm).elim
    · exact congrArg Sum.inr (Fin.ext ((h₂.getElem_inj_iff).1 h))
  ins x := x.elim
  outs x := x.elim
  v₀ := by
    rintro (i | j)
    · exact List.getElem_eq_of_map_eq' hv₁ i.1 _ i.2
    · exact List.getElem_eq_of_map_eq' hv₂ j.1 _ j.2
  v₁ x := x.elim

theorem braidD_dom (a b : FreeMonoid S) (l₁ l₂ : List EX) (hl : (l₁ ++ l₂).Nodup)
    (hv₁ : l₁.map X.val.v₀ = FreeMonoid.toList a) (hv₂ : l₂.map X.val.v₀ = FreeMonoid.toList b) :
    (Diagram.braidD G a b).dom.map (braidD a b l₁ l₂ hl hv₁ hv₂).ιE = l₁ ++ l₂ := by
  show (braidDom a b).map _ = _
  simp only [braidDom, List.map_append, List.map_map]
  congr 1
  · exact List.map_finRange_getElem' l₁ _ (by simp only [wlen, ← hv₁, List.length_map])
  · exact List.map_finRange_getElem' l₂ _ (by simp only [wlen, ← hv₂, List.length_map])

theorem braidD_cod (a b : FreeMonoid S) (l₁ l₂ : List EX) (hl : (l₁ ++ l₂).Nodup)
    (hv₁ : l₁.map X.val.v₀ = FreeMonoid.toList a) (hv₂ : l₂.map X.val.v₀ = FreeMonoid.toList b) :
    (Diagram.braidD G a b).cod.map (braidD a b l₁ l₂ hl hv₁ hv₂).ιE = l₂ ++ l₁ := by
  show (braidCod a b).map _ = _
  simp only [braidCod, List.map_append, List.map_map]
  congr 1
  · exact List.map_finRange_getElem' l₂ _ (by simp only [wlen, ← hv₂, List.length_map])
  · exact List.map_finRange_getElem' l₁ _ (by simp only [wlen, ← hv₁, List.length_map])

/-! ### Disjoint unions and gluings -/

variable {N : Type u₁} {E : Type u₂} {N' : Type u₅} {E' : Type u₆}
  {Γ : Diagram G N E} {Ω : Diagram G N' E'}

/-- The disjoint union of two embeddings with disjoint images. -/
def tensor (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hE : ∀ d d', e₁.ιE d ≠ e₂.ιE d') : PEmb (Γ.tensor Ω) X where
  ιN := Sum.elim e₁.ιN e₂.ιN
  ιE := Sum.elim e₁.ιE e₂.ιE
  injN := by
    rintro (z | z) (z' | z') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [e₁.injN h]
    · exact (hN _ _ h).elim
    · exact (hN _ _ h.symm).elim
    · rw [e₂.injN h]
  injE := by
    rintro (d | d) (d' | d') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [e₁.injE h]
    · exact (hE _ _ h).elim
    · exact (hE _ _ h.symm).elim
    · rw [e₂.injE h]
  ins := by
    rintro (z | z)
    · show X.ins (e₁.ιN z) = ((Γ.ins z).map Sum.inl).map _
      rw [List.map_map, e₁.ins]; rfl
    · show X.ins (e₂.ιN z) = ((Ω.ins z).map Sum.inr).map _
      rw [List.map_map, e₂.ins]; rfl
  outs := by
    rintro (z | z)
    · show X.outs (e₁.ιN z) = ((Γ.outs z).map Sum.inl).map _
      rw [List.map_map, e₁.outs]; rfl
    · show X.outs (e₂.ιN z) = ((Ω.outs z).map Sum.inr).map _
      rw [List.map_map, e₂.outs]; rfl
  v₀ := by
    rintro (d | d)
    · exact e₁.v₀ d
    · exact e₂.v₀ d
  v₁ := by
    rintro (z | z)
    · exact e₁.v₁ z
    · exact e₂.v₁ z

theorem tensor_dom (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hE : ∀ d d', e₁.ιE d ≠ e₂.ιE d') :
    (Γ.tensor Ω).dom.map (tensor e₁ e₂ hN hE).ιE = Γ.dom.map e₁.ιE ++ Ω.dom.map e₂.ιE := by
  show (Γ.dom.map Sum.inl ++ Ω.dom.map Sum.inr).map _ = _
  rw [List.map_append, List.map_map, List.map_map]
  rfl

theorem tensor_cod (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hE : ∀ d d', e₁.ιE d ≠ e₂.ιE d') :
    (Γ.tensor Ω).cod.map (tensor e₁ e₂ hN hE).ιE = Γ.cod.map e₁.ιE ++ Ω.cod.map e₂.ιE := by
  show (Γ.cod.map Sum.inl ++ Ω.cod.map Sum.inr).map _ = _
  rw [List.map_append, List.map_map, List.map_map]
  rfl

/-- The gluing of two embeddings that agree on the glued edges. -/
def glue (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (h : Γ.codWord = Ω.domWord)
    (hc : Γ.cod.map e₁.ιE = Ω.dom.map e₂.ιE) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hE : ∀ d (d' : Ω.InnerSrc), e₁.ιE d ≠ e₂.ιE d'.1) : PEmb (Γ.glue Ω h) X where
  ιN := Sum.elim e₁.ιN e₂.ιN
  ιE := Sum.elim e₁.ιE fun d => e₂.ιE d.1
  injN := by
    rintro (z | z) (z' | z') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [e₁.injN h]
    · exact (hN _ _ h).elim
    · exact (hN _ _ h.symm).elim
    · rw [e₂.injN h]
  injE := by
    rintro (d | d) (d' | d') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [e₁.injE h]
    · exact (hE _ _ h).elim
    · exact (hE _ _ h.symm).elim
    · exact congrArg Sum.inr (Subtype.ext (e₂.injE h))
  ins := by
    have key : ∀ d : E', Sum.elim e₁.ιE (fun d => e₂.ιE d.1)
        (PGraph.glueIn (Γ.toAGraph.matching Ω.toAGraph (length_eq_of_codWord_eq h)) d) = e₂.ιE d := by
      intro d
      by_cases hd : Ω.src d = none
      · rw [PGraph.glueIn_of_eq_none _ hd, Sum.elim_inl]
        have := Enumeration.matching_spec Γ.toAGraph.codEnum Ω.toAGraph.domEnum
          (length_eq_of_codWord_eq h) e₁.ιE e₂.ιE hc
          ((Γ.toAGraph.matching Ω.toAGraph (length_eq_of_codWord_eq h)).symm ⟨d, hd⟩)
        simp only [AGraph.matching, Equiv.apply_symm_apply] at this
        exact this.symm
      · rw [PGraph.glueIn_of_ne_none _ hd]
        rfl
    rintro (z | z)
    · show X.ins (e₁.ιN z) = ((Γ.ins z).map Sum.inl).map _
      rw [List.map_map, e₁.ins]; rfl
    · show X.ins (e₂.ιN z) = ((Ω.ins z).map _).map _
      rw [List.map_map, e₂.ins]
      exact (List.map_congr_left fun d _ => key d).symm
  outs := by
    have key : ∀ d : E', Sum.elim e₁.ιE (fun d => e₂.ιE d.1)
        (PGraph.glueIn (Γ.toAGraph.matching Ω.toAGraph (length_eq_of_codWord_eq h)) d) = e₂.ιE d := by
      intro d
      by_cases hd : Ω.src d = none
      · rw [PGraph.glueIn_of_eq_none _ hd, Sum.elim_inl]
        have := Enumeration.matching_spec Γ.toAGraph.codEnum Ω.toAGraph.domEnum
          (length_eq_of_codWord_eq h) e₁.ιE e₂.ιE hc
          ((Γ.toAGraph.matching Ω.toAGraph (length_eq_of_codWord_eq h)).symm ⟨d, hd⟩)
        simp only [AGraph.matching, Equiv.apply_symm_apply] at this
        exact this.symm
      · rw [PGraph.glueIn_of_ne_none _ hd]
        rfl
    rintro (z | z)
    · show X.outs (e₁.ιN z) = ((Γ.outs z).map Sum.inl).map _
      rw [List.map_map, e₁.outs]; rfl
    · show X.outs (e₂.ιN z) = ((Ω.outs z).map _).map _
      rw [List.map_map, e₂.outs]
      exact (List.map_congr_left fun d _ => key d).symm
  v₀ := by
    rintro (d | d)
    · exact e₁.v₀ d
    · exact e₂.v₀ d.1
  v₁ := by
    rintro (z | z)
    · exact e₁.v₁ z
    · exact e₂.v₁ z

theorem glue_ιE_glueIn (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (h : Γ.codWord = Ω.domWord)
    (hc : Γ.cod.map e₁.ιE = Ω.dom.map e₂.ιE) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hE : ∀ d (d' : Ω.InnerSrc), e₁.ιE d ≠ e₂.ιE d'.1) (d : E') :
    (glue e₁ e₂ h hc hN hE).ιE
      (PGraph.glueIn (Γ.toAGraph.matching Ω.toAGraph (length_eq_of_codWord_eq h)) d) = e₂.ιE d := by
  by_cases hd : Ω.src d = none
  · rw [PGraph.glueIn_of_eq_none _ hd]
    have := Enumeration.matching_spec Γ.toAGraph.codEnum Ω.toAGraph.domEnum
      (length_eq_of_codWord_eq h) e₁.ιE e₂.ιE hc
      ((Γ.toAGraph.matching Ω.toAGraph (length_eq_of_codWord_eq h)).symm ⟨d, hd⟩)
    simp only [AGraph.matching, Equiv.apply_symm_apply] at this
    exact this.symm
  · rw [PGraph.glueIn_of_ne_none _ hd]
    rfl

theorem glue_dom (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (h : Γ.codWord = Ω.domWord)
    (hc : Γ.cod.map e₁.ιE = Ω.dom.map e₂.ιE) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hE : ∀ d (d' : Ω.InnerSrc), e₁.ιE d ≠ e₂.ιE d'.1) :
    (Γ.glue Ω h).dom.map (glue e₁ e₂ h hc hN hE).ιE = Γ.dom.map e₁.ιE := by
  show (Γ.dom.map Sum.inl).map _ = _
  rw [List.map_map]
  rfl

theorem glue_cod (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (h : Γ.codWord = Ω.domWord)
    (hc : Γ.cod.map e₁.ιE = Ω.dom.map e₂.ιE) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hE : ∀ d (d' : Ω.InnerSrc), e₁.ιE d ≠ e₂.ιE d'.1) :
    (Γ.glue Ω h).cod.map (glue e₁ e₂ h hc hN hE).ιE = Ω.cod.map e₂.ιE := by
  show (Ω.cod.map _).map _ = _
  rw [List.map_map]
  exact List.map_congr_left fun d _ => glue_ιE_glueIn e₁ e₂ h hc hN hE d

end PEmb

end Diagram

end FreeMarkov
