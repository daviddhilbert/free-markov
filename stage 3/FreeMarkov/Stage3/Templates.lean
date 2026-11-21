/-
Free Markov categories, Stage 3: the Markov templates (4.1)–(4.4) of Section 4 and the
symmetric set `T_M` of Markov templates.

Each Markov template is built from two anchored diagrams drawn with the operations of
Stage 1 (one-node diagrams, disjoint union, gluing, node-free diagrams), with `α`, `β`
matching the domain and codomain edges position by position (`Template.ofDiagrams`):

* (4.1) `coassT a` has `Ω` = `δ_a` glued to `δ_a ⊗ 1_a` and `Λ` = `δ_a` glued to `1_a ⊗ δ_a`.
  In the picture (4.1) of the paper the labels are the other way round (`Λ_a` is the diagram
  with `δ_a ⊗ 1_a`), so the template drawn there is `(coassT a).symm`; both are Markov
  templates, and `S_M` does not depend on this choice;
* (4.2) `Ω_a` = `δ_a` glued to `1_a ⊗ ε_a` (and `ε_a ⊗ 1_a` for right counitality),
  `Λ_a` = the single edge `1_a`;
* (4.3) `Ω_a` = `δ_a` glued to the symmetry `σ_{aa}`, i.e. the duplicate with its prongs
  in the other order, `Λ_a` = `δ_a`;
* (4.4) `Ω_f` = the node `f` glued to a discard on each output, `Λ_f` = a discard on each
  letter of the source of `f` (empty if the source is empty).

The classes of these diagrams are the composites of generators of `F_s(G)` written next to
them (`mk_coassΩD`, ...).  None of this uses the cited result C1.
-/
module

public import FreeMarkov.Stage2

@[expose] public section

universe w v u₁ u₂

namespace FreeMarkov

open CategoryTheory Diagram

variable {S : Type w}

/-! ### Transport of a morphism of `F_s(G)` along equal words -/

namespace DHom

variable {G : FreeGraphMonoid.{w, v} S}

/-- A class from `a` to `b`, read as a class from `a'` to `b'` when `a = a'`, `b = b'`. -/
def cast {a b a' b' : FreeMonoid S} (f : DHom G a b) (ha : a = a') (hb : b = b') :
    DHom G a' b' :=
  ⟨f.1, f.2.1.trans ha, f.2.2.trans hb⟩

@[simp] theorem cast_val {a b a' b' : FreeMonoid S} (f : DHom G a b) (ha : a = a')
    (hb : b = b') : (f.cast ha hb).1 = f.1 := rfl

/-- A class, as a morphism from its domain to its codomain. -/
def ofClass (c : DClass G) : DHom G c.dom c.cod := ⟨c, rfl, rfl⟩

end DHom

/-! ### A template from two anchored diagrams -/

theorem Enumeration.mapEquiv_matching_symm {E : Type u₁} {E' : Type u₂} {P : E → Prop}
    {P' : E' → Prop} (o : Enumeration P) (o' : Enumeration P')
    (h : o.list.length = o'.list.length) : o'.mapEquiv (o.matching o' h).symm = o := by
  have := Enumeration.mapEquiv_symm o (o.matching o' h)
  rw [Enumeration.mapEquiv_matching] at this
  exact this

theorem PDiagram.anchor_congr {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
    (Λ : PDiagram G N E) {d d' : Enumeration Λ.IsDom} {c c' : Enumeration Λ.IsCod}
    (hd : d = d') (hc : c = c') : Λ.anchor d c = Λ.anchor d' c' := by
  subst hd hc
  rfl

namespace Template

variable {G : FreeGraphMonoid.{w, v} S}

section OfDiagrams

variable {NΩ EΩ NΛ EΛ : Type} [Finite NΩ] [Finite EΩ] [Finite NΛ] [Finite EΛ]
  (Ω : Diagram G NΩ EΩ) (Λ : Diagram G NΛ EΛ)

omit [Finite NΩ] [Finite EΩ] [Finite NΛ] [Finite EΛ] in
theorem dom_map_eq {Ω : Diagram G NΩ EΩ} {Λ : Diagram G NΛ EΛ} (h : Ω.domWord = Λ.domWord) :
    Λ.dom.map Λ.val.v₀ = Ω.dom.map Ω.val.v₀ :=
  FreeMonoid.ofList.injective h.symm

omit [Finite NΩ] [Finite EΩ] [Finite NΛ] [Finite EΛ] in
theorem cod_map_eq {Ω : Diagram G NΩ EΩ} {Λ : Diagram G NΛ EΛ} (h : Ω.codWord = Λ.codWord) :
    Λ.cod.map Λ.val.v₀ = Ω.cod.map Ω.val.v₀ :=
  FreeMonoid.ofList.injective h.symm

omit [Finite NΩ] [Finite EΩ] [Finite NΛ] [Finite EΛ] in
theorem dom_length_eq {Ω : Diagram G NΩ EΩ} {Λ : Diagram G NΛ EΛ} (h : Ω.domWord = Λ.domWord) :
    Λ.dom.length = Ω.dom.length := by
  simpa using congrArg List.length (dom_map_eq h)

omit [Finite NΩ] [Finite EΩ] [Finite NΛ] [Finite EΛ] in
theorem cod_length_eq {Ω : Diagram G NΩ EΩ} {Λ : Diagram G NΛ EΛ} (h : Ω.codWord = Λ.codWord) :
    Λ.cod.length = Ω.cod.length := by
  simpa using congrArg List.length (cod_map_eq h)

/-- The template `((Ω, u) / (Λ, w), α, β)` drawn as two anchored diagrams with the same
domain and codomain words: `Ω`, `Λ` with their anchorings forgotten, and `α`, `β` matching
the domain and codomain edges position by position ("the uppercase letters indicate what
the bijections `α`, `β` are"). -/
noncomputable abbrev ofDiagrams (hd : Ω.domWord = Λ.domWord) (hc : Ω.codWord = Λ.codWord) :
    Template.{0} G where
  NΩ := NΩ
  EΩ := EΩ
  NΛ := NΛ
  EΛ := EΛ
  Ω := Ω.toPDiagram
  Λ := Λ.toPDiagram
  α := Λ.domEnum.matching Ω.domEnum
    (by exact dom_length_eq hd : Λ.toAGraph.domEnum.list.length = Ω.toAGraph.domEnum.list.length)
  β := Λ.codEnum.matching Ω.codEnum
    (by exact cod_length_eq hc : Λ.toAGraph.codEnum.list.length = Ω.toAGraph.codEnum.list.length)
  hα e := Enumeration.matching_spec _ _ _ _ _ (dom_map_eq hd) e
  hβ e := Enumeration.matching_spec _ _ _ _ _ (cod_map_eq hc) e

/-- With the orderings of its two diagrams, the template `ofDiagrams Ω Λ` has the pair
`([Ω], [Λ])` as its generating pair of `E_T`. -/
theorem ofDiagrams_pair (hd : Ω.domWord = Λ.domWord) (hc : Ω.codWord = Λ.codWord) :
    ∃ (dΩ : Enumeration (ofDiagrams Ω Λ hd hc).Ω.IsDom)
      (cΩ : Enumeration (ofDiagrams Ω Λ hd hc).Ω.IsCod),
      DClass.mk ((ofDiagrams Ω Λ hd hc).Ω.anchor dΩ cΩ) = DClass.mk Ω ∧
      DClass.mk ((ofDiagrams Ω Λ hd hc).Λ.anchor (dΩ.mapEquiv (ofDiagrams Ω Λ hd hc).α.symm)
        (cΩ.mapEquiv (ofDiagrams Ω Λ hd hc).β.symm)) = DClass.mk Λ := by
  refine ⟨Ω.toAGraph.domEnum, Ω.toAGraph.codEnum, rfl, ?_⟩
  show DClass.mk (Λ.toPDiagram.anchor
    (Ω.toAGraph.domEnum.mapEquiv (Λ.toAGraph.domEnum.matching Ω.toAGraph.domEnum _).symm)
    (Ω.toAGraph.codEnum.mapEquiv (Λ.toAGraph.codEnum.matching Ω.toAGraph.codEnum _).symm)) = _
  rw [Enumeration.mapEquiv_matching_symm, Enumeration.mapEquiv_matching_symm]
  rfl

end OfDiagrams

/-- If a template has the generating pair `(c, d)` for some ordering, its reverse has the
generating pair `(d, c)`. -/
theorem symm_pair {τ : Template.{u₁} G} {c d : DClass G}
    (h : ∃ (dΩ : Enumeration τ.Ω.IsDom) (cΩ : Enumeration τ.Ω.IsCod),
      DClass.mk (τ.Ω.anchor dΩ cΩ) = c ∧
      DClass.mk (τ.Λ.anchor (dΩ.mapEquiv τ.α.symm) (cΩ.mapEquiv τ.β.symm)) = d) :
    ∃ (dΩ : Enumeration τ.symm.Ω.IsDom) (cΩ : Enumeration τ.symm.Ω.IsCod),
      DClass.mk (τ.symm.Ω.anchor dΩ cΩ) = d ∧
      DClass.mk (τ.symm.Λ.anchor (dΩ.mapEquiv τ.symm.α.symm) (cΩ.mapEquiv τ.symm.β.symm)) = c := by
  obtain ⟨dΩ, cΩ, h₁, h₂⟩ := h
  refine ⟨dΩ.mapEquiv τ.α.symm, cΩ.mapEquiv τ.β.symm, h₂, ?_⟩
  show DClass.mk (τ.Ω.anchor ((dΩ.mapEquiv τ.α.symm).mapEquiv τ.α.symm.symm)
    ((cΩ.mapEquiv τ.β.symm).mapEquiv τ.β.symm.symm)) = c
  rw [Enumeration.mapEquiv_symm, Enumeration.mapEquiv_symm]
  exact h₁

theorem symm_symm (τ : Template.{u₁} G) : τ.symm.symm = τ := by
  cases τ
  rfl

theorem empty_symm : (Template.empty.{u₁} G).symm = Template.empty G := rfl

end Template

/-! ### The Markov templates -/

namespace FreeDDGraphMonoid

variable (G : FreeDDGraphMonoid.{w, v} S)

open Diagram

/-! #### The morphisms of `F_s(G)` that the diagrams of the templates represent -/

/-- The duplicate on `a`, as a morphism `a → aa` of `F_s(G)` (its one-node diagram). -/
noncomputable def dupH (a : S) :
    DHom G.toFreeGraphMonoid (FreeMonoid.of a) (FreeMonoid.of a * FreeMonoid.of a) :=
  (DHom.gen (G.dup a)).cast (G.s_dup a) (G.t_dup a)

/-- The discard on `a`, as a morphism `a → 1` of `F_s(G)` (its one-node diagram). -/
noncomputable def discH (a : S) : DHom G.toFreeGraphMonoid (FreeMonoid.of a) 1 :=
  (DHom.gen (G.disc a)).cast (G.s_disc a) (G.t_disc a)

/-- The discards on the letters of a word, side by side: `ε_{a_1} ⊗ ⋯ ⊗ ε_{a_n}`
(the node-free diagram of the empty word if `n = 0`). -/
noncomputable def discList : (l : List S) → DHom G.toFreeGraphMonoid (FreeMonoid.ofList l) 1
  | [] => DHom.id _ 1
  | a :: l => ((G.discH a).tensor (discList l)).cast rfl (mul_one 1)

/-- `ε_{a_1} ⊗ ⋯ ⊗ ε_{a_n}` for a word `a = a_1 ⋯ a_n`. -/
noncomputable def discWord (a : FreeMonoid S) : DHom G.toFreeGraphMonoid a 1 :=
  G.discList (FreeMonoid.toList a)

/-- (4.1): `(δ_a ⊗ 1_a) ∘ δ_a` (the `Ω` of `coassT`; `Λ_a` in the paper's picture). -/
noncomputable def coassΩ (a : S) : DHom G.toFreeGraphMonoid (FreeMonoid.of a)
    (FreeMonoid.of a * FreeMonoid.of a * FreeMonoid.of a) :=
  (G.dupH a).comp ((G.dupH a).tensor (DHom.id _ (FreeMonoid.of a)))

/-- (4.1): `(1_a ⊗ δ_a) ∘ δ_a` (the `Λ` of `coassT`; `Ω_a` in the paper's picture). -/
noncomputable def coassΛ (a : S) : DHom G.toFreeGraphMonoid (FreeMonoid.of a)
    (FreeMonoid.of a * (FreeMonoid.of a * FreeMonoid.of a)) :=
  (G.dupH a).comp ((DHom.id _ (FreeMonoid.of a)).tensor (G.dupH a))

/-- (4.2): `(1_a ⊗ ε_a) ∘ δ_a`. -/
noncomputable def counitΩ (a : S) :
    DHom G.toFreeGraphMonoid (FreeMonoid.of a) (FreeMonoid.of a * 1) :=
  (G.dupH a).comp ((DHom.id _ (FreeMonoid.of a)).tensor (G.discH a))

/-- (4.2), right counitality: `(ε_a ⊗ 1_a) ∘ δ_a`. -/
noncomputable def counitΩ' (a : S) :
    DHom G.toFreeGraphMonoid (FreeMonoid.of a) (1 * FreeMonoid.of a) :=
  (G.dupH a).comp ((G.discH a).tensor (DHom.id _ (FreeMonoid.of a)))

/-- (4.3): `σ_{aa} ∘ δ_a`. -/
noncomputable def cocommΩ (a : S) :
    DHom G.toFreeGraphMonoid (FreeMonoid.of a) (FreeMonoid.of a * FreeMonoid.of a) :=
  (G.dupH a).comp (DHom.braid _ (FreeMonoid.of a) (FreeMonoid.of a))

/-- (4.4): `(ε_{t_1} ⊗ ⋯ ⊗ ε_{t_m}) ∘ f` for an arrow `f : s → t`. -/
noncomputable def natΩ (f : G.A) : DHom G.toFreeGraphMonoid (G.s f) 1 :=
  (DHom.gen f).comp (G.discWord (G.t f))

/-- (4.4): `ε_{s_1} ⊗ ⋯ ⊗ ε_{s_k}`. -/
noncomputable def natΛ (f : G.A) : DHom G.toFreeGraphMonoid (G.s f) 1 :=
  G.discWord (G.s f)

/-! #### The diagrams of the templates -/

/-- The one-node diagram of the duplicate on `a`. -/
noncomputable abbrev dupD (a : S) := Diagram.oneNode (G := G.toFreeGraphMonoid) (G.dup a)

/-- The one-node diagram of the discard on `a`. -/
noncomputable abbrev discD (a : S) := Diagram.oneNode (G := G.toFreeGraphMonoid) (G.disc a)

theorem dupD_domWord (a : S) : (G.dupD a).domWord = FreeMonoid.of a := by
  rw [oneNode_domWord, G.s_dup]

theorem dupD_codWord (a : S) : (G.dupD a).codWord = FreeMonoid.of a * FreeMonoid.of a := by
  rw [oneNode_codWord, G.t_dup]

theorem discD_domWord (a : S) : (G.discD a).domWord = FreeMonoid.of a := by
  rw [oneNode_domWord, G.s_disc]

theorem discD_codWord (a : S) : (G.discD a).codWord = 1 := by
  rw [oneNode_codWord, G.t_disc]

/-- The nodes of `ε_{a_1} ⊗ ⋯ ⊗ ε_{a_n}`. -/
def discN : List S → Type
  | [] => Empty
  | _ :: l => Unit ⊕ discN l

/-- The edges of `ε_{a_1} ⊗ ⋯ ⊗ ε_{a_n}`. -/
def discE : List S → Type
  | [] => Fin (wlen (1 : FreeMonoid S))
  | a :: l => (Fin (wlen (G.s (G.disc a))) ⊕ Fin (wlen (G.t (G.disc a)))) ⊕ discE l

instance discN.finite : (l : List S) → Finite (discN (S := S) l)
  | [] => inferInstanceAs (Finite Empty)
  | _ :: l => letI := discN.finite l; inferInstanceAs (Finite (Unit ⊕ discN l))

instance discE.finite : (l : List S) → Finite (G.discE l)
  | [] => inferInstanceAs (Finite (Fin _))
  | _ :: l => letI := discE.finite l; inferInstanceAs (Finite (_ ⊕ G.discE l))

/-- The diagram of `ε_{a_1} ⊗ ⋯ ⊗ ε_{a_n}`: the one-node diagrams of the discards on the
letters, side by side. -/
noncomputable def discListD : (l : List S) → Diagram G.toFreeGraphMonoid (discN l) (G.discE l)
  | [] => idD _ 1
  | a :: l => (G.discD a).tensor (discListD l)

theorem discListD_domWord (l : List S) : (G.discListD l).domWord = FreeMonoid.ofList l := by
  induction l with
  | nil => exact idD_domWord _
  | cons a l ih =>
    change ((G.discD a).tensor (G.discListD l)).domWord = _
    rw [tensor_domWord, ih, G.discD_domWord]
    rfl

theorem discListD_codWord (l : List S) : (G.discListD l).codWord = 1 := by
  induction l with
  | nil => exact idD_codWord _
  | cons a l ih =>
    change ((G.discD a).tensor (G.discListD l)).codWord = _
    rw [tensor_codWord, ih, G.discD_codWord, mul_one]

theorem mk_discListD (l : List S) : DClass.mk (G.discListD l) = (G.discList l).1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change DClass.mk ((G.discD a).tensor (G.discListD l)) = _
    rw [← DClass.mk_tensor, ih]
    rfl

/-- (4.1), the `Ω` of `coassT a`: the duplicate on `a` whose first output enters a second
duplicate on `a` (the outputs ordered `H, C, A` from left to right). In the paper's picture this
diagram is labelled `Λ_a`. -/
noncomputable def coassΩD (a : S) :=
  (G.dupD a).glue ((G.dupD a).tensor (idD _ (FreeMonoid.of a)))
    (by rw [tensor_domWord, G.dupD_codWord, G.dupD_domWord, idD_domWord])

/-- (4.1), the `Λ` of `coassT a`: the duplicate on `a` whose second output enters a second
duplicate. In the paper's picture this diagram is labelled `Ω_a`. -/
noncomputable def coassΛD (a : S) :=
  (G.dupD a).glue ((idD _ (FreeMonoid.of a)).tensor (G.dupD a))
    (by rw [tensor_domWord, G.dupD_codWord, G.dupD_domWord, idD_domWord])

/-- (4.2), `Ω_a`: the duplicate on `a` whose second output ends at the discard on `a`. -/
noncomputable def counitΩD (a : S) :=
  (G.dupD a).glue ((idD _ (FreeMonoid.of a)).tensor (G.discD a))
    (by rw [tensor_domWord, G.dupD_codWord, G.discD_domWord, idD_domWord])

/-- (4.2), right counitality, `Ω_a`: the duplicate whose first output ends at a discard. -/
noncomputable def counitΩ'D (a : S) :=
  (G.dupD a).glue ((G.discD a).tensor (idD _ (FreeMonoid.of a)))
    (by rw [tensor_domWord, G.dupD_codWord, G.discD_domWord, idD_domWord])

/-- (4.2), `Λ_a`: a single edge. -/
noncomputable abbrev idDa (a : S) := idD G.toFreeGraphMonoid (FreeMonoid.of a)

/-- (4.3), `Ω_a`: the duplicate on `a` with its outputs in the other order. -/
noncomputable def cocommΩD (a : S) :=
  (G.dupD a).glue (braidD _ (FreeMonoid.of a) (FreeMonoid.of a))
    (by rw [braidD_domWord, G.dupD_codWord])

/-- (4.4), `Ω_f`: the node `f`, and a discard on each of its outputs. -/
noncomputable def natΩD (f : G.A) :=
  (Diagram.oneNode (G := G.toFreeGraphMonoid) f).glue (G.discListD (FreeMonoid.toList (G.t f)))
    (by rw [oneNode_codWord, discListD_domWord, FreeMonoid.ofList_toList])

/-- (4.4), `Λ_f`: a discard on each letter of the source of `f`. -/
noncomputable abbrev natΛD (f : G.A) := G.discListD (FreeMonoid.toList (G.s f))

theorem mk_coassΩD (a : S) : DClass.mk (G.coassΩD a) = (G.coassΩ a).1 := by
  rw [coassΩD, ← DClass.mk_comp, ← DClass.mk_tensor]
  rfl

theorem mk_coassΛD (a : S) : DClass.mk (G.coassΛD a) = (G.coassΛ a).1 := by
  rw [coassΛD, ← DClass.mk_comp, ← DClass.mk_tensor]
  rfl

theorem mk_counitΩD (a : S) : DClass.mk (G.counitΩD a) = (G.counitΩ a).1 := by
  rw [counitΩD, ← DClass.mk_comp, ← DClass.mk_tensor]
  rfl

theorem mk_counitΩ'D (a : S) : DClass.mk (G.counitΩ'D a) = (G.counitΩ' a).1 := by
  rw [counitΩ'D, ← DClass.mk_comp, ← DClass.mk_tensor]
  rfl

theorem mk_cocommΩD (a : S) : DClass.mk (G.cocommΩD a) = (G.cocommΩ a).1 := by
  rw [cocommΩD, ← DClass.mk_comp]
  rfl

theorem mk_natΩD (f : G.A) : DClass.mk (G.natΩD f) = (G.natΩ f).1 := by
  rw [natΩD, ← DClass.mk_comp, mk_discListD]
  rfl

theorem mk_natΛD (f : G.A) : DClass.mk (G.natΛD f) = (G.natΛ f).1 :=
  G.mk_discListD _

/-! #### The templates -/

/-- The template (4.1) for the letter `a` (coassociativity), with `Ω` and `Λ` in the order
opposite to the paper's picture: the drawn template is `(coassT a).symm`. -/
noncomputable abbrev coassT (a : S) : Template.{0} G.toFreeGraphMonoid :=
  Template.ofDiagrams (G.coassΩD a) (G.coassΛD a) (by simp [coassΩD, coassΛD])
    (by simp [coassΩD, coassΛD, G.t_dup, mul_assoc])

/-- The template (4.2) for the letter `a` (counitality, discard on the second prong). -/
noncomputable abbrev counitT (a : S) : Template.{0} G.toFreeGraphMonoid :=
  Template.ofDiagrams (G.counitΩD a) (G.idDa a) (by simp [counitΩD, G.dupD_domWord])
    (by simp [counitΩD, G.discD_codWord])

/-- The template (4.2) for the letter `a`, right counitality (discard on the first prong). -/
noncomputable abbrev counitT' (a : S) : Template.{0} G.toFreeGraphMonoid :=
  Template.ofDiagrams (G.counitΩ'D a) (G.idDa a) (by simp [counitΩ'D, G.dupD_domWord])
    (by simp [counitΩ'D, G.discD_codWord])

/-- The template (4.3) for the letter `a` (cocommutativity). -/
noncomputable abbrev cocommT (a : S) : Template.{0} G.toFreeGraphMonoid :=
  Template.ofDiagrams (G.cocommΩD a) (G.dupD a) (by simp [cocommΩD])
    (by simp [cocommΩD, G.dupD_codWord])

/-- The template (4.4) for the arrow `f` (naturality of discard), including the cases where
the source or the target of `f` is the empty word. -/
noncomputable abbrev natT (f : G.A) : Template.{0} G.toFreeGraphMonoid :=
  Template.ofDiagrams (G.natΩD f) (G.natΛD f)
    (by simp [natΩD, discListD_domWord, FreeMonoid.ofList_toList])
    (by simp [natΩD, discListD_codWord])

/-- The pairs `([Ω], [Λ])` of the Markov templates (4.1)–(4.4), before reversal. -/
inductive MarkovPair : DClass G.toFreeGraphMonoid → DClass G.toFreeGraphMonoid → Prop
  | coass (a : S) : MarkovPair (DClass.mk (G.coassΩD a)) (DClass.mk (G.coassΛD a))
  | counit (a : S) : MarkovPair (DClass.mk (G.counitΩD a)) (DClass.mk (G.idDa a))
  | counit' (a : S) : MarkovPair (DClass.mk (G.counitΩ'D a)) (DClass.mk (G.idDa a))
  | cocomm (a : S) : MarkovPair (DClass.mk (G.cocommΩD a)) (DClass.mk (G.dupD a))
  | nat (f : G.A) : MarkovPair (DClass.mk (G.natΩD f)) (DClass.mk (G.natΛD f))

theorem markovPair_coass (a : S) : G.MarkovPair (G.coassΩ a).1 (G.coassΛ a).1 := by
  rw [← mk_coassΩD, ← mk_coassΛD]
  exact .coass a

theorem markovPair_counit (a : S) :
    G.MarkovPair (G.counitΩ a).1 (DHom.id _ (FreeMonoid.of a)).1 := by
  rw [← mk_counitΩD]
  exact .counit a

theorem markovPair_counit' (a : S) :
    G.MarkovPair (G.counitΩ' a).1 (DHom.id _ (FreeMonoid.of a)).1 := by
  rw [← mk_counitΩ'D]
  exact .counit' a

theorem markovPair_cocomm (a : S) : G.MarkovPair (G.cocommΩ a).1 (G.dupH a).1 := by
  rw [← mk_cocommΩD]
  exact .cocomm a

theorem markovPair_nat (f : G.A) : G.MarkovPair (G.natΩ f).1 (G.natΛ f).1 := by
  rw [← mk_natΩD, ← mk_natΛD]
  exact .nat f

/-- The **Markov templates** before reversal: (4.1), (4.2) (left and right counitality),
(4.3) for every letter `a ∈ S`, and (4.4) for every arrow `f` of `G`. -/
def baseMarkovTemplates : Set (Template.{0} G.toFreeGraphMonoid) :=
  Set.range G.coassT ∪ Set.range G.counitT ∪ Set.range G.counitT' ∪ Set.range G.cocommT ∪
    Set.range G.natT

/-- Each base Markov template has the pair of a `MarkovPair` as a generating pair. -/
theorem baseMarkovTemplates_pair {τ : Template.{0} G.toFreeGraphMonoid}
    (hτ : τ ∈ G.baseMarkovTemplates) :
    ∃ c d, G.MarkovPair c d ∧ ∃ (dΩ : Enumeration τ.Ω.IsDom) (cΩ : Enumeration τ.Ω.IsCod),
      DClass.mk (τ.Ω.anchor dΩ cΩ) = c ∧
      DClass.mk (τ.Λ.anchor (dΩ.mapEquiv τ.α.symm) (cΩ.mapEquiv τ.β.symm)) = d := by
  rcases hτ with ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨f, rfl⟩)
  · exact ⟨_, _, .coass a, Template.ofDiagrams_pair _ _ _ _⟩
  · exact ⟨_, _, .counit a, Template.ofDiagrams_pair _ _ _ _⟩
  · exact ⟨_, _, .counit' a, Template.ofDiagrams_pair _ _ _ _⟩
  · exact ⟨_, _, .cocomm a, Template.ofDiagrams_pair _ _ _ _⟩
  · exact ⟨_, _, .nat f, Template.ofDiagrams_pair _ _ _ _⟩

/-- **The set `T_M` of Markov templates** (Section 4): the templates (4.1)–(4.4), "the
empty template and the versions that switch the roles of `Λ`, `Ω` so that the set becomes
symmetric". -/
def markovTemplates : Set (Template.{0} G.toFreeGraphMonoid) :=
  insert (Template.empty G.toFreeGraphMonoid)
    (G.baseMarkovTemplates ∪ Template.symm '' G.baseMarkovTemplates)

theorem markovTemplates_isSymmetric : Template.IsSymmetric G.markovTemplates where
  empty_mem := Set.mem_insert _ _
  symm_mem τ hτ := by
    rcases hτ with rfl | hτ | ⟨σ, hσ, rfl⟩
    · exact Set.mem_insert _ _
    · exact Or.inr (Or.inr ⟨τ, hτ, rfl⟩)
    · rw [Template.symm_symm]
      exact Or.inr (Or.inl hσ)

end FreeDDGraphMonoid

end FreeMarkov
