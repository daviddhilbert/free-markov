/-
Free Markov categories, Stage 1: relabelling of diagrams, and the value of a diagram
in a symmetric strict monoidal category (PLAN.md, Section 2, the second consequence
of C1 that is proved rather than assumed).

A diagram in `C` is a diagram in the free graph monoid `G_C` (`graphOf C`); its
value is its image under the functor `F_s(G_C) → C` given by C1 and the universal
property, i.e. `Syn.lift` of the evaluation `G_C → C` applied to the morphism of
`Syn_s(G_C)` that corresponds to its class.  A strict symmetric monoidal functor
preserves values.  The proof needs the naturality of the bijection of C1 under
relabelling, which follows from the generation principle.
-/
module

public import FreeMarkov.Stage1.JoyalStreet

@[expose] public section

universe w v w' v' u₁ u₂ u₃ u₄ u v₁ u₅ v₅

namespace FreeMarkov

open CategoryTheory StrictSMC FreeGraphMonoid

/-! ### Relabelling -/

/-- A map of free graph monoids that sends letters to letters: `onS` on the alphabet,
`onA` on arrows, compatible with sources and targets. -/
structure FreeGraphMonoid.Relabel {S : Type w} {S' : Type w'} (G : FreeGraphMonoid.{w, v} S)
    (H : FreeGraphMonoid.{w', v'} S') where
  /-- The map on letters. -/
  onS : S → S'
  /-- The map on arrows. -/
  onA : G.A → H.A
  s_onA (x : G.A) : H.s (onA x) = FreeMonoid.map onS (G.s x)
  t_onA (x : G.A) : H.t (onA x) = FreeMonoid.map onS (G.t x)

namespace FreeGraphMonoid.Relabel

variable {S : Type w} {S' : Type w'} {G : FreeGraphMonoid.{w, v} S}
  {H : FreeGraphMonoid.{w', v'} S'} (φ : G.Relabel H)

/-- The graph monoid homomorphism `G → Syn_s(H)` induced by a relabelling. -/
def toSynHom : G.toGraphMonoid.Hom (graphMonoid H.Syn) where
  V := FreeMonoid.map φ.onS
  A x := Arrow.mk (Syn.gen (φ.onA x))
  s_A x := φ.s_onA x
  t_A x := φ.t_onA x

/-- The strict functor `Syn_s(G) → Syn_s(H)` induced by a relabelling. -/
noncomputable def synMap : StrictFunctor G.Syn H.Syn := Syn.lift φ.toSynHom

end FreeGraphMonoid.Relabel

namespace Diagram

variable {S : Type w} {S' : Type w'} {G : FreeGraphMonoid.{w, v} S}
  {H : FreeGraphMonoid.{w', v'} S'} (φ : G.Relabel H) {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

/-- Relabelling a diagram: the same graph, with labels mapped by `φ`. -/
def relabel (Γ : Diagram G N E) : Diagram H N E where
  toAGraph := Γ.toAGraph
  val :=
    { v₀ := fun e => φ.onS (Γ.val.v₀ e)
      v₁ := fun x => φ.onA (Γ.val.v₁ x)
      s_v₁ := fun x => by
        rw [φ.s_onA, Γ.val.s_v₁]
        change FreeMonoid.ofList (((Γ.ins x).map Γ.val.v₀).map φ.onS) = _
        rw [List.map_map]
        rfl
      t_v₁ := fun x => by
        rw [φ.t_onA, Γ.val.t_v₁]
        change FreeMonoid.ofList (((Γ.outs x).map Γ.val.v₀).map φ.onS) = _
        rw [List.map_map]
        rfl }

@[simp] theorem relabel_domWord (Γ : Diagram G N E) :
    (Γ.relabel φ).domWord = FreeMonoid.map φ.onS Γ.domWord := by
  change FreeMonoid.ofList (Γ.dom.map (fun e => φ.onS (Γ.val.v₀ e))) =
    FreeMonoid.ofList ((Γ.dom.map Γ.val.v₀).map φ.onS)
  rw [List.map_map]
  rfl

@[simp] theorem relabel_codWord (Γ : Diagram G N E) :
    (Γ.relabel φ).codWord = FreeMonoid.map φ.onS Γ.codWord := by
  change FreeMonoid.ofList (Γ.cod.map (fun e => φ.onS (Γ.val.v₀ e))) =
    FreeMonoid.ofList ((Γ.cod.map Γ.val.v₀).map φ.onS)
  rw [List.map_map]
  rfl

/-- An isomorphism of diagrams is an isomorphism of their relabellings. -/
def Iso.relabel {Γ : Diagram G N E} {Γ' : Diagram G N' E'} (i : Γ.Iso Γ') :
    (Γ.relabel φ).Iso (Γ'.relabel φ) where
  toAIso := i.toAIso
  v₀_map e := congrArg φ.onS (i.v₀_map e)
  v₁_map x := congrArg φ.onA (i.v₁_map x)

/-- Diagrams on the same anchored graph with the same labels are isomorphic. -/
def isoOfEq {Γ Γ' : Diagram G N E} (hA : Γ.toAGraph = Γ'.toAGraph)
    (h₀ : ∀ e, Γ'.val.v₀ e = Γ.val.v₀ e) (h₁ : ∀ x, Γ'.val.v₁ x = Γ.val.v₁ x) : Γ.Iso Γ' where
  eN := Equiv.refl N
  eE := Equiv.refl E
  ins_map x := by
    change Γ'.toAGraph.ins x = (Γ.toAGraph.ins x).map id
    rw [hA, List.map_id]
  outs_map x := by
    change Γ'.toAGraph.outs x = (Γ.toAGraph.outs x).map id
    rw [hA, List.map_id]
  dom_map := by
    change Γ'.toAGraph.dom = Γ.toAGraph.dom.map id
    rw [hA, List.map_id]
  cod_map := by
    change Γ'.toAGraph.cod = Γ.toAGraph.cod.map id
    rw [hA, List.map_id]
  v₀_map := h₀
  v₁_map := h₁

/-- Relabelling commutes with disjoint union. -/
def relabelTensorIso (Γ : Diagram G N E) (Δ : Diagram G N' E') :
    ((Γ.tensor Δ).relabel φ).Iso ((Γ.relabel φ).tensor (Δ.relabel φ)) :=
  isoOfEq rfl (fun e => by cases e <;> rfl) (fun x => by cases x <;> rfl)

/-- Relabelling commutes with gluing. -/
noncomputable def relabelGlueIso (Γ : Diagram G N E) (Δ : Diagram G N' E')
    (h : Γ.codWord = Δ.domWord) (h' : (Γ.relabel φ).codWord = (Δ.relabel φ).domWord) :
    ((Γ.glue Δ h).relabel φ).Iso ((Γ.relabel φ).glue (Δ.relabel φ) h') :=
  isoOfEq rfl (fun e => by cases e <;> rfl) (fun x => by cases x <;> rfl)

theorem map_finCongr_finRange {n m : ℕ} (h : n = m) :
    (List.finRange n).map (finCongr h) = List.finRange m := by
  subst h; simp

theorem wlen_map (a : FreeMonoid S) : wlen (FreeMonoid.map φ.onS a) = wlen a := by
  simp [wlen, FreeMonoid.toList_map]

theorem letters_map {a : FreeMonoid S'} {b : FreeMonoid S} (h : a = FreeMonoid.map φ.onS b)
    (hl : wlen b = wlen a) (i : Fin (wlen b)) :
    letters a (finCongr hl i) = φ.onS (letters b i) := by
  subst h
  simp [letters, FreeMonoid.toList_map]

theorem wlen_s (x : G.A) : wlen (G.s x) = wlen (H.s (φ.onA x)) := by rw [φ.s_onA, wlen_map]

theorem wlen_t (x : G.A) : wlen (G.t x) = wlen (H.t (φ.onA x)) := by rw [φ.t_onA, wlen_map]

/-- The relabelled one-node diagram of `x` is the one-node diagram of `φ x`. -/
noncomputable def relabelOneNodeIso (x : G.A) : ((oneNode x).relabel φ).Iso (oneNode (φ.onA x)) where
  eN := Equiv.refl Unit
  eE := Equiv.sumCongr (finCongr (wlen_s φ x)) (finCongr (wlen_t φ x))
  ins_map _ := by
    simp [relabel, oneNode, PGraph.oneNode, List.map_map, Function.comp_def]
    rw [← map_finCongr_finRange (wlen_s φ x), List.map_map]
    rfl
  outs_map _ := by
    simp [relabel, oneNode, PGraph.oneNode, List.map_map, Function.comp_def]
    rw [← map_finCongr_finRange (wlen_t φ x), List.map_map]
    rfl
  dom_map := by
    simp [relabel, oneNode, List.map_map, Function.comp_def]
    rw [← map_finCongr_finRange (wlen_s φ x), List.map_map]
    rfl
  cod_map := by
    simp [relabel, oneNode, List.map_map, Function.comp_def]
    rw [← map_finCongr_finRange (wlen_t φ x), List.map_map]
    rfl
  v₀_map e := by
    cases e with
    | inl i => exact letters_map φ (φ.s_onA x) _ i
    | inr j => exact letters_map φ (φ.t_onA x) _ j
  v₁_map _ := rfl

/-- The relabelled identity diagram of `a` is the identity diagram of `φ a`. -/
noncomputable def relabelIdIso (a : FreeMonoid S) :
    ((idD G a).relabel φ).Iso (idD H (FreeMonoid.map φ.onS a)) where
  eN := Equiv.refl Empty
  eE := finCongr (wlen_map φ a).symm
  ins_map x := x.elim
  outs_map x := x.elim
  dom_map := by
    simp only [relabel, idD, nodeFree]
    rw [map_finCongr_finRange]
  cod_map := by
    simp only [relabel, idD, nodeFree]
    rw [map_finCongr_finRange]
  v₀_map i := letters_map φ rfl _ i
  v₁_map x := x.elim

/-- The relabelled symmetry diagram of `a, b` is the symmetry diagram of `φ a, φ b`. -/
noncomputable def relabelBraidIso (a b : FreeMonoid S) :
    ((braidD G a b).relabel φ).Iso
      (braidD H (FreeMonoid.map φ.onS a) (FreeMonoid.map φ.onS b)) where
  eN := Equiv.refl Empty
  eE := Equiv.sumCongr (finCongr (wlen_map φ a).symm) (finCongr (wlen_map φ b).symm)
  ins_map x := x.elim
  outs_map x := x.elim
  dom_map := by
    simp only [relabel, braidD, nodeFree, braidDom, List.map_append, List.map_map]
    rw [← map_finCongr_finRange (wlen_map φ a).symm, ← map_finCongr_finRange (wlen_map φ b).symm]
    simp [List.map_map, Function.comp_def]
  cod_map := by
    simp only [relabel, braidD, nodeFree, braidCod, List.map_append, List.map_map]
    rw [← map_finCongr_finRange (wlen_map φ a).symm, ← map_finCongr_finRange (wlen_map φ b).symm]
    simp [List.map_map, Function.comp_def]
  v₀_map e := by
    cases e with
    | inl i => exact letters_map φ rfl _ i
    | inr j => exact letters_map φ rfl _ j
  v₁_map x := x.elim

end Diagram

namespace DClass

open Diagram

variable {S : Type w} {S' : Type w'} {G : FreeGraphMonoid.{w, v} S}
  {H : FreeGraphMonoid.{w', v'} S'} (φ : G.Relabel H) {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

/-- Relabelling of isomorphism classes. -/
noncomputable def relabel (c : DClass G) : DClass H :=
  Quotient.lift (fun Γ : FinDiag G => mk (Γ.2.relabel φ))
    (fun _ _ h => (show Nonempty (Diagram.Iso _ _) from h).elim fun i => mk_eq_mk (i.relabel φ)) c

theorem mk_relabel (Γ : Diagram G N E) [Finite N] [Finite E] :
    (mk Γ).relabel φ = mk (Γ.relabel φ) :=
  mk_eq_mk (Γ.isoToFin.symm.relabel φ)

theorem relabel_tensor (c d : DClass G) : (c.tensor d).relabel φ = (c.relabel φ).tensor (d.relabel φ) := by
  induction c using ind with
  | h _ _ Γ => induction d using ind with
    | h _ _ Δ =>
      rw [mk_tensor, mk_relabel, mk_relabel, mk_relabel, mk_tensor]
      exact mk_eq_mk (relabelTensorIso φ Γ Δ)

theorem relabel_comp {c d : DClass G} (h : c.cod = d.dom) :
    (c.comp d).relabel φ = (c.relabel φ).comp (d.relabel φ) := by
  induction c using ind with
  | h _ _ Γ => induction d using ind with
    | h _ _ Δ =>
      simp only [cod_mk, dom_mk] at h
      have h' : (Γ.relabel φ).codWord = (Δ.relabel φ).domWord := by simp [h]
      rw [mk_comp _ _ h, mk_relabel, mk_relabel, mk_relabel, mk_comp _ _ h']
      exact mk_eq_mk (relabelGlueIso φ Γ Δ h h')

end DClass

namespace JoyalStreet

variable {S : Type w} {S' : Type w'} {G : FreeGraphMonoid.{w, v} S}
  {H : FreeGraphMonoid.{w', v'} S'}

/-- Morphisms of `Syn_s(H)` corresponding under C1 to classes that agree are equal as
arrows. -/
theorem arrow_eq_of_val_eq (J : JoyalStreet G) {a b a' b' : FreeMonoid S}
    (m : Syn.of G a ⟶ Syn.of G b) (u : DHom G a' b') (h : (J.equiv a b m).1 = u.1) :
    Arrow.mk m = Arrow.mk ((J.equiv a' b').symm u) := by
  have ha : a = a' := (J.equiv a b m).2.1.symm.trans (h ▸ u.2.1)
  have hb : b = b' := (J.equiv a b m).2.2.symm.trans (h ▸ u.2.2)
  subst ha hb
  rw [(Equiv.eq_symm_apply _).2 (DHom.ext h)]

/-- **Naturality of C1 under relabelling.** The bijections of C1 for `G` and `H`
commute with relabelling along `φ`.  Proved by the generation principle. -/
theorem val_synMap (JG : JoyalStreet G) (JH : JoyalStreet H) (φ : G.Relabel H)
    {a b : FreeMonoid S} (m : Syn.of G a ⟶ Syn.of G b) :
    (JH.equiv _ _ (φ.synMap.map m)).1 = (JG.equiv a b m).1.relabel φ := by
  refine Syn.induction (P := fun {a b} m =>
    (JH.equiv _ _ (φ.synMap.map m)).1 = (JG.equiv a b m).1.relabel φ) ?_ ?_ ?_ ?_ ?_ m
  · intro x
    have harr : Arrow.mk (φ.synMap.map (Syn.gen x)) = Arrow.mk (Syn.gen (φ.onA x)) :=
      Syn.arrow_interp_gen φ.toSynHom x
    refine (JH.val_eq_of_arrow_eq harr).trans ?_
    refine (congrArg Subtype.val (JH.map_gen (φ.onA x))).trans ?_
    refine Eq.trans ?_ (congrArg (DClass.relabel φ) (congrArg Subtype.val (JG.map_gen x))).symm
    exact ((DClass.mk_relabel φ _).trans (DClass.mk_eq_mk (Diagram.relabelOneNodeIso φ x))).symm
  · intro a
    refine (congrArg Subtype.val ((congrArg (JH.equiv _ _) (φ.synMap.map_id a)).trans
      (JH.map_id (FreeMonoid.map φ.onS a)))).trans ?_
    refine Eq.trans ?_ (congrArg (DClass.relabel φ) (congrArg Subtype.val (JG.map_id a))).symm
    exact ((DClass.mk_relabel φ _).trans (DClass.mk_eq_mk (Diagram.relabelIdIso φ a))).symm
  · intro a b
    refine (JH.val_eq_of_arrow_eq (φ.synMap.map_braid a b)).trans ?_
    refine (congrArg Subtype.val (JH.map_braid _ _)).trans ?_
    refine Eq.trans ?_ (congrArg (DClass.relabel φ) (congrArg Subtype.val (JG.map_braid a b))).symm
    exact ((DClass.mk_relabel φ _).trans (DClass.mk_eq_mk (Diagram.relabelBraidIso φ a b))).symm
  · intro a b c f g hf hg
    refine (congrArg Subtype.val ((congrArg (JH.equiv _ _) (φ.synMap.map_comp f g)).trans
      (JH.map_comp _ _))).trans ?_
    refine (congrArg₂ DClass.comp hf hg).trans ?_
    refine Eq.trans ?_ (congrArg (DClass.relabel φ) (congrArg Subtype.val (JG.map_comp f g))).symm
    exact (DClass.relabel_comp φ ((JG.equiv _ _ f).2.2.trans (JG.equiv _ _ g).2.1.symm)).symm
  · intro a b c d f g hf hg
    refine (JH.val_eq_of_arrow_eq (φ.synMap.map_tensorHom f g)).trans ?_
    refine (congrArg Subtype.val (JH.map_tensor _ _)).trans ?_
    refine (congrArg₂ DClass.tensor hf hg).trans ?_
    refine Eq.trans ?_ (congrArg (DClass.relabel φ) (congrArg Subtype.val (JG.map_tensor f g))).symm
    exact (DClass.relabel_tensor φ _ _).symm

end JoyalStreet

/-! ### The value of a diagram in a symmetric strict monoidal category -/

variable {C : Type u} [Monoid C] [Category.{v₁} C] [StrictSMC C]

/-- The evaluation `G_C → C`: the identity on objects (words multiplied out) and on
morphisms. -/
def evalHom (C : Type u) [Monoid C] [Category.{v₁} C] :
    (graphOf C).toGraphMonoid.Hom (graphMonoid C) where
  V := FreeMonoid.lift id
  A f := Arrow.mk f.2.2
  s_A _ := rfl
  t_A _ := rfl

/-- The value of an anchored diagram `Δ` in `G_C`: the image of its class under the
functor `F_s(G_C) → C` given by C1 (`Syn.lift` of the evaluation, read through the
bijection of C1). -/
noncomputable def valueFree (J : JoyalStreet (graphOf C)) {N : Type u₁} {E : Type u₂}
    (Δ : Diagram (graphOf C) N E) [Finite N] [Finite E] :
    evalWord Δ.domWord ⟶ evalWord Δ.codWord :=
  (Syn.lift (evalHom C)).map ((J.equiv _ _).symm (DHom.mk Δ))

/-- *Section 2 (the value of a diagram, Joyal–Street, Chapter 2, §1).* The **value** `[Γ, v] : dom(Γ, v) → cod(Γ, v)`
of an anchored diagram in a symmetric strict monoidal category `C`. -/
noncomputable def CDiagram.value (J : JoyalStreet (graphOf C)) {N : Type u₁} {E : Type u₂}
    (Γ : CDiagram C N E) [Finite N] [Finite E] : Γ.domObj ⟶ Γ.codObj :=
  valueFree J Γ.toFree

/-- The value of the one-node diagram of a morphism `f` of `C` is `f`. -/
theorem valueFree_oneNode (J : JoyalStreet (graphOf C)) (x : (graphOf C).A) :
    Arrow.mk (valueFree J (Diagram.oneNode x)) = Arrow.mk x.2.2 := by
  have h : Arrow.mk ((J.equiv _ _).symm (DHom.mk (Diagram.oneNode x))) =
      Arrow.mk (Syn.gen x) := by
    refine (J.arrow_eq_of_val_eq (Syn.gen x) (DHom.mk (Diagram.oneNode x)) ?_).symm
    rw [J.map_gen]
    rfl
  exact ((Syn.lift (evalHom C)).toFunctor.mk_map_congr h).trans
    (Syn.arrow_interp_gen (evalHom C) x)

/-- Values depend only on the class. -/
theorem valueFree_eq_of_iso (J : JoyalStreet (graphOf C)) {N : Type u₁} {E : Type u₂}
    {N' : Type u₃} {E' : Type u₄} {Δ : Diagram (graphOf C) N E} [Finite N] [Finite E]
    {Δ' : Diagram (graphOf C) N' E'} [Finite N'] [Finite E'] (i : Δ.Iso Δ') :
    Arrow.mk (valueFree J Δ) = Arrow.mk (valueFree J Δ') := by
  refine (Syn.lift (evalHom C)).toFunctor.mk_map_congr ?_
  refine J.arrow_eq_of_val_eq _ _ ?_
  exact (congrArg Subtype.val ((J.equiv _ _).apply_symm_apply _)).trans (DClass.mk_eq_mk i)

variable {D : Type u₅} [Monoid D] [Category.{v₅} D] [StrictSMC D]

theorem StrictFunctor.obj_evalWord (F : StrictFunctor C D) (a : FreeMonoid C) :
    F.obj (evalWord a) = evalWord (FreeMonoid.map F.obj a) := by
  have : F.objHom.comp (FreeMonoid.lift _root_.id) =
      (FreeMonoid.lift _root_.id).comp (FreeMonoid.map F.obj) :=
    FreeMonoid.hom_eq fun x => by simp [StrictFunctor.objHom]
  exact DFunLike.congr_fun this a

omit [Monoid D] [StrictSMC D] in
theorem arrow_mk_cast {X Y X' Y' : D} (hX : X' = X) (f : X ⟶ Y) (hY : Y = Y') :
    Arrow.mk (eqToHom hX ≫ f ≫ eqToHom hY) = Arrow.mk f := by
  subst hX hY
  simp

/-- The relabelling `G_C → G_D` induced by a strict functor `F : C → D`. -/
def StrictFunctor.relabel (F : StrictFunctor C D) : (graphOf C).Relabel (graphOf D) where
  onS := F.obj
  onA f := ⟨FreeMonoid.map F.obj f.1, FreeMonoid.map F.obj f.2.1,
    eqToHom (F.obj_evalWord f.1).symm ≫ F.map f.2.2 ≫ eqToHom (F.obj_evalWord f.2.1)⟩
  s_onA _ := rfl
  t_onA _ := rfl

/-- **A strict symmetric monoidal functor preserves values** (PLAN.md, Section 2), for
diagrams in `G_C`: `F [Δ] = [F_* Δ]`. -/
theorem StrictFunctor.map_valueFree (F : StrictFunctor C D) (JC : JoyalStreet (graphOf C))
    (JD : JoyalStreet (graphOf D)) {N : Type u₁} {E : Type u₂} (Δ : Diagram (graphOf C) N E)
    [Finite N] [Finite E] :
    Arrow.mk (F.map (valueFree JC Δ)) = Arrow.mk (valueFree JD (Δ.relabel F.relabel)) := by
  set m := (JC.equiv _ _).symm (DHom.mk Δ)
  -- `F ∘ lift ev_C = lift (F ∘ ev_C) = lift ev_D ∘ Syn(φ_F)`.
  have h₁ : F.comp (Syn.lift (evalHom C)) = Syn.lift (F.toGraphMonoidHom.comp (evalHom C)) :=
    Syn.eq_lift _ (by
      change F.toGraphMonoidHom.comp ((Syn.lift (evalHom C)).toGraphMonoidHom.comp (Syn.ι _)) = _
      rw [Syn.lift_comp_ι])
  have h₂ : (Syn.lift (evalHom D)).comp F.relabel.synMap =
      Syn.lift (F.toGraphMonoidHom.comp (evalHom C)) := by
    refine Syn.eq_lift _ ?_
    change (Syn.lift (evalHom D)).toGraphMonoidHom.comp
      (F.relabel.synMap.toGraphMonoidHom.comp (Syn.ι _)) = _
    rw [FreeGraphMonoid.Relabel.synMap, Syn.lift_comp_ι]
    ext x
    · exact (F.obj_evalWord (FreeMonoid.of x)).symm
    · change Arrow.mk ((Syn.lift (evalHom D)).map (Syn.gen _)) = Arrow.mk (F.map x.2.2)
      refine (Syn.arrow_interp_gen (evalHom D) _).trans ?_
      exact arrow_mk_cast _ _ _
  have h₃ : Arrow.mk (F.map (valueFree JC Δ)) =
      Arrow.mk ((Syn.lift (evalHom D)).map (F.relabel.synMap.map m)) := by
    change Arrow.mk ((F.comp (Syn.lift (evalHom C))).map m) =
      Arrow.mk (((Syn.lift (evalHom D)).comp F.relabel.synMap).map m)
    rw [h₁, h₂]
  refine h₃.trans ((Syn.lift (evalHom D)).toFunctor.mk_map_congr ?_)
  refine JD.arrow_eq_of_val_eq _ _ ?_
  rw [JoyalStreet.val_synMap JC JD F.relabel m, Equiv.apply_symm_apply]
  exact DClass.mk_relabel _ _

omit [StrictSMC D] in
theorem graphOf_A_ext {a a' b b' : FreeMonoid D} (ha : a = a') (hb : b = b') {X Y : D}
    (f : X ⟶ Y) (p : evalWord a = X) (q : Y = evalWord b) (p' : evalWord a' = X)
    (q' : Y = evalWord b') :
    (⟨a, b, eqToHom p ≫ f ≫ eqToHom q⟩ : (graphOf D).A) = ⟨a', b', eqToHom p' ≫ f ≫ eqToHom q'⟩ := by
  subst ha hb
  rfl

theorem StrictFunctor.obj_evalWord_ofList (F : StrictFunctor C D) {E : Type u₂} (l : List E)
    (v : E → C) : evalWord (FreeMonoid.ofList (l.map fun e => F.obj (v e))) =
      F.obj (evalWord (FreeMonoid.ofList (l.map v))) := by
  rw [F.obj_evalWord]
  exact congrArg (fun l => evalWord (FreeMonoid.ofList l)) (List.map_map ..).symm

/-- The image `F_*(Γ, v)` of a diagram in `C` under a strict functor `F : C → D`: the
same graph, with `F` applied to the labels. -/
def CDiagram.map (F : StrictFunctor C D) {N : Type u₁} {E : Type u₂} (Γ : CDiagram C N E) :
    CDiagram D N E where
  toAGraph := Γ.toAGraph
  val :=
    { v₀ := fun e => F.obj (Γ.val.v₀ e)
      v₁ := fun x => eqToHom (F.obj_evalWord_ofList _ _) ≫ F.map (Γ.val.v₁ x) ≫
        eqToHom (F.obj_evalWord_ofList _ _).symm }

/-- **A strict symmetric monoidal functor preserves values** (PLAN.md, Section 2):
`F [Γ, v] = [F_*(Γ, v)]`. -/
theorem CDiagram.map_value (F : StrictFunctor C D) (JC : JoyalStreet (graphOf C))
    (JD : JoyalStreet (graphOf D)) {N : Type u₁} {E : Type u₂} (Γ : CDiagram C N E) [Finite N]
    [Finite E] : Arrow.mk (F.map (Γ.value JC)) = Arrow.mk ((Γ.map F).value JD) := by
  refine (F.map_valueFree JC JD Γ.toFree).trans (valueFree_eq_of_iso JD ?_)
  refine Diagram.isoOfEq rfl (fun _ => rfl) (fun x => ?_)
  exact graphOf_A_ext (D := D)
    (a := FreeMonoid.ofList ((Γ.ins x).map fun e => F.obj (Γ.val.v₀ e)))
    (a' := FreeMonoid.map F.obj (FreeMonoid.ofList ((Γ.ins x).map Γ.val.v₀)))
    (b := FreeMonoid.ofList ((Γ.outs x).map fun e => F.obj (Γ.val.v₀ e)))
    (b' := FreeMonoid.map F.obj (FreeMonoid.ofList ((Γ.outs x).map Γ.val.v₀)))
    (congrArg FreeMonoid.ofList (List.map_map (g := F.obj) (f := Γ.val.v₀) (l := Γ.ins x))).symm
    (congrArg FreeMonoid.ofList (List.map_map (g := F.obj) (f := Γ.val.v₀) (l := Γ.outs x))).symm
    _ _ _ _ _

end FreeMarkov
