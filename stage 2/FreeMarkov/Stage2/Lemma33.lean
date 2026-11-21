/-
Free Markov categories, Stage 2: Lemma 3.3.

The three-piece gluing along the position-by-position matchings is the composite of
the three classes (`threeIsoGlue`, `mk_three`).  A surgery therefore decomposes as
`h ∘ [Λ^♯] ∘ g` next to `[Γ] = h ∘ [Ω^♯] ∘ g` (`classDecomp`, the "only if" half), and
conversely such a pair of decompositions comes from a surgery (`classRecognition`, the
"if" half).  `lemma_3_3` is the statement of the paper, with `Γ'^♯` anchored by total
orderings for which the bijections given by `φ ∘ α`, `φ ∘ β` and the identity on
`Γ'^♯ ∖ Γ'` are order-preserving.  No cited result is used: the composites are taken in
the bracketing `h ∘ (X ∘ g)`, which needs no associativity.
-/
module

public import FreeMarkov.Stage2.Recognition

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁

namespace FreeMarkov

open Relation

/-! ### Enumerations transported along bijections -/

namespace Enumeration

variable {E : Type u₁} {E' : Type u₂} {E'' : Type u₃} {P : E → Prop} {P' : E' → Prop}
  {P'' : E'' → Prop}

theorem ext_list {o o' : Enumeration P} (h : o.list = o'.list) : o = o' := by
  cases o; cases o'; subst h; rfl

theorem mapEquiv_list (o : Enumeration P) (σ : {e // P e} ≃ {e' // P' e'}) :
    (o.mapEquiv σ).list = o.sub.map fun x => (σ x).1 := by
  simp [mapEquiv, List.map_map, Function.comp_def]

theorem sub_mapEquiv (o : Enumeration P) (σ : {e // P e} ≃ {e' // P' e'}) :
    (o.mapEquiv σ).sub = o.sub.map σ := by
  refine List.map_injective_iff.2 Subtype.val_injective ?_
  rw [sub_map_val, mapEquiv_list, List.map_map]
  rfl

theorem mapEquiv_mapEquiv (o : Enumeration P) (σ : {e // P e} ≃ {e' // P' e'})
    (τ : {e' // P' e'} ≃ {e'' // P'' e''}) : (o.mapEquiv σ).mapEquiv τ = o.mapEquiv (σ.trans τ) :=
  ext_list (by rw [mapEquiv_list, sub_mapEquiv, mapEquiv_list, List.map_map]; rfl)

theorem mapEquiv_refl (o : Enumeration P) : o.mapEquiv (Equiv.refl _) = o :=
  ext_list (by rw [mapEquiv_list]; exact o.sub_map_val)

theorem mapEquiv_symm (o : Enumeration P) (σ : {e // P e} ≃ {e' // P' e'}) :
    (o.mapEquiv σ).mapEquiv σ.symm = o := by
  rw [mapEquiv_mapEquiv, Equiv.self_trans_symm, mapEquiv_refl]

theorem mapEquiv_cancel (o : Enumeration P) (σ : {e // P e} ≃ {e' // P' e'})
    (τ : {e // P e} ≃ {e'' // P'' e''}) : (o.mapEquiv σ).mapEquiv (σ.symm.trans τ) = o.mapEquiv τ := by
  rw [mapEquiv_mapEquiv, ← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]

theorem mapEquiv_cancel' (o : Enumeration P') (σ : {e // P e} ≃ {e' // P' e'})
    (τ : {e' // P' e'} ≃ {e'' // P'' e''}) : (o.mapEquiv σ.symm).mapEquiv (σ.trans τ) = o.mapEquiv τ := by
  rw [mapEquiv_mapEquiv, ← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]

theorem mapEquiv_trans_eq (o : Enumeration P) (σ : {e // P e} ≃ {e' // P' e'})
    (τ : {e' // P' e'} ≃ {e'' // P'' e''}) (o' : Enumeration P') (h : o' = o.mapEquiv σ) :
    o'.mapEquiv τ = o.mapEquiv (σ.trans τ) := by
  subst h
  exact mapEquiv_mapEquiv o σ τ

theorem mapEquiv_matching (o : Enumeration P) (o' : Enumeration P')
    (h : o.list.length = o'.list.length) : o.mapEquiv (o.matching o' h) = o' := by
  refine ext_list (List.ext_getElem (by rw [mapEquiv_length, h]) fun i h₁ h₂ => ?_)
  have hi : i < o.list.length := by rwa [mapEquiv_length] at h₁
  simp only [mapEquiv_list, List.getElem_map]
  rw [← matching_getElem o o' h i hi]
  congr 2
  refine Subtype.ext ?_
  have := congrArg (fun l => l[i]?) o.sub_map_val
  simp only [List.getElem?_map] at this
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem] at this
  · simpa using this

theorem matching_eq_of_eq_mapEquiv {o : Enumeration P} {o' : Enumeration P'}
    {σ : {e // P e} ≃ {e' // P' e'}} (h : o' = o.mapEquiv σ)
    (hl : o.list.length = o'.list.length) : o.matching o' hl = σ := by
  subst h
  exact matching_mapEquiv o σ hl

/-- Two orderings related by a bijection give the same word when the labels agree along
the bijection. -/
theorem map_mapEquiv {S : Type u₄} (o : Enumeration P) (σ : {e // P e} ≃ {e' // P' e'})
    (v : E → S) (v' : E' → S) (h : ∀ x, v' (σ x).1 = v x.1) :
    (o.mapEquiv σ).list.map v' = o.list.map v := by
  rw [mapEquiv_list, List.map_map, ← o.sub_map_val, List.map_map]
  exact List.map_congr_left fun x _ => h x

/-- `o.mapEquiv σ = o'` when an injective map identifies the two lists. -/
theorem mapEquiv_eq_of_map {T : Type u₄} (o : Enumeration P) (o' : Enumeration P')
    (σ : {e // P e} ≃ {e' // P' e'}) (f : E' → T) (hf : Function.Injective f)
    (h : o'.list.map f = o.sub.map fun x => f (σ x).1) : o.mapEquiv σ = o' :=
  ext_list (List.map_injective_iff.2 hf (by rw [h, mapEquiv_list, List.map_map]; rfl))

end Enumeration

theorem AGraph.matching_eq_of {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}
    {Γ : AGraph N E} {Ω : AGraph N' E'} (h : Γ.cod.length = Ω.dom.length)
    {σ : {e // Γ.IsCod e} ≃ {e // Ω.IsDom e}} (hσ : Ω.domEnum = Γ.codEnum.mapEquiv σ) :
    Γ.matching Ω h = σ :=
  Enumeration.matching_eq_of_eq_mapEquiv hσ h

theorem AGraph.domEnum_eq_mapEquiv_matching {N : Type u₁} {E : Type u₂} {N' : Type u₃}
    {E' : Type u₄} (Γ : AGraph N E) (Ω : AGraph N' E') (h : Γ.cod.length = Ω.dom.length) :
    Ω.domEnum = Γ.codEnum.mapEquiv (Γ.matching Ω h) :=
  (Enumeration.mapEquiv_matching _ _ _).symm

/-! ### The three-piece gluing along matchings of orderings is a composite -/

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}
  {NA : Type u₁} {EA : Type u₂} {NK : Type u₃} {EK : Type u₄} {NC : Type u₅} {EC : Type u₆}

theorem glue_matching_glueCodEquiv (A' : Diagram G NA EA) (K' : Diagram G NK EK)
    (C' : Diagram G NC EC) (hw₁ : A'.codWord = K'.domWord) (hw₂ : K'.codWord = C'.domWord)
    (hw₂' : (A'.glue K' hw₁).codWord = C'.domWord) (k : {e // K'.IsCod e}) :
    (A'.glue K' hw₁).toAGraph.matching C'.toAGraph (length_eq_of_codWord_eq hw₂')
      (PGraph.glueCodEquiv _ k) =
      K'.toAGraph.matching C'.toAGraph (length_eq_of_codWord_eq hw₂) k :=
  Subtype.ext (Enumeration.matching_map K'.codEnum C'.domEnum (A'.glue K' hw₁).codEnum
    C'.domEnum _ _ (PGraph.glueIn _) id rfl (List.map_id _).symm k _)

/-- **Gluing three pieces along the matchings of their orderings** is the same as
gluing twice in `F_s(G)`. -/
noncomputable def threeIsoGlue (A' : Diagram G NA EA) (K' : Diagram G NK EK)
    (C' : Diagram G NC EC) (hw₁ : A'.codWord = K'.domWord) (hw₂ : K'.codWord = C'.domWord)
    (hw₂' : (A'.glue K' hw₁).codWord = C'.domWord) :
    (Diagram.three A'.toPDiagram K'.toPDiagram C'.toPDiagram
      (A'.toAGraph.matching K'.toAGraph (length_eq_of_codWord_eq hw₁))
      (K'.toAGraph.matching C'.toAGraph (length_eq_of_codWord_eq hw₂))
      (matching_v₀ hw₁) (matching_v₀ hw₂) A'.domEnum C'.codEnum).Iso
      ((A'.glue K' hw₁).glue C' hw₂') := by
  have hμ : (A'.glue K' hw₁).toAGraph.matching C'.toAGraph (length_eq_of_codWord_eq hw₂') =
      PGraph.threeMatch (A'.toAGraph.matching K'.toAGraph (length_eq_of_codWord_eq hw₁))
        (K'.toAGraph.matching C'.toAGraph (length_eq_of_codWord_eq hw₂)) := by
    refine Equiv.ext fun c => ?_
    obtain ⟨k, rfl⟩ := (PGraph.glueCodEquiv _).surjective c
    rw [glue_matching_glueCodEquiv A' K' C' hw₁ hw₂ hw₂']
    change _ = (K'.toAGraph.matching C'.toAGraph _)
      ((PGraph.glueCodEquiv _).symm (PGraph.glueCodEquiv _ k))
    rw [Equiv.symm_apply_apply]
  exact
    { eN := Equiv.refl _
      eE := Equiv.refl _
      ins_map := by
        rintro (n | z)
        · simp [Diagram.glue, AGraph.glue, Diagram.three, PGraph.threeA, PGraph.three,
            AGraph.ofPGraph, Function.comp_def]
        · simp only [Equiv.coe_refl, List.map_id, id_eq]
          show (C'.ins z).map (PGraph.glueIn _) = (C'.ins z).map (PGraph.glueIn _)
          rw [hμ]
          rfl
      outs_map := by
        rintro (n | z)
        · simp [Diagram.glue, AGraph.glue, Diagram.three, PGraph.threeA, PGraph.three,
            AGraph.ofPGraph, Function.comp_def]
        · simp only [Equiv.coe_refl, List.map_id, id_eq]
          show (C'.outs z).map (PGraph.glueIn _) = (C'.outs z).map (PGraph.glueIn _)
          rw [hμ]
          rfl
      dom_map := by
        simp only [Equiv.coe_refl, List.map_id]
        show (A'.dom.map Sum.inl).map Sum.inl = A'.dom.map PGraph.rA
        rw [List.map_map]
        rfl
      cod_map := by
        simp only [Equiv.coe_refl, List.map_id]
        show C'.cod.map (PGraph.glueIn _) = C'.cod.map (PGraph.glueIn _)
        rw [hμ]
        rfl
      v₀_map := fun _ => rfl
      v₁_map := fun _ => rfl }

variable [Finite NA] [Finite EA] [Finite NK] [Finite EK] [Finite NC] [Finite EC]

theorem mk_three (A' : Diagram G NA EA) (K' : Diagram G NK EK) (C' : Diagram G NC EC)
    (hw₁ : A'.codWord = K'.domWord) (hw₂ : K'.codWord = C'.domWord) :
    DClass.mk (Diagram.three A'.toPDiagram K'.toPDiagram C'.toPDiagram
      (A'.toAGraph.matching K'.toAGraph (length_eq_of_codWord_eq hw₁))
      (K'.toAGraph.matching C'.toAGraph (length_eq_of_codWord_eq hw₂))
      (matching_v₀ hw₁) (matching_v₀ hw₂) A'.domEnum C'.codEnum) =
      ((DClass.mk A').comp (DClass.mk K')).comp (DClass.mk C') := by
  have hw₂' : (A'.glue K' hw₁).codWord = C'.domWord := by rw [glue_codWord]; exact hw₂
  rw [DClass.mk_comp _ _ hw₁, DClass.mk_comp _ _ hw₂']
  exact DClass.mk_eq_mk (threeIsoGlue A' K' C' hw₁ hw₂ hw₂')

end Diagram

/-! ### Decomposition of a surgery into classes ("only if" half of Lemma 3.3) -/

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

section ClassDecomp

variable {N : Type u₁} {E : Type u₂} (Γ : Diagram G N E) {A : Subgraph N E}
  (V : Γ.ValidLayer A) {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PDiagram G NΩ EΩ}
  {NΛ : Type u₅} {EΛ : Type u₆} {Λ : PDiagram G NΛ EΛ}
  (φ : Ω.Iso (Γ.subD A V.edgeAt))
  (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e})
  (hα : ∀ e, Ω.val.v₀ (α e).1 = Λ.val.v₀ e.1) (hβ : ∀ e, Ω.val.v₀ (β e).1 = Λ.val.v₀ e.1)
  (dK : Enumeration (Ω.toPGraph.addLoose V.R).IsDom)
  (cK : Enumeration (Ω.toPGraph.addLoose V.R).IsCod)

/-- The lower layer `Γ[∅, L]`, anchored by `dom(Γ)` and the ordering of `cut(L)`
corresponding to `dK`. -/
noncomputable abbrev lowerA : Diagram G {x // Γ.LayerNode ∅ V.L x} {e // Γ.LayerEdge ∅ V.L e} :=
  (Γ.layerP Γ.isLevel_empty V.isLevel_L).anchor (Γ.toAGraph.lowerDom V.L)
    (dK.mapEquiv (V.domMatch φ.toPIso))

/-- The upper layer `Γ[M, Γ̇]`, anchored by the ordering of `cut(M)` corresponding to `cK`
and `cod(Γ)`. -/
noncomputable abbrev upperA :
    Diagram G {x // Γ.LayerNode V.M Set.univ x} {e // Γ.LayerEdge V.M Set.univ e} :=
  (Γ.layerP V.isLevel_M Γ.isLevel_univ).anchor (cK.mapEquiv (V.codMatch φ.toPIso))
    (Γ.toAGraph.upperCod V.M)

/-- `Ω^♯ = Ω ⊎ R`, anchored by `dK` and `cK`. -/
noncomputable abbrev midΩ : Diagram G NΩ (EΩ ⊕ V.R) := (Ω.addLoose (Γ.rLabel V)).anchor dK cK

/-- `Λ^♯ = Λ ⊎ R`, anchored by the orderings corresponding to `dK` and `cK` through
`α ⊎ id` and `β ⊎ id`. -/
noncomputable abbrev midΛ : Diagram G NΛ (EΛ ⊕ V.R) :=
  (Λ.addLoose (Γ.rLabel V)).anchor (dK.mapEquiv (PGraph.liftDom α V.R).symm)
    (cK.mapEquiv (PGraph.liftCod β V.R).symm)

theorem lowerA_codWord : (Γ.lowerA V φ dK).codWord = (Γ.midΩ V dK cK).domWord := by
  unfold codWord domWord
  congr 1
  exact Enumeration.map_mapEquiv dK _ _ _ fun x => (v₀_edgeOf Γ V φ x.1).symm

theorem midΩ_codWord : (Γ.midΩ V dK cK).codWord = (Γ.upperA V φ cK).domWord := by
  unfold codWord domWord
  congr 1
  exact (Enumeration.map_mapEquiv cK _ _ _ fun x => (v₀_edgeOf Γ V φ x.1).symm).symm

include hα in
theorem midΛ_domWord : (Γ.midΛ V α β dK cK).domWord = (Γ.midΩ V dK cK).domWord := by
  unfold domWord
  congr 1
  refine Enumeration.map_mapEquiv dK _ _ _ fun x => ?_
  have := v₀_liftDom α hα (Γ.rLabel V) ((PGraph.liftDom α V.R).symm x)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

include hβ in
theorem midΛ_codWord : (Γ.midΛ V α β dK cK).codWord = (Γ.midΩ V dK cK).codWord := by
  unfold codWord
  congr 1
  refine Enumeration.map_mapEquiv cK _ _ _ fun x => ?_
  have := v₀_liftCod β hβ (Γ.rLabel V) ((PGraph.liftCod β V.R).symm x)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

variable [Finite N] [Finite E] [Finite NΩ] [Finite EΩ] [Finite NΛ] [Finite EΛ]

/-- **Lemma 3.3, "only if" half, class form**: `[Γ] = h ∘ [Ω^♯] ∘ g` with `g`, `h` the
classes of the lower and upper layers, for any anchoring of `Ω^♯`. -/
theorem mk_eq_decomp :
    DClass.mk Γ = ((DClass.mk (Γ.lowerA V φ dK)).comp (DClass.mk (Γ.midΩ V dK cK))).comp
      (DClass.mk (Γ.upperA V φ cK)) := by
  rw [← mk_three _ _ _ (Γ.lowerA_codWord V φ dK cK) (Γ.midΩ_codWord V φ dK cK)]
  refine DClass.mk_eq_mk ((Γ.isoDecomp V φ).symm.trans (isoMid (PDiagram.Iso.refl _) ?_ ?_))
  · intro c
    have key := AGraph.matching_eq_of (Γ := (Γ.lowerA V φ dK).toAGraph)
      (Ω := (Γ.midΩ V dK cK).toAGraph) (σ := (V.domMatch φ.toPIso).symm)
      (length_eq_of_codWord_eq (Γ.lowerA_codWord V φ dK cK)) (by
        change dK = (dK.mapEquiv (V.domMatch φ.toPIso)).mapEquiv (V.domMatch φ.toPIso).symm
        rw [Enumeration.mapEquiv_symm])
    exact congrArg Subtype.val (DFunLike.congr_fun key c)
  · intro k k' hk
    have : k' = k := Subtype.ext hk
    subst this
    exact DFunLike.congr_fun (AGraph.matching_eq_of (Γ := (Γ.midΩ V dK cK).toAGraph)
      (Ω := (Γ.upperA V φ cK).toAGraph) (σ := V.codMatch φ.toPIso)
      (length_eq_of_codWord_eq (Γ.midΩ_codWord V φ dK cK)) rfl) k'

omit [Finite NΩ] [Finite EΩ] in
/-- **Lemma 3.3, "only if" half, class form**: the result of the surgery is
`h ∘ [Λ^♯] ∘ g` with the same `g`, `h`. -/
theorem mk_surgeryAt_eq_decomp :
    DClass.mk (Γ.surgeryAt V φ α β hα hβ) =
      ((DClass.mk (Γ.lowerA V φ dK)).comp (DClass.mk (Γ.midΛ V α β dK cK))).comp
        (DClass.mk (Γ.upperA V φ cK)) := by
  rw [← mk_three _ _ _ ((Γ.lowerA_codWord V φ dK cK).trans (Γ.midΛ_domWord V α β hα dK cK).symm)
    ((Γ.midΛ_codWord V α β hβ dK cK).trans (Γ.midΩ_codWord V φ dK cK))]
  refine DClass.mk_eq_mk (isoMid (PDiagram.Iso.refl _) ?_ ?_)
  · intro c
    have key := AGraph.matching_eq_of (Γ := (Γ.lowerA V φ dK).toAGraph)
      (Ω := (Γ.midΛ V α β dK cK).toAGraph)
      (σ := (V.domMatch φ.toPIso).symm.trans (PGraph.liftDom α V.R).symm)
      (length_eq_of_codWord_eq
        ((Γ.lowerA_codWord V φ dK cK).trans (Γ.midΛ_domWord V α β hα dK cK).symm)) (by
        exact (Enumeration.mapEquiv_cancel dK (V.domMatch φ.toPIso)
          (PGraph.liftDom α V.R).symm).symm)
    exact congrArg Subtype.val (DFunLike.congr_fun key c)
  · intro k k' hk
    have : k' = k := Subtype.ext hk
    subst this
    exact DFunLike.congr_fun (AGraph.matching_eq_of (Γ := (Γ.midΛ V α β dK cK).toAGraph)
      (Ω := (Γ.upperA V φ cK).toAGraph)
      (σ := (PGraph.liftCod β V.R).trans (V.codMatch φ.toPIso))
      (length_eq_of_codWord_eq
        ((Γ.midΛ_codWord V α β hβ dK cK).trans (Γ.midΩ_codWord V φ dK cK))) (by
        exact (Enumeration.mapEquiv_cancel' cK (PGraph.liftCod β V.R)
          (V.codMatch φ.toPIso)).symm)) k'

end ClassDecomp

/-! ### Recognition in terms of classes ("if" half of Lemma 3.3) -/

section ClassRecognition

variable {NX : Type u₁} {EX : Type u₂} (X : Diagram G NX EX) {NΞ : Type u₃} {EΞ : Type u₄}
  (Ξ : Diagram G NΞ EΞ) {NΩ : Type u₅} {EΩ : Type u₆} {Ω : PDiagram G NΩ EΩ}
  {NΛ : Type u₇} {EΛ : Type u₈} {Λ : PDiagram G NΛ EΛ}
  (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e})
  (hα : ∀ e, Ω.val.v₀ (α e).1 = Λ.val.v₀ e.1) (hβ : ∀ e, Ω.val.v₀ (β e).1 = Λ.val.v₀ e.1)
  {R : Type u₉} (r : R → S) (dK : Enumeration (Ω.toPGraph.addLoose R).IsDom)
  (cK : Enumeration (Ω.toPGraph.addLoose R).IsCod)

include hα in
theorem anchor_liftDom_domWord :
    ((Λ.addLoose r).anchor (dK.mapEquiv (PGraph.liftDom α R).symm)
      (cK.mapEquiv (PGraph.liftCod β R).symm)).domWord = ((Ω.addLoose r).anchor dK cK).domWord := by
  unfold domWord
  congr 1
  refine Enumeration.map_mapEquiv dK _ _ _ fun x => ?_
  have := v₀_liftDom α hα r ((PGraph.liftDom α R).symm x)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

include hβ in
theorem anchor_liftCod_codWord :
    ((Λ.addLoose r).anchor (dK.mapEquiv (PGraph.liftDom α R).symm)
      (cK.mapEquiv (PGraph.liftCod β R).symm)).codWord = ((Ω.addLoose r).anchor dK cK).codWord := by
  unfold codWord
  congr 1
  refine Enumeration.map_mapEquiv cK _ _ _ fun x => ?_
  have := v₀_liftCod β hβ r ((PGraph.liftCod β R).symm x)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

variable [Finite NX] [Finite EX] [Finite NΞ] [Finite EΞ] [Finite NΩ] [Finite EΩ] [Finite NΛ]
  [Finite EΛ] [Finite R]

/-- **Lemma 3.3, "if" half, class form**: if `[X] = h ∘ [Ω ⊎ R] ∘ g` and
`[Ξ] = h ∘ [Λ ⊎ R] ∘ g` (with the orderings of `Λ ⊎ R` corresponding to those of `Ω ⊎ R`
through `α ⊎ id`, `β ⊎ id`), then `Ξ` is isomorphic to the result of an
`(Ω / Λ, α, β)`-surgery on `X`. -/
theorem classRecognition (g h : DClass G) (hg : g.cod = ((Ω.addLoose r).anchor dK cK).domWord)
    (hh : ((Ω.addLoose r).anchor dK cK).codWord = h.dom)
    (hX : (g.comp (DClass.mk ((Ω.addLoose r).anchor dK cK))).comp h = DClass.mk X)
    (hΞ : (g.comp (DClass.mk ((Λ.addLoose r).anchor (dK.mapEquiv (PGraph.liftDom α R).symm)
      (cK.mapEquiv (PGraph.liftCod β R).symm)))).comp h = DClass.mk Ξ) :
    ∃ (A : Subgraph NX EX) (hA : X.IsNormal A) (φ : Ω.Iso (X.subD A hA.edge_at)),
      Nonempty ((X.surgery α β hα hβ hA φ).Iso Ξ) := by
  obtain ⟨n₁, m₁, gD, rfl⟩ := DClass.exists_eq_mk g
  obtain ⟨n₂, m₂, hD, rfl⟩ := DClass.exists_eq_mk h
  rw [DClass.cod_mk] at hg
  rw [DClass.dom_mk] at hh
  rw [← mk_three _ _ _ hg hh] at hX
  obtain ⟨θ⟩ := (DClass.mk_eq_mk_iff _ _).1 hX
  obtain ⟨A, hA, φ, ⟨i⟩⟩ := recognition α β hα hβ θ
  have hg' := hg.trans (anchor_liftDom_domWord α β hα r dK cK).symm
  have hh' := (anchor_liftCod_codWord α β hβ r dK cK).trans hh
  rw [← mk_three _ _ _ hg' hh'] at hΞ
  obtain ⟨j⟩ := (DClass.mk_eq_mk_iff _ _).1 hΞ
  refine ⟨A, hA, φ, ⟨i.symm.trans ((isoMid (PDiagram.Iso.refl _) ?_ ?_).trans j)⟩⟩
  · intro c
    have key := AGraph.matching_eq_of (Γ := gD.toAGraph)
      (Ω := ((Λ.addLoose r).anchor (dK.mapEquiv (PGraph.liftDom α R).symm)
        (cK.mapEquiv (PGraph.liftCod β R).symm)).toAGraph)
      (σ := (gD.toAGraph.matching ((Ω.addLoose r).anchor dK cK).toAGraph
        (length_eq_of_codWord_eq hg)).trans (PGraph.liftDom α R).symm)
      (length_eq_of_codWord_eq hg') (by
        exact Enumeration.mapEquiv_trans_eq _ _ _ _
          (AGraph.domEnum_eq_mapEquiv_matching gD.toAGraph
            ((Ω.addLoose r).anchor dK cK).toAGraph (length_eq_of_codWord_eq hg)))
    exact congrArg Subtype.val (DFunLike.congr_fun key c)
  · intro k k' hk
    have : k' = k := Subtype.ext hk
    subst this
    exact DFunLike.congr_fun (AGraph.matching_eq_of
      (Γ := ((Λ.addLoose r).anchor (dK.mapEquiv (PGraph.liftDom α R).symm)
        (cK.mapEquiv (PGraph.liftCod β R).symm)).toAGraph) (Ω := hD.toAGraph)
      (σ := (PGraph.liftCod β R).trans (((Ω.addLoose r).anchor dK cK).toAGraph.matching
        hD.toAGraph (length_eq_of_codWord_eq hh)))
      (length_eq_of_codWord_eq hh') (by
        refine Eq.trans ?_ (Enumeration.mapEquiv_cancel' cK (PGraph.liftCod β R) _).symm
        exact AGraph.domEnum_eq_mapEquiv_matching ((Ω.addLoose r).anchor dK cK).toAGraph
          hD.toAGraph (length_eq_of_codWord_eq hh))) k'

end ClassRecognition

end Diagram

/-! ### Anchoring isomorphic diagrams -/

namespace PGraph.Iso

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄} {Γ : PGraph N E}
  {Γ' : PGraph N' E'}

/-- An isomorphism maps the domain bijectively onto the domain. -/
def domEquiv (i : Γ.Iso Γ') : {e // Γ.IsDom e} ≃ {e // Γ'.IsDom e} :=
  i.eE.subtypeEquiv fun e => by
    change Γ.src e = none ↔ Γ'.src (i.eE e) = none
    rw [i.src_map]
    simp

/-- An isomorphism maps the codomain bijectively onto the codomain. -/
def codEquiv (i : Γ.Iso Γ') : {e // Γ.IsCod e} ≃ {e // Γ'.IsCod e} :=
  i.eE.subtypeEquiv fun e => by
    change Γ.tgt e = none ↔ Γ'.tgt (i.eE e) = none
    rw [i.tgt_map]
    simp

end PGraph.Iso

namespace PDiagram.Iso

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄} {Γ : PDiagram G N E} {Γ' : PDiagram G N' E'}

/-- An isomorphism of diagrams is an isomorphism of the diagrams anchored by
corresponding orderings. -/
def anchor (i : Γ.Iso Γ') (d : Enumeration Γ.IsDom) (c : Enumeration Γ.IsCod) :
    (Γ.anchor d c).Iso (Γ'.anchor (d.mapEquiv i.toPIso.domEquiv) (c.mapEquiv i.toPIso.codEquiv)) where
  toIso := i.toPIso
  dom_map := by
    change (d.mapEquiv i.toPIso.domEquiv).list = d.list.map i.eE
    rw [Enumeration.mapEquiv_list, ← d.sub_map_val, List.map_map]
    rfl
  cod_map := by
    change (c.mapEquiv i.toPIso.codEquiv).list = c.list.map i.eE
    rw [Enumeration.mapEquiv_list, ← c.sub_map_val, List.map_map]
    rfl
  v₀_map := i.v₀_map
  v₁_map := i.v₁_map

end PDiagram.Iso

/-! ### Lemma 3.3 -/

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

section Sharp

variable {N : Type u₁} {E : Type u₂} (Γ : Diagram G N E) {A : Subgraph N E}
  (V : Γ.ValidLayer A) {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PDiagram G NΩ EΩ}
  (φ : Ω.Iso (Γ.subD A V.edgeAt))

/-- `Γ[L, M] = Γ' ⊎ R ≅ Ω ⊎ R` ("`cut(L) = dom(Γ') ⊎ R` and `cut(M) = cod(Γ') ⊎ R`"):
the layer is isomorphic to `Ω^♯`, by `φ⁻¹` and the identity on `R`. -/
noncomputable def layerIso :
    (Γ.layerP V.isLevel_L V.isLevel_M).Iso (Ω.addLoose (Γ.rLabel V)) :=
  PDiagram.Iso.ofProj Subtype.val Subtype.val (fun z => (φ.eN z).1) (V.edgeOf φ.toPIso)
    Subtype.val_injective (fun z z' h => φ.eN.injective (Subtype.ext h)) Subtype.val_injective
    (V.edgeOf_injective φ.toPIso)
    (fun t => ⟨fun ⟨x, hx⟩ => ⟨φ.eN.symm ⟨t, (V.node_iff t).2 (hx ▸ x.2)⟩, by simp⟩,
      fun ⟨z, hz⟩ => ⟨⟨t, hz ▸ (V.node_iff _).1 (φ.eN z).2⟩, rfl⟩⟩)
    (fun t => ⟨fun ⟨e, he⟩ => by
        subst he
        by_cases hA : A.edge e.1
        · refine ⟨.inl (φ.eE.symm ⟨e.1, hA⟩), ?_⟩
          change (φ.eE (φ.eE.symm ⟨e.1, hA⟩)).1 = e.1
          rw [Equiv.apply_symm_apply]
        · have hl : Γ.LooseIn (Γ.LayerNode V.L V.M) e.1 := by
            by_contra hl
            exact hA ((V.edge_flat_iff e.1).1 ⟨e.2, hl⟩).1
          have hcut := (Γ.layer_isLoose_iff e).1 ((Γ.sub_isLoose_iff_looseIn e).2 hl)
          exact ⟨.inr ⟨e.1, hcut.1, hcut.2, hA⟩, rfl⟩,
      fun ⟨k, hk⟩ => by
        subst hk
        rcases k with d | ρ
        · exact ⟨⟨_, V.layerEdge (φ.eE d).2⟩, rfl⟩
        · exact ⟨⟨_, (Γ.mem_layerEdge_iff V.subset _).2 (Or.inr (Or.inl ρ.2.1))⟩, rfl⟩⟩)
    (by
      intro x z h
      refine Eq.trans (PGraph.sub_ins_map_val (P := Γ.LayerNode V.L V.M)
        (Q := Γ.LayerEdge V.L V.M) x fun _ he => Γ.layerEdge_of_mem_ins V.isLevel_M x.2 he) ?_
      rw [h]
      change _ = ((Ω.ins z).map Sum.inl).map _
      rw [List.map_map, ← PGraph.sub_ins_map_val (φ.eN z) fun e he =>
        V.edgeAt _ (φ.eN z).2 e (Or.inr ((Γ.mem_ins _ e).1 he))]
      rw [show (Γ.sub A.node A.edge).ins (φ.eN z) = (Ω.ins z).map φ.eE from φ.ins_map z,
        List.map_map]
      rfl)
    (by
      intro x z h
      refine Eq.trans (PGraph.sub_outs_map_val (P := Γ.LayerNode V.L V.M)
        (Q := Γ.LayerEdge V.L V.M) x fun _ he => Γ.layerEdge_of_mem_outs V.isLevel_L x.2 he) ?_
      rw [h]
      change _ = ((Ω.outs z).map Sum.inl).map _
      rw [List.map_map, ← PGraph.sub_outs_map_val (φ.eN z) fun e he =>
        V.edgeAt _ (φ.eN z).2 e (Or.inl ((Γ.mem_outs _ e).1 he))]
      rw [show (Γ.sub A.node A.edge).outs (φ.eN z) = (Ω.outs z).map φ.eE from φ.outs_map z,
        List.map_map]
      rfl)
    (by
      intro e k h
      change Γ.val.v₀ e.1 = _
      rw [h, v₀_edgeOf])
    (by
      intro x z h
      change Γ.val.v₁ x.1 = _
      rw [h]
      exact φ.v₁_map z)

theorem edgeOf_layerIso (e : {e // Γ.LayerEdge V.L V.M e}) :
    V.edgeOf φ.toPIso ((Γ.layerIso V φ).eE e) = e.1 :=
  equivOfProj_spec Subtype.val (V.edgeOf φ.toPIso) Subtype.val_injective
    (V.edgeOf_injective φ.toPIso) _ e

/-- The ordering of `dom(Ω ⊎ R)` corresponding to an ordering of `cut(L)`. -/
noncomputable def domOrd (oL : Enumeration (Γ.Cut V.L)) :
    Enumeration (Ω.toPGraph.addLoose V.R).IsDom :=
  (oL.lift (fun e he => ((Γ.mem_layerEdge_iff V.subset e).2 (Or.inr (Or.inl he)))) _
    Γ.layer_isDom_iff).mapEquiv (Γ.layerIso V φ).toPIso.domEquiv

/-- The ordering of `cod(Ω ⊎ R)` corresponding to an ordering of `cut(M)`. -/
noncomputable def codOrd (oM : Enumeration (Γ.Cut V.M)) :
    Enumeration (Ω.toPGraph.addLoose V.R).IsCod :=
  (oM.lift (fun e he => ((Γ.mem_layerEdge_iff V.subset e).2 (Or.inr (Or.inr he)))) _
    Γ.layer_isCod_iff).mapEquiv (Γ.layerIso V φ).toPIso.codEquiv

theorem domOrd_map (oL : Enumeration (Γ.Cut V.L)) :
    (Γ.domOrd V φ oL).list.map (V.edgeOf φ.toPIso) = oL.list := by
  rw [domOrd, Enumeration.mapEquiv_list, List.map_map]
  conv_rhs => rw [← Enumeration.lift_map_val oL (fun e he =>
    ((Γ.mem_layerEdge_iff V.subset e).2 (Or.inr (Or.inl he)))) _ Γ.layer_isDom_iff,
    ← Enumeration.sub_map_val, List.map_map]
  exact List.map_congr_left fun e _ => Γ.edgeOf_layerIso V φ e.1

theorem codOrd_map (oM : Enumeration (Γ.Cut V.M)) :
    (Γ.codOrd V φ oM).list.map (V.edgeOf φ.toPIso) = oM.list := by
  rw [codOrd, Enumeration.mapEquiv_list, List.map_map]
  conv_rhs => rw [← Enumeration.lift_map_val oM (fun e he =>
    ((Γ.mem_layerEdge_iff V.subset e).2 (Or.inr (Or.inr he)))) _ Γ.layer_isCod_iff,
    ← Enumeration.sub_map_val, List.map_map]
  exact List.map_congr_left fun e _ => Γ.edgeOf_layerIso V φ e.1

variable [Finite N] [Finite E] [Finite NΩ] [Finite EΩ]

/-- The anchored layer `Γ'^♯` has the class of `Ω^♯` anchored by the corresponding
orderings. -/
theorem mk_layerD_eq (oL : Enumeration (Γ.Cut V.L)) (oM : Enumeration (Γ.Cut V.M)) :
    DClass.mk (Γ.layerD V.isLevel_L V.isLevel_M V.subset oL oM) =
      DClass.mk ((Ω.addLoose (Γ.rLabel V)).anchor (Γ.domOrd V φ oL) (Γ.codOrd V φ oM)) :=
  DClass.mk_eq_mk (PDiagram.Iso.anchor (Γ.layerIso V φ) _ _)

end Sharp

variable {N : Type u₁} {E : Type u₂} (Γ : Diagram G N E) {NΞ : Type u₃} {EΞ : Type u₄}
  (Ξ : Diagram G NΞ EΞ) {NΩ : Type u₅} {EΩ : Type u₆} {Ω : PDiagram G NΩ EΩ}
  {NΛ : Type u₇} {EΛ : Type u₈} {Λ : PDiagram G NΛ EΛ}
  (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e})
  (hα : ∀ e, Ω.val.v₀ (α e).1 = Λ.val.v₀ e.1) (hβ : ∀ e, Ω.val.v₀ (β e).1 = Λ.val.v₀ e.1)
  [Finite N] [Finite E] [Finite NΞ] [Finite EΞ] [Finite NΩ] [Finite EΩ] [Finite NΛ]
  [Finite EΛ]

omit [Finite N] [Finite E] [Finite NΩ] [Finite EΩ] [Finite NΛ] [Finite EΛ] in
theorem domOrd_eq {A : Subgraph N E} (V : Γ.ValidLayer A) (φ : Ω.Iso (Γ.subD A V.edgeAt))
    (oL : Enumeration (Γ.Cut V.L)) (dΛ : Enumeration (Λ.toPGraph.addLoose V.R).IsDom)
    (hd : oL.list = dΛ.sub.map fun k => V.edgeOf φ.toPIso (PGraph.liftDom α V.R k).1) :
    dΛ = (Γ.domOrd V φ oL).mapEquiv (PGraph.liftDom α V.R).symm := by
  rw [← Enumeration.mapEquiv_eq_of_map dΛ (Γ.domOrd V φ oL) (PGraph.liftDom α V.R)
    (V.edgeOf φ.toPIso) (V.edgeOf_injective φ.toPIso) ((Γ.domOrd_map V φ oL).trans hd),
    Enumeration.mapEquiv_symm]

omit [Finite N] [Finite E] [Finite NΩ] [Finite EΩ] [Finite NΛ] [Finite EΛ] in
theorem codOrd_eq {A : Subgraph N E} (V : Γ.ValidLayer A) (φ : Ω.Iso (Γ.subD A V.edgeAt))
    (oM : Enumeration (Γ.Cut V.M)) (cΛ : Enumeration (Λ.toPGraph.addLoose V.R).IsCod)
    (hc : oM.list = cΛ.sub.map fun k => V.edgeOf φ.toPIso (PGraph.liftCod β V.R k).1) :
    cΛ = (Γ.codOrd V φ oM).mapEquiv (PGraph.liftCod β V.R).symm := by
  rw [← Enumeration.mapEquiv_eq_of_map cΛ (Γ.codOrd V φ oM) (PGraph.liftCod β V.R)
    (V.edgeOf φ.toPIso) (V.edgeOf_injective φ.toPIso) ((Γ.codOrd_map V φ oM).trans hc),
    Enumeration.mapEquiv_symm]

/-- **Lemma 3.3.** "Let `((Ω, u) / (Λ, w), α, β)` be a template. An anchored diagram
`(Ξ, t)` is isomorphic to the result of a surgery on `(Γ, v)` with this template if and
only if there are
* a normal subgraph `Γ' ⊆ Γ` and an isomorphism of diagrams `φ : (Ω, u) → (Γ', v')`,
* total orderings that anchor `Γ'^♯` and `Λ^♯` such that the bijections
  `dom(Λ^♯) → dom(Γ'^♯)` and `cod(Λ^♯) → cod(Γ'^♯)` given by `φ ∘ α`, `φ ∘ β`, and the
  identity on `Γ'^♯ ∖ Γ'` are order-preserving,
* morphisms `g`, `h` in `F_s(G)`
such that `h ∘ [Γ'^♯, v'^♯] ∘ g = [Γ, v]` and `h ∘ [Λ^♯, w^♯] ∘ g = [Ξ, t]`."

`Γ'^♯ = Γ[L, M]` is anchored by orderings `oL`, `oM` of `cut(L)`, `cut(M)` (Stage 1's
`layerD`, with the restriction `v'^♯` of `v`), `Λ^♯ = Λ ⊎ R` by orderings `dΛ`, `cΛ` (with
`w^♯ = w ⊎ v|_R`); order preservation says that `φ ∘ α ⊎ id` carries `dΛ` to `oL` and
`φ ∘ β ⊎ id` carries `cΛ` to `oM`.  The morphisms are classes with the matching domain and
codomain words, and the composites are taken in the bracketing `h ∘ (X ∘ g)`. -/
theorem lemma_3_3 :
    (∃ (A : Subgraph N E) (hA : Γ.IsNormal A) (φ : Ω.Iso (Γ.subD A hA.edge_at)),
      Nonempty (Ξ.Iso (Γ.surgery α β hα hβ hA φ))) ↔
    ∃ (A : Subgraph N E) (hA : Γ.IsNormal A) (φ : Ω.Iso (Γ.subD A hA.edge_at))
      (oL : Enumeration (Γ.Cut hA.sharpLayer.L)) (oM : Enumeration (Γ.Cut hA.sharpLayer.M))
      (dΛ : Enumeration (Λ.toPGraph.addLoose hA.sharpLayer.R).IsDom)
      (cΛ : Enumeration (Λ.toPGraph.addLoose hA.sharpLayer.R).IsCod),
      oL.list = dΛ.sub.map (fun k =>
        hA.sharpLayer.edgeOf φ.toPIso (PGraph.liftDom α hA.sharpLayer.R k).1) ∧
      oM.list = cΛ.sub.map (fun k =>
        hA.sharpLayer.edgeOf φ.toPIso (PGraph.liftCod β hA.sharpLayer.R k).1) ∧
      ∃ g h : DClass G,
        g.cod = (DClass.mk (Γ.layerD hA.sharpLayer.isLevel_L hA.sharpLayer.isLevel_M
          hA.sharpLayer.subset oL oM)).dom ∧
        (DClass.mk (Γ.layerD hA.sharpLayer.isLevel_L hA.sharpLayer.isLevel_M
          hA.sharpLayer.subset oL oM)).cod = h.dom ∧
        (g.comp (DClass.mk (Γ.layerD hA.sharpLayer.isLevel_L hA.sharpLayer.isLevel_M
          hA.sharpLayer.subset oL oM))).comp h = DClass.mk Γ ∧
        (g.comp (DClass.mk ((Λ.addLoose (Γ.rLabel hA.sharpLayer)).anchor dΛ cΛ))).comp h =
          DClass.mk Ξ := by
  constructor
  · rintro ⟨A, hA, φ, ⟨i⟩⟩
    set V := hA.sharpLayer
    let oL : Enumeration (Γ.Cut V.L) := Enumeration.ofFinite _
    let oM : Enumeration (Γ.Cut V.M) := Enumeration.ofFinite _
    have hlay := Γ.mk_layerD_eq V φ oL oM
    refine ⟨A, hA, φ, oL, oM, (Γ.domOrd V φ oL).mapEquiv (PGraph.liftDom α V.R).symm,
      (Γ.codOrd V φ oM).mapEquiv (PGraph.liftCod β V.R).symm, ?_, ?_,
      DClass.mk (Γ.lowerA V φ (Γ.domOrd V φ oL)), DClass.mk (Γ.upperA V φ (Γ.codOrd V φ oM)),
      ?_, ?_, ?_, ?_⟩
    · rw [Enumeration.sub_mapEquiv, List.map_map, ← Γ.domOrd_map V φ oL,
        ← Enumeration.sub_map_val, List.map_map]
      exact List.map_congr_left fun k _ => by
        change _ = V.edgeOf φ.toPIso (PGraph.liftDom α V.R ((PGraph.liftDom α V.R).symm k)).1
        rw [Equiv.apply_symm_apply]
        rfl
    · rw [Enumeration.sub_mapEquiv, List.map_map, ← Γ.codOrd_map V φ oM,
        ← Enumeration.sub_map_val, List.map_map]
      exact List.map_congr_left fun k _ => by
        change _ = V.edgeOf φ.toPIso (PGraph.liftCod β V.R ((PGraph.liftCod β V.R).symm k)).1
        rw [Equiv.apply_symm_apply]
        rfl
    · change _ = (DClass.mk (Γ.layerD V.isLevel_L V.isLevel_M V.subset oL oM)).dom
      rw [hlay, DClass.cod_mk, DClass.dom_mk]
      exact Γ.lowerA_codWord V φ _ (Γ.codOrd V φ oM)
    · change (DClass.mk (Γ.layerD V.isLevel_L V.isLevel_M V.subset oL oM)).cod = _
      rw [hlay, DClass.cod_mk, DClass.dom_mk]
      exact Γ.midΩ_codWord V φ _ _
    · change DClass.comp (DClass.comp _
        (DClass.mk (Γ.layerD V.isLevel_L V.isLevel_M V.subset oL oM))) _ = _
      rw [hlay]
      exact (Γ.mk_eq_decomp V φ _ _).symm
    · rw [DClass.mk_eq_mk i, Γ.mk_surgeryAt_eq_decomp V φ α β hα hβ]
  · rintro ⟨A, hA, φ, oL, oM, dΛ, cΛ, hd, hc, g, h, hg, hh, hΓ, hΞ⟩
    have hlay := Γ.mk_layerD_eq hA.sharpLayer φ oL oM
    rw [hlay, DClass.dom_mk] at hg
    rw [hlay, DClass.cod_mk] at hh
    rw [hlay] at hΓ
    rw [Γ.domOrd_eq α hA.sharpLayer φ oL dΛ hd, Γ.codOrd_eq β hA.sharpLayer φ oM cΛ hc] at hΞ
    obtain ⟨A', hA', φ', ⟨i⟩⟩ :=
      classRecognition Γ Ξ α β hα hβ (Γ.rLabel hA.sharpLayer) _ _ g h hg hh hΓ hΞ
    exact ⟨A', hA', φ', ⟨i.symm⟩⟩

end Diagram

end FreeMarkov
