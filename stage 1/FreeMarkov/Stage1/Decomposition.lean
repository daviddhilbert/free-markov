/-
Free Markov categories, Stage 1: Remark 2.4, the decomposition of a diagram into
layers, for every choice of total orderings of the cuts.

The key fact is that gluing two consecutive layers `Γ[L, M]` and `Γ[M, K]` along
`cut(M)` gives the layer `Γ[L, K]` (`Diagram.glueLayersIso`), for any orderings of
`cut(L)`, `cut(M)`, `cut(K)`.  No cited result is used.
-/
module

public import FreeMarkov.Stage1.Layers

@[expose] public section

universe w v u₁ u₂

namespace FreeMarkov

open PGraph

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  (Γ : Diagram G N E)

theorem layerD_domWord {L M : Set N} (hL : Γ.IsLevel L) (hM : Γ.IsLevel M) (hLM : L ⊆ M)
    (oL : Enumeration (Γ.Cut L)) (oM : Enumeration (Γ.Cut M)) :
    (Γ.layerD hL hM hLM oL oM).domWord = FreeMonoid.ofList (oL.list.map Γ.val.v₀) := by
  rw [← Γ.layerD_dom_map_val hL hM hLM oL oM, List.map_map]
  rfl

theorem layerD_codWord {L M : Set N} (hL : Γ.IsLevel L) (hM : Γ.IsLevel M) (hLM : L ⊆ M)
    (oL : Enumeration (Γ.Cut L)) (oM : Enumeration (Γ.Cut M)) :
    (Γ.layerD hL hM hLM oL oM).codWord = FreeMonoid.ofList (oM.list.map Γ.val.v₀) := by
  rw [← Γ.layerD_cod_map_val hL hM hLM oL oM, List.map_map]
  rfl

theorem layerD_codWord_eq_domWord {L M K : Set N} (hL : Γ.IsLevel L) (hM : Γ.IsLevel M)
    (hK : Γ.IsLevel K) (hLM : L ⊆ M) (hMK : M ⊆ K) (oL : Enumeration (Γ.Cut L))
    (oM : Enumeration (Γ.Cut M)) (oK : Enumeration (Γ.Cut K)) :
    (Γ.layerD hL hM hLM oL oM).codWord = (Γ.layerD hM hK hMK oM oK).domWord := by
  rw [layerD_codWord, layerD_domWord]

theorem ins_map_val_layerD {L M : Set N} (hL : Γ.IsLevel L) (hM : Γ.IsLevel M) (hLM : L ⊆ M)
    (oL : Enumeration (Γ.Cut L)) (oM : Enumeration (Γ.Cut M)) (x : {x // Γ.LayerNode L M x}) :
    ((Γ.layerD hL hM hLM oL oM).ins x).map Subtype.val = Γ.ins x.1 :=
  sub_ins_map_val x fun _ he => Γ.layerEdge_of_mem_ins hM x.2 he

theorem outs_map_val_layerD {L M : Set N} (hL : Γ.IsLevel L) (hM : Γ.IsLevel M) (hLM : L ⊆ M)
    (oL : Enumeration (Γ.Cut L)) (oM : Enumeration (Γ.Cut M)) (x : {x // Γ.LayerNode L M x}) :
    ((Γ.layerD hL hM hLM oL oM).outs x).map Subtype.val = Γ.outs x.1 :=
  sub_outs_map_val x fun _ he => Γ.layerEdge_of_mem_outs hL x.2 he

section Glue

variable {L M K : Set N} (hL : Γ.IsLevel L) (hM : Γ.IsLevel M) (hK : Γ.IsLevel K)
  (hLM : L ⊆ M) (hMK : M ⊆ K) (oL : Enumeration (Γ.Cut L)) (oM : Enumeration (Γ.Cut M))
  (oK : Enumeration (Γ.Cut K))

/-- The nodes of `Γ[L, M]` and of `Γ[M, K]` together are those of `Γ[L, K]`. -/
noncomputable def glueLayersNodeEquiv :
    {x // Γ.LayerNode L M x} ⊕ {x // Γ.LayerNode M K x} ≃ {x // Γ.LayerNode L K x} := by
  classical
  refine Equiv.ofBijective
    (Sum.elim (fun x => ⟨x.1, hMK x.2.1, x.2.2⟩) (fun y => ⟨y.1, y.2.1, fun h => y.2.2 (hLM h)⟩))
    ⟨?_, ?_⟩
  · rintro (x | x) (y | y) h <;> simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact (y.2.2 (h ▸ x.2.1)).elim
    · exact (x.2.2 (h ▸ y.2.1)).elim
    · exact congrArg Sum.inr (Subtype.ext h)
  · rintro ⟨z, hzK, hzL⟩
    by_cases hzM : z ∈ M
    · exact ⟨.inl ⟨z, hzM, hzL⟩, rfl⟩
    · exact ⟨.inr ⟨z, hzK, hzM⟩, rfl⟩

theorem glueLayersNodeEquiv_val (n : {x // Γ.LayerNode L M x} ⊕ {x // Γ.LayerNode M K x}) :
    (Γ.glueLayersNodeEquiv hLM hMK n).1 = Sum.elim Subtype.val Subtype.val n := by
  cases n <;> rfl

/-- The second layer, `Γ[M, K]`, anchored. -/
local notation "B" => Γ.layerD hM hK hMK oM oK

/-- The first layer, `Γ[L, M]`, anchored. -/
local notation "A" => Γ.layerD hL hM hLM oL oM

theorem layerD_src_ne_none_iff (e : {e // Γ.LayerEdge M K e}) :
    (B).src e ≠ none ↔ ∃ x, Γ.src e.1 = some x ∧ Γ.LayerNode M K x := by
  change (Γ.layer M K).src e ≠ none ↔ _
  rw [Ne, layer, sub_src_eq_none_iff]
  simp only [not_forall, not_not, exists_prop]

/-- The edges of `Γ[L, M]` and the edges of `Γ[M, K]` with an inner source together
are those of `Γ[L, K]`. -/
noncomputable def glueLayersEdgeEquiv :
    {e // Γ.LayerEdge L M e} ⊕ (B).InnerSrc ≃ {e // Γ.LayerEdge L K e} := by
  classical
  refine Equiv.ofBijective
    (Sum.elim (fun e => ⟨e.1, fun x hx => hMK (e.2.1 x hx), e.2.2⟩)
      (fun b => ⟨b.1.1, b.1.2.1, fun y hy hyL => b.1.2.2 y hy (hLM hyL)⟩)) ⟨?_, ?_⟩
  · have key : ∀ (e : {e // Γ.LayerEdge L M e}) (b : (B).InnerSrc), e.1 ≠ b.1.1 := by
      intro e b h
      obtain ⟨x, hx, hxM⟩ := (Γ.layerD_src_ne_none_iff hM hK hMK oM oK b.1).1 b.2
      rw [← h] at hx
      exact hxM.2 (e.2.1 x hx)
    rintro (e | e) (f | f) h <;> simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact (key e f h).elim
    · exact (key f e h.symm).elim
    · exact congrArg Sum.inr (Subtype.ext (Subtype.ext h))
  · rintro ⟨c, hcK, hcL⟩
    by_cases hc : ∃ x, Γ.src c = some x ∧ x ∉ M
    · obtain ⟨x, hx, hxM⟩ := hc
      have hcM : Γ.TgtIn Mᶜ c := fun y hy hyM => hxM (hM x y (Γ.lt_of_edge hx hy) hyM)
      refine ⟨.inr ⟨⟨c, hcK, hcM⟩, ?_⟩, rfl⟩
      exact (Γ.layerD_src_ne_none_iff hM hK hMK oM oK _).2 ⟨x, hx, hcK x hx, hxM⟩
    · simp only [not_exists, not_and, not_not] at hc
      exact ⟨.inl ⟨c, fun x hx => hc x hx, hcL⟩, rfl⟩

@[simp] theorem glueLayersEdgeEquiv_inl (e : {e // Γ.LayerEdge L M e}) :
    (Γ.glueLayersEdgeEquiv hM hK hLM hMK oM oK (.inl e)).1 = e.1 := rfl

@[simp] theorem glueLayersEdgeEquiv_inr (b : (B).InnerSrc) :
    (Γ.glueLayersEdgeEquiv hM hK hLM hMK oM oK (.inr b)).1 = b.1.1 := rfl

theorem glueLayers_matching_val (c : {e // (A).IsCod e}) :
    ((A).matching (B).toAGraph (length_eq_of_codWord_eq
      (Γ.layerD_codWord_eq_domWord hL hM hK hLM hMK oL oM oK)) c).1.1 = c.1.1 :=
  Enumeration.matching_spec _ _ _ Subtype.val Subtype.val
    ((Γ.layerD_cod_map_val hL hM hLM oL oM).trans (Γ.layerD_dom_map_val hM hK hMK oM oK).symm) c

theorem glueLayersEdgeEquiv_glueIn (e : {e // Γ.LayerEdge M K e}) :
    (Γ.glueLayersEdgeEquiv hM hK hLM hMK oM oK (PGraph.glueIn ((A).matching (B).toAGraph
      (length_eq_of_codWord_eq (Γ.layerD_codWord_eq_domWord hL hM hK hLM hMK oL oM oK))) e)).1 =
      e.1 := by
  by_cases h : (B).src e = none
  · rw [PGraph.glueIn_of_eq_none _ h, glueLayersEdgeEquiv_inl]
    rw [← Γ.glueLayers_matching_val hL hM hK hLM hMK oL oM oK, Equiv.apply_symm_apply]
  · rw [PGraph.glueIn_of_ne_none _ h, glueLayersEdgeEquiv_inr]

/-- **Gluing consecutive layers.** For levels `L ⊆ M ⊆ K` and any total orderings of
`cut(L)`, `cut(M)`, `cut(K)`, gluing `Γ[L, M]` and `Γ[M, K]` along `cut(M)` gives
`Γ[L, K]`, up to isomorphism of diagrams. -/
noncomputable def glueLayersIso (hLK : L ⊆ K) :
    ((A).glue (B) (Γ.layerD_codWord_eq_domWord hL hM hK hLM hMK oL oM oK)).Iso
      (Γ.layerD hL hK hLK oL oK) where
  eN := Γ.glueLayersNodeEquiv hLM hMK
  eE := Γ.glueLayersEdgeEquiv hM hK hLM hMK oM oK
  ins_map n := by
    refine List.map_injective_iff.2 Subtype.val_injective ?_
    rw [ins_map_val_layerD, glueLayersNodeEquiv_val, List.map_map]
    cases n with
    | inl x =>
      change Γ.ins x.1 = ((((A).ins x).map Sum.inl).map _)
      rw [List.map_map, ← Γ.ins_map_val_layerD hL hM hLM oL oM x]
      rfl
    | inr y =>
      change Γ.ins y.1 = (((B).ins y).map (PGraph.glueIn _)).map _
      rw [List.map_map, ← Γ.ins_map_val_layerD hM hK hMK oM oK y]
      exact List.map_congr_left fun e _ =>
        (Γ.glueLayersEdgeEquiv_glueIn hL hM hK hLM hMK oL oM oK e).symm
  outs_map n := by
    refine List.map_injective_iff.2 Subtype.val_injective ?_
    rw [outs_map_val_layerD, glueLayersNodeEquiv_val, List.map_map]
    cases n with
    | inl x =>
      change Γ.outs x.1 = ((((A).outs x).map Sum.inl).map _)
      rw [List.map_map, ← Γ.outs_map_val_layerD hL hM hLM oL oM x]
      rfl
    | inr y =>
      change Γ.outs y.1 = (((B).outs y).map (PGraph.glueIn _)).map _
      rw [List.map_map, ← Γ.outs_map_val_layerD hM hK hMK oM oK y]
      exact List.map_congr_left fun e _ =>
        (Γ.glueLayersEdgeEquiv_glueIn hL hM hK hLM hMK oL oM oK e).symm
  dom_map := by
    refine List.map_injective_iff.2 Subtype.val_injective ?_
    rw [layerD_dom_map_val, List.map_map]
    change oL.list = (((A).dom.map Sum.inl).map _)
    rw [List.map_map, ← Γ.layerD_dom_map_val hL hM hLM oL oM]
    rfl
  cod_map := by
    refine List.map_injective_iff.2 Subtype.val_injective ?_
    rw [layerD_cod_map_val, List.map_map]
    change oK.list = (((B).cod.map (PGraph.glueIn _)).map _)
    rw [List.map_map, ← Γ.layerD_cod_map_val hM hK hMK oM oK]
    exact List.map_congr_left fun e _ =>
      (Γ.glueLayersEdgeEquiv_glueIn hL hM hK hLM hMK oL oM oK e).symm
  v₀_map e := by
    cases e with
    | inl e => rfl
    | inr b => rfl
  v₁_map n := by
    cases n with
    | inl x => rfl
    | inr y => rfl

end Glue

/-- The whole diagram as the layer `Γ[∅, Γ̇]`, anchored by `dom(Γ)` and `cod(Γ)`. -/
noncomputable def wholeLayer : Diagram G {x // Γ.LayerNode ∅ Set.univ x}
    {e // Γ.LayerEdge ∅ Set.univ e} :=
  Γ.layerD Γ.isLevel_empty Γ.isLevel_univ (Set.empty_subset _) Γ.cutEmptyEnum Γ.cutUnivEnum

/-- A diagram is isomorphic to its layer `Γ[∅, Γ̇]`. -/
noncomputable def isoWholeLayer : Γ.Iso Γ.wholeLayer where
  eN := Equiv.ofBijective (fun x => ⟨x, Set.mem_univ x, Set.notMem_empty x⟩)
    ⟨fun _ _ h => congrArg Subtype.val h, fun y => ⟨y.1, rfl⟩⟩
  eE := Equiv.ofBijective (fun e => ⟨e, fun _ _ => Set.mem_univ _, fun _ _ => Set.notMem_empty _⟩)
    ⟨fun _ _ h => congrArg Subtype.val h, fun y => ⟨y.1, rfl⟩⟩
  ins_map x := by
    refine List.map_injective_iff.2 Subtype.val_injective ?_
    rw [wholeLayer, ins_map_val_layerD, List.map_map]
    exact (List.map_id _).symm
  outs_map x := by
    refine List.map_injective_iff.2 Subtype.val_injective ?_
    rw [wholeLayer, outs_map_val_layerD, List.map_map]
    exact (List.map_id _).symm
  dom_map := by
    refine List.map_injective_iff.2 Subtype.val_injective ?_
    rw [wholeLayer, layerD_dom_map_val, List.map_map]
    exact (List.map_id _).symm
  cod_map := by
    refine List.map_injective_iff.2 Subtype.val_injective ?_
    rw [wholeLayer, layerD_cod_map_val, List.map_map]
    exact (List.map_id _).symm
  v₀_map _ := rfl
  v₁_map _ := rfl

/-- The lower layer `Γ[∅, L]`, anchored by `dom(Γ)` and a chosen ordering of
`cut(L)`. -/
noncomputable abbrev lowerD {L : Set N} (hL : Γ.IsLevel L) (oL : Enumeration (Γ.Cut L)) :=
  Γ.layerD Γ.isLevel_empty hL (Set.empty_subset _) Γ.cutEmptyEnum oL

/-- The upper layer `Γ[M, Γ̇]`, anchored by a chosen ordering of `cut(M)` and
`cod(Γ)`. -/
noncomputable abbrev upperD {M : Set N} (hM : Γ.IsLevel M) (oM : Enumeration (Γ.Cut M)) :=
  Γ.layerD hM Γ.isLevel_univ (Set.subset_univ _) oM Γ.cutUnivEnum

variable [Finite N] [Finite E]

/-- The two-piece decomposition `[Γ] = [Γ[L, Γ̇]] ∘ [Γ[∅, L]]`, for any ordering of
`cut(L)`. -/
theorem mk_eq_comp_lower_upper {L : Set N} (hL : Γ.IsLevel L) (oL : Enumeration (Γ.Cut L)) :
    DClass.mk Γ = (DClass.mk (Γ.lowerD hL oL)).comp (DClass.mk (Γ.upperD hL oL)) := by
  rw [DClass.mk_comp _ _ (Γ.layerD_codWord_eq_domWord _ _ _ _ _ _ _ _)]
  exact DClass.mk_eq_mk (Γ.isoWholeLayer.trans
    (Γ.glueLayersIso Γ.isLevel_empty hL Γ.isLevel_univ (Set.empty_subset _)
      (Set.subset_univ _) Γ.cutEmptyEnum oL Γ.cutUnivEnum (Set.empty_subset _)).symm)

/-- **Remark 2.4** (layer decomposition). For levels `L ⊆ M` of an anchored diagram
`Γ` and *any* total orderings `oL` of `cut(L)` and `oM` of `cut(M)`,
`[Γ, v] = [Γ[M, Γ̇], v₃] ∘ [Γ[L, M], v₂] ∘ [Γ[∅, L], v₁]`, where the layers carry the
induced valuations and the anchorings `dom(Γ)`, `oL`, `oM`, `cod(Γ)`; in this
bracketing. -/
theorem remark_2_4 {L M : Set N} (hL : Γ.IsLevel L) (hM : Γ.IsLevel M) (hLM : L ⊆ M)
    (oL : Enumeration (Γ.Cut L)) (oM : Enumeration (Γ.Cut M)) :
    DClass.mk Γ = (DClass.mk (Γ.lowerD hL oL)).comp
      ((DClass.mk (Γ.layerD hL hM hLM oL oM)).comp (DClass.mk (Γ.upperD hM oM))) := by
  rw [DClass.mk_comp _ _ (Γ.layerD_codWord_eq_domWord _ _ _ _ _ _ _ _),
    DClass.mk_comp _ _ (by
      rw [glue_domWord]
      exact Γ.layerD_codWord_eq_domWord _ _ _ _ _ _ _ _)]
  refine DClass.mk_eq_mk (Γ.isoWholeLayer.trans ?_)
  refine (Γ.glueLayersIso Γ.isLevel_empty hL Γ.isLevel_univ (Set.empty_subset _)
      (Set.subset_univ _) Γ.cutEmptyEnum oL Γ.cutUnivEnum (Set.empty_subset _)).symm.trans ?_
  exact (Iso.refl _).glue (Γ.glueLayersIso hL hM Γ.isLevel_univ hLM (Set.subset_univ _) oL oM
    Γ.cutUnivEnum (Set.subset_univ _)).symm _ _

/-- **Remark 2.4**, the other bracketing:
`[Γ, v] = [Γ[M, Γ̇], v₃] ∘ ([Γ[L, M], v₂] ∘ [Γ[∅, L], v₁])`. -/
theorem remark_2_4' {L M : Set N} (hL : Γ.IsLevel L) (hM : Γ.IsLevel M) (hLM : L ⊆ M)
    (oL : Enumeration (Γ.Cut L)) (oM : Enumeration (Γ.Cut M)) :
    DClass.mk Γ = ((DClass.mk (Γ.lowerD hL oL)).comp
      (DClass.mk (Γ.layerD hL hM hLM oL oM))).comp (DClass.mk (Γ.upperD hM oM)) := by
  rw [DClass.mk_comp _ _ (Γ.layerD_codWord_eq_domWord _ _ _ _ _ _ _ _),
    DClass.mk_comp _ _ (by
      rw [glue_codWord]
      exact Γ.layerD_codWord_eq_domWord _ _ _ _ _ _ _ _)]
  refine DClass.mk_eq_mk (Γ.isoWholeLayer.trans ?_)
  refine (Γ.glueLayersIso Γ.isLevel_empty hM Γ.isLevel_univ (Set.empty_subset _)
      (Set.subset_univ _) Γ.cutEmptyEnum oM Γ.cutUnivEnum (Set.empty_subset _)).symm.trans ?_
  exact (Γ.glueLayersIso Γ.isLevel_empty hL hM (Set.empty_subset _) hLM Γ.cutEmptyEnum oL oM
    (Set.empty_subset _)).symm.glue (Iso.refl _) _ _

end Diagram

end FreeMarkov
