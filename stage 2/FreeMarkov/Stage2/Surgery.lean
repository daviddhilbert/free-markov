/-
Free Markov categories, Stage 2: the surgery `Γ^Ω_Λ(φ, α, β)` of Section 3.

"Write `Γ'^♯ = Γ[L, M]` and let `R` be the set of the loose edges of `Γ[L, M]` that are
not in `Γ'`, so that `cut(L) = dom(Γ') ⊎ R` and `cut(M) = cod(Γ') ⊎ R` by Lemma 3.2.
Let `Λ^♯ = Λ ⊎ R`, where the edges in `R` are loose. Then `Γ^Ω_Λ` is obtained from the
disjoint union of `Γ[∅, L]`, `Λ^♯`, and `Γ[M, Γ̇]` by gluing `cod(Γ[∅, L]) = cut(L)` to
`dom(Λ^♯)` and `cod(Λ^♯)` to `dom(Γ[M, Γ̇]) = cut(M)`, in the same way as in the
composition of `F_s(G)`, along the bijections given by `φ ∘ α`, `φ ∘ β`, and the
identity on `R`."

The construction is made for any layer `Γ[L, M]` as in Lemma 3.2 (`surgeryAt`); the
surgery of the paper uses `Γ'^♯` (`surgery`).  That the result does not depend on the
choice of the layer is proved in `Canonical.lean` (proof of Lemma 3.3).  No directed
circuit arises because a gluing never creates one (`PGraph.glue`, Stage 1).
-/
module

public import FreeMarkov.Stage2.Gluing

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇

namespace FreeMarkov

open Relation

/-! ### Edges of the lower and upper layers -/

namespace PGraph

variable {N : Type u₁} {E : Type u₂} {Γ : PGraph N E}

theorem lowerEdge_of_cut {L : Set N} {e : E} (h : Γ.Cut L e) : Γ.LayerEdge ∅ L e :=
  ⟨h.1, fun _ _ => Set.notMem_empty _⟩

theorem upperEdge_of_cut {M : Set N} {e : E} (h : Γ.Cut M e) : Γ.LayerEdge M Set.univ e :=
  ⟨fun _ _ => Set.mem_univ _, h.2⟩

theorem lowerEdge_of_isDom (L : Set N) {e : E} (h : Γ.IsDom e) : Γ.LayerEdge ∅ L e :=
  ⟨fun x hx => (by rw [h] at hx; cases hx), fun _ _ => Set.notMem_empty _⟩

theorem upperEdge_of_isCod (M : Set N) {e : E} (h : Γ.IsCod e) : Γ.LayerEdge M Set.univ e :=
  ⟨fun _ _ => Set.mem_univ _, fun y hy => (by rw [h] at hy; cases hy)⟩

end PGraph

namespace AGraph

variable {N : Type u₁} {E : Type u₂} (Γ : AGraph N E)

/-- `dom(Γ) = cut(∅)`, in the ordering of `dom(Γ)`. -/
def domCut : Enumeration (Γ.Cut ∅) :=
  ⟨Γ.dom, Γ.dom_nodup, fun e => by rw [Γ.cut_empty_iff]; exact Γ.mem_dom e⟩

/-- `cod(Γ) = cut(Γ̇)`, in the ordering of `cod(Γ)`. -/
def codCut : Enumeration (Γ.Cut Set.univ) :=
  ⟨Γ.cod, Γ.cod_nodup, fun e => by rw [Γ.cut_univ_iff]; exact Γ.mem_cod e⟩

/-- `dom(Γ[∅, L]) = dom(Γ)`, in the ordering of `dom(Γ)`. -/
def lowerDom (L : Set N) : Enumeration (Γ.layer ∅ L).IsDom :=
  Γ.domCut.lift (fun _ he => PGraph.lowerEdge_of_isDom L ((Γ.cut_empty_iff _).1 he)) _
    Γ.layer_isDom_iff

/-- `cod(Γ[M, Γ̇]) = cod(Γ)`, in the ordering of `cod(Γ)`. -/
def upperCod (M : Set N) : Enumeration (Γ.layer M Set.univ).IsCod :=
  Γ.codCut.lift (fun _ he => PGraph.upperEdge_of_isCod M ((Γ.cut_univ_iff _).1 he)) _
    Γ.layer_isCod_iff

theorem lowerDom_map_val (L : Set N) : (Γ.lowerDom L).list.map Subtype.val = Γ.dom :=
  Enumeration.lift_map_val _ _ _ _

theorem upperCod_map_val (M : Set N) : (Γ.upperCod M).list.map Subtype.val = Γ.cod :=
  Enumeration.lift_map_val _ _ _ _

end AGraph

/-! ### The data of the surgery -/

namespace PGraph

variable {N : Type u₁} {E : Type u₂} {Γ : PGraph N E} {A : Subgraph N E}
  {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PGraph NΩ EΩ}

section Iso

variable (φ : Ω.Iso (Γ.sub A.node A.edge))

theorem sub_iso_src_eq_none_iff (d : EΩ) :
    Ω.src d = none ↔ ∀ x, Γ.src (φ.eE d).1 = some x → ¬ A.node x := by
  rw [← sub_src_eq_none_iff, φ.src_map]
  simp

theorem sub_iso_tgt_eq_none_iff (d : EΩ) :
    Ω.tgt d = none ↔ ∀ y, Γ.tgt (φ.eE d).1 = some y → ¬ A.node y := by
  rw [← sub_tgt_eq_none_iff, φ.tgt_map]
  simp

theorem sub_iso_src_eq_some {d : EΩ} {z : NΩ} (h : Ω.src d = some z) :
    Γ.src (φ.eE d).1 = some (φ.eN z).1 := by
  rw [← sub_src_eq_some_iff, φ.src_map, h]
  rfl

theorem sub_iso_tgt_eq_some {d : EΩ} {z : NΩ} (h : Ω.tgt d = some z) :
    Γ.tgt (φ.eE d).1 = some (φ.eN z).1 := by
  rw [← sub_tgt_eq_some_iff, φ.tgt_map, h]
  rfl

end Iso

variable (V : Γ.ValidLayer A)

/-- The set `R` of the loose edges of `Γ[L, M]` that are not in `Γ'`: the edges cut by
both `L` and `M` that are not in `Γ'`. -/
def ValidLayer.R : Type u₂ := {e : E // Γ.Cut V.L e ∧ Γ.Cut V.M e ∧ ¬ A.edge e}

instance ValidLayer.finite_R [Finite E] : Finite V.R := Subtype.finite

variable (φ : Ω.Iso (Γ.sub A.node A.edge))

/-- The edge of `Γ` underlying an edge of `Ω^♯ = Ω ⊎ R`: `φ` on `Ω`, the identity on `R`. -/
def ValidLayer.edgeOf (k : EΩ ⊕ V.R) : E := Sum.elim (fun d => (φ.eE d).1) Subtype.val k

theorem ValidLayer.edgeOf_injective : Function.Injective (V.edgeOf φ) := by
  rintro (d | r) (d' | r') h
  · exact congrArg Sum.inl (φ.eE.injective (Subtype.ext h))
  · change (φ.eE d).1 = r'.1 at h
    exact (r'.2.2.2 (h ▸ (φ.eE d).2)).elim
  · change r.1 = (φ.eE d').1 at h
    exact (r.2.2.2 (h.symm ▸ (φ.eE d').2)).elim
  · exact congrArg Sum.inr (Subtype.ext h)

theorem ValidLayer.cut_L_edgeOf {k : EΩ ⊕ V.R} (hk : (Ω.addLoose V.R).IsDom k) :
    Γ.Cut V.L (V.edgeOf φ k) := by
  rcases k with d | r
  · exact V.cut_L_of_dom (φ.eE d).2 ((sub_iso_src_eq_none_iff φ d).1 hk)
  · exact r.2.1

theorem ValidLayer.cut_M_edgeOf {k : EΩ ⊕ V.R} (hk : (Ω.addLoose V.R).IsCod k) :
    Γ.Cut V.M (V.edgeOf φ k) := by
  rcases k with d | r
  · exact V.cut_M_of_cod (φ.eE d).2 ((sub_iso_tgt_eq_none_iff φ d).1 hk)
  · exact r.2.2.1

/-- The bijection `dom(Ω^♯) → cod(Γ[∅, L]) = cut(L)` given by `φ` and the identity on
`R` (`cut(L) = dom(Γ') ⊎ R`). -/
noncomputable def ValidLayer.domMatch :
    {k // (Ω.addLoose V.R).IsDom k} ≃ {c // (Γ.layer ∅ V.L).IsCod c} :=
  Equiv.ofBijective (fun k => ⟨⟨V.edgeOf φ k.1, lowerEdge_of_cut (V.cut_L_edgeOf φ k.2)⟩,
      (Γ.layer_isCod_iff _).2 (V.cut_L_edgeOf φ k.2)⟩)
    ⟨fun k k' h => Subtype.ext (V.edgeOf_injective φ (congrArg (fun c => c.1.1) h)), by
      rintro ⟨⟨c, hc⟩, hc'⟩
      have hcut : Γ.Cut V.L c := (Γ.layer_isCod_iff ⟨c, hc⟩).1 hc'
      by_cases hA : A.edge c
      · refine ⟨⟨.inl (φ.eE.symm ⟨c, hA⟩), ?_⟩, ?_⟩
        · change Ω.src _ = none
          rw [sub_iso_src_eq_none_iff φ]
          simpa using V.not_node_src_of_cut_L hcut
        · apply Subtype.ext; apply Subtype.ext
          change (φ.eE (φ.eE.symm ⟨c, hA⟩)).1 = c
          rw [Equiv.apply_symm_apply]
      · exact ⟨⟨.inr ⟨c, hcut, V.cut_M_of_cut_L hcut hA, hA⟩, rfl⟩, rfl⟩⟩

/-- The bijection `cod(Ω^♯) → dom(Γ[M, Γ̇]) = cut(M)` given by `φ` and the identity on
`R` (`cut(M) = cod(Γ') ⊎ R`). -/
noncomputable def ValidLayer.codMatch :
    {k // (Ω.addLoose V.R).IsCod k} ≃ {c // (Γ.layer V.M Set.univ).IsDom c} :=
  Equiv.ofBijective (fun k => ⟨⟨V.edgeOf φ k.1, upperEdge_of_cut (V.cut_M_edgeOf φ k.2)⟩,
      (Γ.layer_isDom_iff _).2 (V.cut_M_edgeOf φ k.2)⟩)
    ⟨fun k k' h => Subtype.ext (V.edgeOf_injective φ (congrArg (fun c => c.1.1) h)), by
      rintro ⟨⟨c, hc⟩, hc'⟩
      have hcut : Γ.Cut V.M c := (Γ.layer_isDom_iff ⟨c, hc⟩).1 hc'
      by_cases hA : A.edge c
      · refine ⟨⟨.inl (φ.eE.symm ⟨c, hA⟩), ?_⟩, ?_⟩
        · change Ω.tgt _ = none
          rw [sub_iso_tgt_eq_none_iff φ]
          simpa using V.not_node_tgt_of_cut_M hcut
        · apply Subtype.ext; apply Subtype.ext
          change (φ.eE (φ.eE.symm ⟨c, hA⟩)).1 = c
          rw [Equiv.apply_symm_apply]
      · exact ⟨⟨.inr ⟨c, V.cut_L_of_cut_M hcut hA, hcut, hA⟩, rfl⟩, rfl⟩⟩

@[simp] theorem ValidLayer.domMatch_val (k : {k // (Ω.addLoose V.R).IsDom k}) :
    (V.domMatch φ k).1.1 = V.edgeOf φ k.1 := rfl

@[simp] theorem ValidLayer.codMatch_val (k : {k // (Ω.addLoose V.R).IsCod k}) :
    (V.codMatch φ k).1.1 = V.edgeOf φ k.1 := rfl

theorem ValidLayer.domMatch_symm_val (c : {c // (Γ.layer ∅ V.L).IsCod c}) :
    V.edgeOf φ ((V.domMatch φ).symm c).1 = c.1.1 := by
  rw [← ValidLayer.domMatch_val, Equiv.apply_symm_apply]

theorem ValidLayer.codMatch_symm_val (c : {c // (Γ.layer V.M Set.univ).IsDom c}) :
    V.edgeOf φ ((V.codMatch φ).symm c).1 = c.1.1 := by
  rw [← ValidLayer.codMatch_val, Equiv.apply_symm_apply]

variable {NΛ : Type u₅} {EΛ : Type u₆} {Λ : PGraph NΛ EΛ}

/-- The gluing bijection `cod(Γ[∅, L]) → dom(Λ^♯)`, given by `φ ∘ α` and the identity
on `R`. -/
noncomputable def ValidLayer.m₁ (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) :
    {c // (Γ.layer ∅ V.L).IsCod c} ≃ {k // (Λ.addLoose V.R).IsDom k} :=
  (V.domMatch φ).symm.trans (liftDom α V.R).symm

/-- The gluing bijection `cod(Λ^♯) → dom(Γ[M, Γ̇])`, given by `φ ∘ β` and the identity
on `R`. -/
noncomputable def ValidLayer.m₂ (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}) :
    {k // (Λ.addLoose V.R).IsCod k} ≃ {c // (Γ.layer V.M Set.univ).IsDom c} :=
  (liftCod β V.R).trans (V.codMatch φ)

end PGraph

/-! ### The surgery on anchored graphs -/

namespace AGraph

variable {N : Type u₁} {E : Type u₂} (Γ : AGraph N E) {A : Subgraph N E}
  {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PGraph NΩ EΩ} {NΛ : Type u₅} {EΛ : Type u₆}
  {Λ : PGraph NΛ EΛ}

/-- The surgery `Γ^Ω_Λ(φ, α, β)` computed with a layer `Γ[L, M]` as in Lemma 3.2,
anchored by `dom(Γ)` and `cod(Γ)` (through the induced bijections `α^♯`, `β^♯`). -/
noncomputable def surgeryAt (V : Γ.ValidLayer A) (φ : Ω.Iso (Γ.sub A.node A.edge))
    (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}) :
    AGraph (({x // Γ.LayerNode ∅ V.L x} ⊕ NΛ) ⊕ {x // Γ.LayerNode V.M Set.univ x})
      (({e // Γ.LayerEdge ∅ V.L e} ⊕ (Λ.addLoose V.R).InnerSrc) ⊕
        (Γ.layer V.M Set.univ).InnerSrc) :=
  PGraph.threeA (V.m₁ φ α) (V.m₂ φ β) (Γ.lowerDom V.L) (Γ.upperCod V.M)

/-- **The `(Ω / Λ, φ, α, β)`-surgery** `Γ^Ω_Λ(φ, α, β)` on an anchored graph `Γ`, for a
normal subgraph `Γ'` and an isomorphism `φ : Ω → Γ'` (Section 3), computed with
`Γ'^♯`. -/
noncomputable abbrev surgery (hA : Γ.IsNormal A) (φ : Ω.Iso (Γ.sub A.node A.edge))
    (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}) :=
  Γ.surgeryAt hA.sharpLayer φ α β

variable (V : Γ.ValidLayer A) (φ : Ω.Iso (Γ.sub A.node A.edge))
  (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e})

theorem surgeryAt_isDom_iff (e) :
    (Γ.surgeryAt V φ α β).IsDom e ↔ ∃ a : {e // Γ.IsDom e}, PGraph.rA ⟨a.1,
      PGraph.lowerEdge_of_isDom V.L a.2⟩ = e := by
  rw [show (Γ.surgeryAt V φ α β).IsDom e ↔ (PGraph.three (V.m₁ φ α) (V.m₂ φ β)).IsDom e from
    Iff.rfl, PGraph.three_isDom_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a.1, (Γ.layer_empty_isDom_iff V.L a).1 ha⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, (Γ.layer_empty_isDom_iff V.L _).2 a.2, rfl⟩

theorem surgeryAt_isCod_iff (e) :
    (Γ.surgeryAt V φ α β).IsCod e ↔ ∃ c : {e // Γ.IsCod e}, PGraph.rC (V.m₁ φ α) (V.m₂ φ β)
      ⟨c.1, PGraph.upperEdge_of_isCod V.M c.2⟩ = e := by
  rw [show (Γ.surgeryAt V φ α β).IsCod e ↔ (PGraph.three (V.m₁ φ α) (V.m₂ φ β)).IsCod e from
    Iff.rfl, PGraph.three_isCod_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c.1, (Γ.layer_univ_isCod_iff V.M c).1 hc⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, (Γ.layer_univ_isCod_iff V.M _).2 c.2, rfl⟩

/-- The induced bijection `α^♯ : dom(Γ^Ω_Λ) → dom(Γ)` ("Clearly there are induced
bijections"). -/
noncomputable def alphaSharp : {e // (Γ.surgeryAt V φ α β).IsDom e} ≃ {e // Γ.IsDom e} :=
  (Equiv.ofBijective (fun a : {e // Γ.IsDom e} =>
      (⟨PGraph.rA ⟨a.1, PGraph.lowerEdge_of_isDom V.L a.2⟩,
        (Γ.surgeryAt_isDom_iff V φ α β _).2 ⟨a, rfl⟩⟩ : {e // (Γ.surgeryAt V φ α β).IsDom e}))
    ⟨fun a b h => Subtype.ext (by
        have := PGraph.rA_injective (congrArg Subtype.val h)
        exact Subtype.mk.inj this),
      fun e => by
        obtain ⟨a, ha⟩ := (Γ.surgeryAt_isDom_iff V φ α β e.1).1 e.2
        exact ⟨a, Subtype.ext ha⟩⟩).symm

/-- The induced bijection `β^♯ : cod(Γ^Ω_Λ) → cod(Γ)`. -/
noncomputable def betaSharp : {e // (Γ.surgeryAt V φ α β).IsCod e} ≃ {e // Γ.IsCod e} :=
  (Equiv.ofBijective (fun c : {e // Γ.IsCod e} =>
      (⟨PGraph.rC (V.m₁ φ α) (V.m₂ φ β) ⟨c.1, PGraph.upperEdge_of_isCod V.M c.2⟩,
        (Γ.surgeryAt_isCod_iff V φ α β _).2 ⟨c, rfl⟩⟩ : {e // (Γ.surgeryAt V φ α β).IsCod e}))
    ⟨fun a b h => Subtype.ext (by
        have := PGraph.rC_injective (congrArg Subtype.val h)
        exact Subtype.mk.inj this),
      fun e => by
        obtain ⟨c, hc⟩ := (Γ.surgeryAt_isCod_iff V φ α β e.1).1 e.2
        exact ⟨c, Subtype.ext hc⟩⟩).symm

theorem alphaSharp_symm_val (a : {e // Γ.IsDom e}) :
    ((Γ.alphaSharp V φ α β).symm a).1 = PGraph.rA ⟨a.1, PGraph.lowerEdge_of_isDom V.L a.2⟩ := by
  rw [alphaSharp, Equiv.symm_symm]
  rfl

theorem betaSharp_symm_val (c : {e // Γ.IsCod e}) :
    ((Γ.betaSharp V φ α β).symm c).1 =
      PGraph.rC (V.m₁ φ α) (V.m₂ φ β) ⟨c.1, PGraph.upperEdge_of_isCod V.M c.2⟩ := by
  rw [betaSharp, Equiv.symm_symm]
  rfl

/-- "`Γ^Ω_Λ` is indeed naturally anchored": its domain is ordered as `dom(Γ)` through
`α^♯`. -/
theorem surgeryAt_dom :
    (Γ.surgeryAt V φ α β).dom = (Γ.domEnum.mapEquiv (Γ.alphaSharp V φ α β).symm).list := by
  change (Γ.lowerDom V.L).list.map PGraph.rA = _
  simp only [Enumeration.mapEquiv, List.map_map]
  unfold AGraph.lowerDom Enumeration.lift Enumeration.sub
  rw [List.map_pmap, List.map_pmap]
  apply List.pmap_congr_left
  intro e _ h₁ h₂
  simp only [Function.comp_apply, alphaSharp_symm_val]

/-- "... and its codomain as `cod(Γ)` through `β^♯`". -/
theorem surgeryAt_cod :
    (Γ.surgeryAt V φ α β).cod = (Γ.codEnum.mapEquiv (Γ.betaSharp V φ α β).symm).list := by
  change (Γ.upperCod V.M).list.map (PGraph.rC (V.m₁ φ α) (V.m₂ φ β)) = _
  simp only [Enumeration.mapEquiv, List.map_map]
  unfold AGraph.upperCod Enumeration.lift Enumeration.sub
  rw [List.map_pmap, List.map_pmap]
  apply List.pmap_congr_left
  intro e _ h₁ h₂
  simp only [Function.comp_apply, betaSharp_symm_val]

end AGraph

/-! ### The surgery on diagrams -/

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  (Γ : Diagram G N E)

/-- A subgraph `Γ'` containing all the edges at its nodes, with the restriction `v'` of
the valuation of `Γ`. -/
noncomputable abbrev subD (A : Subgraph N E) (h : Γ.EdgeAt A) :
    PDiagram G {x // A.node x} {e // A.edge e} :=
  ⟨Γ.sub A.node A.edge, Γ.val.restrict _ _
    (fun x hx e he => h x hx e (Or.inr ((Γ.mem_ins x e).1 he)))
    (fun x hx e he => h x hx e (Or.inl ((Γ.mem_outs x e).1 he)))⟩

/-- The layer `Γ[L, M]` with its induced valuation, not anchored. -/
noncomputable abbrev layerP {L M : Set N} (hL : Γ.IsLevel L) (hM : Γ.IsLevel M) :
    PDiagram G {x // Γ.LayerNode L M x} {e // Γ.LayerEdge L M e} :=
  ⟨Γ.layer L M, Γ.val.restrict _ _ (fun _ hx _ he => Γ.layerEdge_of_mem_ins hM hx he)
    (fun _ hx _ he => Γ.layerEdge_of_mem_outs hL hx he)⟩

@[simp] theorem subD_v₀ (A : Subgraph N E) (h : Γ.EdgeAt A) (e : {e // A.edge e}) :
    (Γ.subD A h).val.v₀ e = Γ.val.v₀ e.1 := rfl

@[simp] theorem layerP_v₀ {L M : Set N} (hL : Γ.IsLevel L) (hM : Γ.IsLevel M)
    (e : {e // Γ.LayerEdge L M e}) : (Γ.layerP hL hM).val.v₀ e = Γ.val.v₀ e.1 := rfl

variable {A : Subgraph N E} (V : Γ.ValidLayer A)
  {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PDiagram G NΩ EΩ} {NΛ : Type u₅} {EΛ : Type u₆}
  {Λ : PDiagram G NΛ EΛ}

/-- The labels of the edges in `R` (restriction of `v`). -/
def rLabel : V.R → S := fun r => Γ.val.v₀ r.1

variable (φ : Ω.Iso (Γ.subD A V.edgeAt))

theorem v₀_edgeOf (k : EΩ ⊕ V.R) :
    (Ω.addLoose (Γ.rLabel V)).val.v₀ k = Γ.val.v₀ (V.edgeOf φ.toPIso k) := by
  rcases k with d | r
  · exact (φ.v₀_map d).symm
  · rfl

variable (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e})
  (hα : ∀ e, Ω.val.v₀ (α e).1 = Λ.val.v₀ e.1) (hβ : ∀ e, Ω.val.v₀ (β e).1 = Λ.val.v₀ e.1)

include hα in
theorem v₀_liftDom {R : Type u₇} (r : R → S) (k : {k // (Λ.toPGraph.addLoose R).IsDom k}) :
    (Ω.addLoose r).val.v₀ (PGraph.liftDom α R k).1 = (Λ.addLoose r).val.v₀ k.1 := by
  rcases k with ⟨d | x, h⟩
  · exact hα ⟨d, h⟩
  · rfl

include hβ in
theorem v₀_liftCod {R : Type u₇} (r : R → S) (k : {k // (Λ.toPGraph.addLoose R).IsCod k}) :
    (Ω.addLoose r).val.v₀ (PGraph.liftCod β R k).1 = (Λ.addLoose r).val.v₀ k.1 := by
  rcases k with ⟨d | x, h⟩
  · exact hβ ⟨d, h⟩
  · rfl

include hα in
theorem m₁_v₀ (c : {c // (Γ.layer ∅ V.L).IsCod c}) :
    (Λ.addLoose (Γ.rLabel V)).val.v₀ (V.m₁ φ.toPIso α c).1 =
      (Γ.layerP Γ.isLevel_empty V.isLevel_L).val.v₀ c.1 := by
  rw [layerP_v₀, ← v₀_liftDom α hα, PGraph.ValidLayer.m₁, Equiv.trans_apply,
    Equiv.apply_symm_apply, v₀_edgeOf, PGraph.ValidLayer.domMatch_symm_val]

include hβ in
theorem m₂_v₀ (k : {k // (Λ.toPGraph.addLoose V.R).IsCod k}) :
    (Γ.layerP V.isLevel_M Γ.isLevel_univ).val.v₀ (V.m₂ φ.toPIso β k).1 =
      (Λ.addLoose (Γ.rLabel V)).val.v₀ k.1 := by
  rw [layerP_v₀, ← v₀_liftCod β hβ, PGraph.ValidLayer.m₂, Equiv.trans_apply,
    PGraph.ValidLayer.codMatch_val, v₀_edgeOf]

/-- The `((Ω, u) / (Λ, w), φ, α, β)`-surgery on the diagram `(Γ, v)`, computed with a
layer `Γ[L, M]` as in Lemma 3.2: the graph `Γ^Ω_Λ` with the fused valuation `v_w`. -/
noncomputable def surgeryAt : Diagram G
    (({x // Γ.LayerNode ∅ V.L x} ⊕ NΛ) ⊕ {x // Γ.LayerNode V.M Set.univ x})
    (({e // Γ.LayerEdge ∅ V.L e} ⊕ (Λ.toPGraph.addLoose V.R).InnerSrc) ⊕
      (Γ.layer V.M Set.univ).InnerSrc) :=
  Diagram.three (Γ.layerP Γ.isLevel_empty V.isLevel_L) (Λ.addLoose (Γ.rLabel V))
    (Γ.layerP V.isLevel_M Γ.isLevel_univ) (V.m₁ φ.toPIso α) (V.m₂ φ.toPIso β)
    (Γ.m₁_v₀ V φ α hα) (Γ.m₂_v₀ V φ β hβ) (Γ.toAGraph.lowerDom V.L) (Γ.toAGraph.upperCod V.M)

/-- **The `((Ω, u) / (Λ, w), φ, α, β)`-surgery** on `(Γ, v)` (Section 3): the transition
from `(Γ, v)` to `(Γ^Ω_Λ, v_w)`, computed with `Γ'^♯`. -/
noncomputable abbrev surgery (hA : Γ.IsNormal A) (φ : Ω.Iso (Γ.subD A hA.edge_at)) :=
  Γ.surgeryAt hA.sharpLayer φ α β hα hβ

theorem surgeryAt_toAGraph :
    (Γ.surgeryAt V φ α β hα hβ).toAGraph = Γ.toAGraph.surgeryAt V φ.toPIso α β := rfl

/-- "`v_w(e) = (v ∘ α^♯)(e)` for `e ∈ dom(Γ^Ω_Λ)`". -/
theorem surgeryAt_v₀_dom (e : {e // (Γ.surgeryAt V φ α β hα hβ).IsDom e}) :
    (Γ.surgeryAt V φ α β hα hβ).val.v₀ e.1 =
      Γ.val.v₀ (Γ.toAGraph.alphaSharp V φ.toPIso α β e).1 := by
  obtain ⟨a, rfl⟩ := (Γ.toAGraph.alphaSharp V φ.toPIso α β).symm.surjective e
  rw [Equiv.apply_symm_apply]
  change (Γ.surgeryAt V φ α β hα hβ).val.v₀ ((Γ.toAGraph.alphaSharp V φ.toPIso α β).symm a).1 = _
  rw [AGraph.alphaSharp_symm_val]
  rfl

/-- "... and similarly for `e ∈ cod(Γ^Ω_Λ)`". -/
theorem surgeryAt_v₀_cod (e : {e // (Γ.surgeryAt V φ α β hα hβ).IsCod e}) :
    (Γ.surgeryAt V φ α β hα hβ).val.v₀ e.1 =
      Γ.val.v₀ (Γ.toAGraph.betaSharp V φ.toPIso α β e).1 := by
  obtain ⟨c, rfl⟩ := (Γ.toAGraph.betaSharp V φ.toPIso α β).symm.surjective e
  rw [Equiv.apply_symm_apply]
  change (Γ.surgeryAt V φ α β hα hβ).val.v₀ ((Γ.toAGraph.betaSharp V φ.toPIso α β).symm c).1 = _
  rw [AGraph.betaSharp_symm_val]
  exact Valuation.three_v₀_rC _ _ _ (Γ.m₁_v₀ V φ α hα) (Γ.m₂_v₀ V φ β hβ) _

/-- "So `dom(Γ^Ω_Λ, v_w) = dom(Γ, v)`". -/
@[simp] theorem surgeryAt_domWord : (Γ.surgeryAt V φ α β hα hβ).domWord = Γ.domWord := by
  unfold domWord
  congr 1
  change ((Γ.toAGraph.lowerDom V.L).list.map PGraph.rA).map _ = _
  rw [List.map_map, ← Γ.toAGraph.lowerDom_map_val V.L, List.map_map]
  rfl

/-- "... and `cod(Γ^Ω_Λ, v_w) = cod(Γ, v)`". -/
@[simp] theorem surgeryAt_codWord : (Γ.surgeryAt V φ α β hα hβ).codWord = Γ.codWord := by
  unfold codWord
  congr 1
  change ((Γ.toAGraph.upperCod V.M).list.map (PGraph.rC _ _)).map _ = _
  rw [List.map_map, ← Γ.toAGraph.upperCod_map_val V.M, List.map_map]
  exact List.map_congr_left fun c _ =>
    Valuation.three_v₀_rC _ _ _ (Γ.m₁_v₀ V φ α hα) (Γ.m₂_v₀ V φ β hβ) c

end Diagram

end FreeMarkov
