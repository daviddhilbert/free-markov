/-
Free Markov categories, Stage 2: the structure of a surgery.

* `Diagram.isoMid`: replacing the middle piece of a three-piece gluing by an isomorphic
  one gives an isomorphic diagram.
* `Diagram.decompAt`, `Diagram.isoDecomp`: `Γ` is the three-piece gluing of `Γ[∅, L]`,
  `Ω^♯ = Ω ⊎ R` and `Γ[M, Γ̇]` along the bijections given by `φ` and the identity on `R`
  (the decomposition behind the "more precisely" paragraph of Section 3).
* `CanonProj`: the nodes, edges and incidences of the result of a surgery are
  determined by `Γ`, `Γ'`, `Λ`, `φ ∘ α`, `φ ∘ β` (proof of Lemma 3.3).  This is proved
  for every three-piece decomposition of `Γ` whose middle piece contains `Γ'`
  (`Diagram.canonProj`), and gives the independence of the choice of layer, the
  recognition of surgeries (the "if" half of Lemma 3.3), reversibility, and the
  invariance of surgeries under isomorphisms.
-/
module

public import FreeMarkov.Stage2.Surgery

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁

namespace FreeMarkov

open Relation

/-! ### Isomorphic middle pieces -/

namespace PDiagram.Iso

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄} {Λ : PDiagram G N E} {Ω : PDiagram G N' E'}

/-- An isomorphism `Λ → Ω` and the identity on `R` give an isomorphism
`Λ ⊎ R → Ω ⊎ R`. -/
def addLoose (ψ : Λ.Iso Ω) {R : Type u₅} (r : R → S) : (Λ.addLoose r).Iso (Ω.addLoose r) where
  eN := ψ.eN
  eE := Equiv.sumCongr ψ.eE (Equiv.refl R)
  ins_map x := by
    simp [PGraph.addLoose, ψ.ins_map, Function.comp_def]
  outs_map x := by
    simp [PGraph.addLoose, ψ.outs_map, Function.comp_def]
  v₀_map e := by
    rcases e with e | e
    · exact ψ.v₀_map e
    · rfl
  v₁_map x := ψ.v₁_map x

end PDiagram.Iso

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}
  {NA : Type u₁} {EA : Type u₂} {NK : Type u₃} {EK : Type u₄} {NK' : Type u₅} {EK' : Type u₆}
  {NC : Type u₇} {EC : Type u₈}
  {PA : PDiagram G NA EA} {K : PDiagram G NK EK} {K' : PDiagram G NK' EK'}
  {PC : PDiagram G NC EC}

section IsoMid

variable {m₁ : {e // PA.IsCod e} ≃ {e // K.IsDom e}} {m₂ : {e // K.IsCod e} ≃ {e // PC.IsDom e}}
  {h₁ : ∀ c, K.val.v₀ (m₁ c).1 = PA.val.v₀ c.1} {h₂ : ∀ c, PC.val.v₀ (m₂ c).1 = K.val.v₀ c.1}
  {m₁' : {e // PA.IsCod e} ≃ {e // K'.IsDom e}} {m₂' : {e // K'.IsCod e} ≃ {e // PC.IsDom e}}
  {h₁' : ∀ c, K'.val.v₀ (m₁' c).1 = PA.val.v₀ c.1}
  {h₂' : ∀ c, PC.val.v₀ (m₂' c).1 = K'.val.v₀ c.1}
  {dA : Enumeration PA.IsDom} {cC : Enumeration PC.IsCod}
  (κ : K.Iso K')
  (hm₁ : ∀ c, (m₁' c).1 = κ.eE (m₁ c).1)
  (hm₂ : ∀ (k : {e // K.IsCod e}) (k' : {e // K'.IsCod e}), k'.1 = κ.eE k.1 → m₂' k' = m₂ k)

/-- The map of edges underlying `isoMid`. -/
noncomputable def isoMidE (κ : K.Iso K') :
    (EA ⊕ K.InnerSrc) ⊕ PC.InnerSrc → (EA ⊕ K'.InnerSrc) ⊕ PC.InnerSrc :=
  Sum.map (Sum.map id κ.toPIso.innerSrcEquiv) id

include hm₁ in
theorem isoMidE_rK (k : EK) :
    isoMidE (PC := PC) κ (PGraph.rK m₁ k) = PGraph.rK m₁' (κ.eE k) := by
  by_cases hk : K.src k = none
  · have hk' : K'.src (κ.eE k) = none := by
      rw [κ.toPIso.src_map, hk]; rfl
    rw [PGraph.rK_of_src_eq_none hk, PGraph.rK_of_src_eq_none hk']
    have : m₁' (m₁.symm ⟨k, hk⟩) = ⟨κ.eE k, hk'⟩ := Subtype.ext (by rw [hm₁]; simp)
    rw [← this, Equiv.symm_apply_apply]
    rfl
  · have hk' : K'.src (κ.eE k) ≠ none := by
      rw [κ.toPIso.src_map]; simpa using hk
    rw [PGraph.rK_of_src_ne_none hk, PGraph.rK_of_src_ne_none hk']
    rfl

include hm₁ hm₂ in
theorem isoMidE_rC (c : EC) :
    isoMidE (PC := PC) κ (PGraph.rC m₁ m₂ c) = PGraph.rC m₁' m₂' c := by
  by_cases hc : PC.src c = none
  · rw [PGraph.rC_of_src_eq_none hc, PGraph.rC_of_src_eq_none hc, isoMidE_rK κ hm₁]
    congr 1
    set k := m₂.symm ⟨c, hc⟩
    have hk' : K'.tgt (κ.eE k.1) = none := by
      rw [κ.toPIso.tgt_map, k.2]; rfl
    have : m₂' ⟨κ.eE k.1, hk'⟩ = ⟨c, hc⟩ := by
      rw [hm₂ k ⟨κ.eE k.1, hk'⟩ rfl]
      simp [k]
    rw [← this, Equiv.symm_apply_apply]
  · rw [PGraph.rC_of_src_ne_none hc, PGraph.rC_of_src_ne_none hc]
    rfl

include hm₁ hm₂ in
/-- Replacing the middle piece of a three-piece gluing by an isomorphic one, compatibly
with the gluing bijections, gives an isomorphic diagram. -/
noncomputable def isoMid :
    (Diagram.three PA K PC m₁ m₂ h₁ h₂ dA cC).Iso (Diagram.three PA K' PC m₁' m₂' h₁' h₂' dA cC) :=
  Diagram.Iso.ofProj (Sum.map (Sum.map id κ.eN) id) (isoMidE κ) id id
    (Sum.map_injective.2 ⟨Sum.map_injective.2 ⟨Function.injective_id, κ.eN.injective⟩,
      Function.injective_id⟩) Function.injective_id
    (Sum.map_injective.2 ⟨Sum.map_injective.2 ⟨Function.injective_id,
      κ.toPIso.innerSrcEquiv.injective⟩, Function.injective_id⟩) Function.injective_id
    (fun t => ⟨fun ⟨n, h⟩ => ⟨_, h⟩, fun _ => (Sum.map_surjective.2
      ⟨Sum.map_surjective.2 ⟨Function.surjective_id, κ.eN.surjective⟩,
        Function.surjective_id⟩) t⟩)
    (fun t => ⟨fun ⟨n, h⟩ => ⟨_, h⟩, fun _ => (Sum.map_surjective.2
      ⟨Sum.map_surjective.2 ⟨Function.surjective_id, κ.toPIso.innerSrcEquiv.surjective⟩,
        Function.surjective_id⟩) t⟩)
    (by
      rintro ((x | y) | z) n' rfl
      · simp only [Sum.map_inl, id, three_ins_A, List.map_map]
        rfl
      · simp only [Sum.map_inl, Sum.map_inr, three_ins_K, List.map_map]
        rw [show K'.ins (κ.eN y) = (K.ins y).map κ.eE from κ.ins_map y, List.map_map]
        exact List.map_congr_left fun k _ => isoMidE_rK κ hm₁ k
      · simp only [Sum.map_inr, id, three_ins_C, List.map_map]
        exact List.map_congr_left fun c _ => isoMidE_rC κ hm₁ hm₂ c)
    (by
      rintro ((x | y) | z) n' rfl
      · simp only [Sum.map_inl, id, three_outs_A, List.map_map]
        rfl
      · simp only [Sum.map_inl, Sum.map_inr, three_outs_K, List.map_map]
        rw [show K'.outs (κ.eN y) = (K.outs y).map κ.eE from κ.outs_map y, List.map_map]
        exact List.map_congr_left fun k _ => isoMidE_rK κ hm₁ k
      · simp only [Sum.map_inr, id, three_outs_C, List.map_map]
        exact List.map_congr_left fun c _ => isoMidE_rC κ hm₁ hm₂ c)
    (by
      simp only [three_dom, List.map_map]
      rfl)
    (by
      simp only [three_cod, List.map_map]
      exact List.map_congr_left fun c _ => isoMidE_rC κ hm₁ hm₂ c)
    (by
      intro e e' he
      subst he
      rcases PGraph.three_edge_cases (m₁ := m₁) (m₂ := m₂) e with ⟨a, rfl⟩ | ⟨k, -, rfl⟩ |
        ⟨c, -, rfl⟩
      · rfl
      · simp only [isoMidE_rK κ hm₁, three_v₀_rK]
        exact (κ.v₀_map k).symm
      · simp only [isoMidE_rC κ hm₁ hm₂, three_v₀_rC])
    (by
      rintro ((x | y) | z) n' rfl
      · rfl
      · exact (κ.v₁_map y).symm
      · rfl)

end IsoMid

/-! ### The decomposition of `Γ` by a layer -/

section Decomp

variable {N : Type u₁} {E : Type u₂} (Γ : Diagram G N E) {A : Subgraph N E}
  (V : Γ.ValidLayer A) {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PDiagram G NΩ EΩ}
  (φ : Ω.Iso (Γ.subD A V.edgeAt))

theorem domMatch_v₀ (c : {c // (Γ.layer ∅ V.L).IsCod c}) :
    (Ω.addLoose (Γ.rLabel V)).val.v₀ ((V.domMatch φ.toPIso).symm c).1 =
      (Γ.layerP Γ.isLevel_empty V.isLevel_L).val.v₀ c.1 := by
  rw [v₀_edgeOf, PGraph.ValidLayer.domMatch_symm_val]
  rfl

theorem codMatch_v₀ (k : {k // (Ω.toPGraph.addLoose V.R).IsCod k}) :
    (Γ.layerP V.isLevel_M Γ.isLevel_univ).val.v₀ (V.codMatch φ.toPIso k).1 =
      (Ω.addLoose (Γ.rLabel V)).val.v₀ k.1 := by
  rw [v₀_edgeOf]
  rfl

/-- `Γ` as the three-piece gluing of `Γ[∅, L]`, `Ω^♯ = Ω ⊎ R` and `Γ[M, Γ̇]` along the
bijections given by `φ` and the identity on `R`. -/
noncomputable abbrev decompAt : Diagram G
    (({x // Γ.LayerNode ∅ V.L x} ⊕ NΩ) ⊕ {x // Γ.LayerNode V.M Set.univ x})
    (({e // Γ.LayerEdge ∅ V.L e} ⊕ (Ω.toPGraph.addLoose V.R).InnerSrc) ⊕
      (Γ.layer V.M Set.univ).InnerSrc) :=
  Diagram.three (Γ.layerP Γ.isLevel_empty V.isLevel_L) (Ω.addLoose (Γ.rLabel V))
    (Γ.layerP V.isLevel_M Γ.isLevel_univ) (V.domMatch φ.toPIso).symm (V.codMatch φ.toPIso)
    (Γ.domMatch_v₀ V φ) (Γ.codMatch_v₀ V φ) (Γ.toAGraph.lowerDom V.L) (Γ.toAGraph.upperCod V.M)

/-- The nodes of the decomposition, as nodes of `Γ`. -/
def decompN : (({x // Γ.LayerNode ∅ V.L x} ⊕ NΩ) ⊕ {x // Γ.LayerNode V.M Set.univ x}) → N
  | .inl (.inl x) => x.1
  | .inl (.inr z) => (φ.eN z).1
  | .inr x => x.1

/-- The edges of the decomposition, as edges of `Γ`. -/
def decompE : (({e // Γ.LayerEdge ∅ V.L e} ⊕ (Ω.toPGraph.addLoose V.R).InnerSrc) ⊕
    (Γ.layer V.M Set.univ).InnerSrc) → E
  | .inl (.inl a) => a.1
  | .inl (.inr b) => V.edgeOf φ.toPIso b.1
  | .inr c => c.1.1

theorem decompE_rK (k : EΩ ⊕ V.R) :
    Γ.decompE V φ (PGraph.rK (C := (Γ.layer V.M Set.univ)) (V.domMatch φ.toPIso).symm k) =
      V.edgeOf φ.toPIso k := by
  by_cases hk : (Ω.toPGraph.addLoose V.R).src k = none
  · rw [PGraph.rK_of_src_eq_none hk]
    change ((V.domMatch φ.toPIso).symm.symm ⟨k, hk⟩).1.1 = _
    rw [Equiv.symm_symm]
    rfl
  · rw [PGraph.rK_of_src_ne_none hk]
    rfl

theorem decompE_rC (c : {e // Γ.LayerEdge V.M Set.univ e}) :
    Γ.decompE V φ (PGraph.rC (V.domMatch φ.toPIso).symm (V.codMatch φ.toPIso) c) = c.1 := by
  by_cases hc : (Γ.layer V.M Set.univ).src c = none
  · rw [PGraph.rC_of_src_eq_none hc, decompE_rK, PGraph.ValidLayer.codMatch_symm_val]
  · rw [PGraph.rC_of_src_ne_none hc]
    rfl

theorem layer_src_ne_none_iff {L M : Set N} (e : {e // Γ.LayerEdge L M e}) :
    (Γ.layer L M).src e ≠ none ↔ ∃ x, Γ.src e.1 = some x ∧ Γ.LayerNode L M x := by
  rw [Ne, PGraph.layer, PGraph.sub_src_eq_none_iff]
  simp only [not_forall, not_not, exists_prop]

theorem innerSrc_cases (b : (Ω.toPGraph.addLoose V.R).InnerSrc) :
    ∃ d z, b.1 = .inl d ∧ Ω.src d = some z := by
  obtain ⟨d | r, hb⟩ := b
  · obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hb
    exact ⟨d, z, rfl, hz⟩
  · exact (hb rfl).elim

theorem decompN_injective : Function.Injective (Γ.decompN V φ) := by
  rintro ((x | z) | x) ((y | z') | y) h <;> simp only [decompN] at h
  · exact congrArg _ (congrArg _ (Subtype.ext h))
  · exact (((V.node_iff _).1 (h ▸ (φ.eN z').2)).2 x.2.1).elim
  · exact (y.2.2 (V.subset (h ▸ x.2.1))).elim
  · exact (((V.node_iff _).1 (h ▸ (φ.eN z).2)).2 (h ▸ y.2.1)).elim
  · exact congrArg _ (congrArg _ (φ.eN.injective (Subtype.ext h)))
  · exact (y.2.2 (h ▸ ((V.node_iff _).1 (φ.eN z).2).1)).elim
  · exact (x.2.2 (V.subset (h ▸ y.2.1))).elim
  · exact (x.2.2 (h ▸ ((V.node_iff _).1 (φ.eN z').2).1)).elim
  · exact congrArg _ (Subtype.ext h)

theorem decompE_injective : Function.Injective (Γ.decompE V φ) := by
  have hb : ∀ b : (Ω.toPGraph.addLoose V.R).InnerSrc, ∃ x, Γ.src (V.edgeOf φ.toPIso b.1) = some x ∧
      A.node x := by
    intro b
    obtain ⟨d, z, hd, hz⟩ := Γ.innerSrc_cases V b
    rw [hd]
    exact ⟨_, PGraph.sub_iso_src_eq_some φ.toPIso hz, (φ.eN z).2⟩
  have hc : ∀ c : (Γ.layer V.M Set.univ).InnerSrc, ∃ x, Γ.src c.1.1 = some x ∧ x ∉ V.M := by
    intro c
    obtain ⟨x, hx, -, hxM⟩ := (Γ.layer_src_ne_none_iff c.1).1 c.2
    exact ⟨x, hx, hxM⟩
  rintro ((a | b) | c) ((a' | b') | c') h <;> simp only [decompE] at h
  · exact congrArg _ (congrArg _ (Subtype.ext h))
  · obtain ⟨x, hx, hxA⟩ := hb b'
    rw [← h] at hx
    exact (((V.node_iff x).1 hxA).2 (a.2.1 x hx)).elim
  · obtain ⟨x, hx, hxM⟩ := hc c'
    rw [← h] at hx
    exact (hxM (V.subset (a.2.1 x hx))).elim
  · obtain ⟨x, hx, hxA⟩ := hb b
    rw [h] at hx
    exact (((V.node_iff x).1 hxA).2 (a'.2.1 x hx)).elim
  · exact congrArg _ (congrArg _ (Subtype.ext (V.edgeOf_injective φ.toPIso h)))
  · obtain ⟨x, hx, hxA⟩ := hb b
    obtain ⟨x', hx', hxM⟩ := hc c'
    rw [h, hx'] at hx
    injection hx with hx
    subst hx
    exact (hxM ((V.node_iff _).1 hxA).1).elim
  · obtain ⟨x, hx, hxM⟩ := hc c
    rw [h] at hx
    exact (hxM (V.subset (a'.2.1 x hx))).elim
  · obtain ⟨x, hx, hxA⟩ := hb b'
    obtain ⟨x', hx', hxM⟩ := hc c
    rw [← h, hx'] at hx
    injection hx with hx
    subst hx
    exact (hxM ((V.node_iff _).1 hxA).1).elim
  · exact congrArg _ (Subtype.ext (Subtype.ext h))

theorem decompE_surjective (f : E) : ∃ e, Γ.decompE V φ e = f := by
  by_cases hs : Γ.SrcIn V.L f
  · exact ⟨.inl (.inl ⟨f, hs, fun _ _ => Set.notMem_empty _⟩), rfl⟩
  · unfold PGraph.SrcIn at hs
    simp only [not_forall] at hs
    obtain ⟨x, hx, hxL⟩ := hs
    by_cases hA : A.node x
    · have hAf : A.edge f := V.edgeAt x hA f (Or.inl hx)
      have hd : (Ω.toPGraph.addLoose V.R).src (.inl (φ.eE.symm ⟨f, hAf⟩)) ≠ none := by
        change Ω.src _ ≠ none
        rw [Ne, PGraph.sub_iso_src_eq_none_iff φ.toPIso]
        intro h
        exact h x (by simpa using hx) hA
      refine ⟨.inl (.inr ⟨_, hd⟩), ?_⟩
      change (φ.eE (φ.eE.symm ⟨f, hAf⟩)).1 = f
      rw [Equiv.apply_symm_apply]
    · have hxM : x ∉ V.M := fun hxM => hA ((V.node_iff x).2 ⟨hxM, hxL⟩)
      have hf : Γ.LayerEdge V.M Set.univ f :=
        ⟨fun _ _ => Set.mem_univ _, fun y hy hyM => hxM (V.isLevel_M x y (Γ.lt_of_edge hx hy) hyM)⟩
      exact ⟨.inr ⟨⟨f, hf⟩, (Γ.layer_src_ne_none_iff _).2 ⟨x, hx, Set.mem_univ x, hxM⟩⟩, rfl⟩

theorem decompN_surjective (t : N) : ∃ n, Γ.decompN V φ n = t := by
  by_cases hL : t ∈ V.L
  · exact ⟨.inl (.inl ⟨t, hL, Set.notMem_empty t⟩), rfl⟩
  · by_cases hA : A.node t
    · exact ⟨.inl (.inr (φ.eN.symm ⟨t, hA⟩)), by simp [decompN]⟩
    · exact ⟨.inr ⟨t, Set.mem_univ t, fun hM => hA ((V.node_iff t).2 ⟨hM, hL⟩)⟩, rfl⟩

theorem decomp_ins (n) : ((Γ.decompAt V φ).ins n).map (Γ.decompE V φ) = Γ.ins (Γ.decompN V φ n) := by
  rcases n with (x | z) | x
  · rw [three_ins_A, List.map_map]
    exact PGraph.sub_ins_map_val x fun _ he => Γ.layerEdge_of_mem_ins V.isLevel_L x.2 he
  · rw [three_ins_K, List.map_map]
    change (((Ω.ins z).map Sum.inl).map _) = _
    rw [List.map_map]
    rw [show Γ.decompN V φ (.inl (.inr z)) = (φ.eN z).1 from rfl,
      ← PGraph.sub_ins_map_val (φ.eN z) fun e he =>
        V.edgeAt _ (φ.eN z).2 e (Or.inr ((Γ.mem_ins _ e).1 he))]
    rw [show (Γ.sub A.node A.edge).ins (φ.eN z) = (Ω.ins z).map φ.eE from φ.ins_map z,
      List.map_map]
    exact List.map_congr_left fun d _ => Γ.decompE_rK V φ (.inl d)
  · rw [three_ins_C, List.map_map]
    change _ = Γ.ins x.1
    rw [← PGraph.sub_ins_map_val (P := Γ.LayerNode V.M Set.univ) (Q := Γ.LayerEdge V.M Set.univ) x
      fun _ he => Γ.layerEdge_of_mem_ins Γ.isLevel_univ x.2 he]
    exact List.map_congr_left fun c _ => Γ.decompE_rC V φ c

theorem decomp_outs (n) :
    ((Γ.decompAt V φ).outs n).map (Γ.decompE V φ) = Γ.outs (Γ.decompN V φ n) := by
  rcases n with (x | z) | x
  · rw [three_outs_A, List.map_map]
    exact PGraph.sub_outs_map_val x fun _ he => Γ.layerEdge_of_mem_outs Γ.isLevel_empty x.2 he
  · rw [three_outs_K, List.map_map]
    change (((Ω.outs z).map Sum.inl).map _) = _
    rw [List.map_map]
    rw [show Γ.decompN V φ (.inl (.inr z)) = (φ.eN z).1 from rfl,
      ← PGraph.sub_outs_map_val (φ.eN z) fun e he =>
        V.edgeAt _ (φ.eN z).2 e (Or.inl ((Γ.mem_outs _ e).1 he))]
    rw [show (Γ.sub A.node A.edge).outs (φ.eN z) = (Ω.outs z).map φ.eE from φ.outs_map z,
      List.map_map]
    exact List.map_congr_left fun d _ => Γ.decompE_rK V φ (.inl d)
  · rw [three_outs_C, List.map_map]
    change _ = Γ.outs x.1
    rw [← PGraph.sub_outs_map_val (P := Γ.LayerNode V.M Set.univ)
      (Q := Γ.LayerEdge V.M Set.univ) x fun _ he => Γ.layerEdge_of_mem_outs V.isLevel_M x.2 he]
    exact List.map_congr_left fun c _ => Γ.decompE_rC V φ c

theorem decomp_v₀ (e) : (Γ.decompAt V φ).val.v₀ e = Γ.val.v₀ (Γ.decompE V φ e) := by
  rcases PGraph.three_edge_cases (m₁ := (V.domMatch φ.toPIso).symm) (m₂ := V.codMatch φ.toPIso)
    e with ⟨a, rfl⟩ | ⟨k, -, rfl⟩ | ⟨c, -, rfl⟩
  · rfl
  · rw [three_v₀_rK, decompE_rK, v₀_edgeOf]
  · rw [three_v₀_rC, decompE_rC]
    rfl

theorem decomp_v₁ (n) : (Γ.decompAt V φ).val.v₁ n = Γ.val.v₁ (Γ.decompN V φ n) := by
  rcases n with (x | z) | x
  · rfl
  · exact (φ.v₁_map z).symm
  · rfl

/-- **The decomposition of `Γ` by a layer**: `Γ` is isomorphic to the three-piece gluing
of `Γ[∅, L]`, `Ω ⊎ R`, `Γ[M, Γ̇]`, by an isomorphism that is `φ` on `Ω`. -/
noncomputable def isoDecomp : (Γ.decompAt V φ).Iso Γ :=
  Diagram.Iso.ofProj (Γ.decompN V φ) (Γ.decompE V φ) id id
    (Γ.decompN_injective V φ) Function.injective_id (Γ.decompE_injective V φ) Function.injective_id
    (fun t => ⟨fun ⟨n, h⟩ => ⟨_, h⟩, fun _ => Γ.decompN_surjective V φ t⟩)
    (fun t => ⟨fun ⟨n, h⟩ => ⟨_, h⟩, fun _ => Γ.decompE_surjective V φ t⟩)
    (by rintro n n' rfl; rw [decomp_ins, List.map_id])
    (by rintro n n' rfl; rw [decomp_outs, List.map_id])
    (by
      rw [List.map_id, three_dom, List.map_map]
      exact Γ.toAGraph.lowerDom_map_val V.L)
    (by
      rw [List.map_id, three_cod, List.map_map,
        ← Γ.toAGraph.upperCod_map_val V.M]
      exact List.map_congr_left fun c _ => Γ.decompE_rC V φ c)
    (by rintro e e' rfl; exact Γ.decomp_v₀ V φ e)
    (by rintro n n' rfl; exact Γ.decomp_v₁ V φ n)

theorem isoDecomp_eN (n) : (Γ.isoDecomp V φ).eN n = Γ.decompN V φ n :=
  equivOfProj_spec (Γ.decompN V φ) id (Γ.decompN_injective V φ) Function.injective_id _ n

theorem isoDecomp_eE (e) : (Γ.isoDecomp V φ).eE e = Γ.decompE V φ e :=
  equivOfProj_spec (Γ.decompE V φ) id (Γ.decompE_injective V φ) Function.injective_id _ e

end Decomp

end Diagram

/-! ### The canonical description of the result of a surgery -/

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

section Canon

variable {NX : Type u₁} {EX : Type u₂} (X : Diagram G NX EX)
  {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PDiagram G NΩ EΩ} {NΛ : Type u₅} {EΛ : Type u₆}
  {Λ : PDiagram G NΛ EΛ} (ιN : NΩ → NX) (ιE : EΩ → EX)
  (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e})

/-- An edge of `Λ` in the result of a surgery: itself if its source is an inner node,
otherwise the edge of `Γ` that it is glued to through `φ ∘ α`. -/
noncomputable def canonG (d : EΛ) : EX ⊕ Λ.InnerSrc :=
  if h : Λ.src d = none then .inl (ιE (α ⟨d, h⟩).1) else .inr ⟨d, h⟩

/-- An edge of `Γ` whose target is not in `Γ'`, in the result of a surgery: an edge of
`cod(Γ')` is replaced by the edge of `Λ` that corresponds to it through `φ ∘ β`; the
other edges are kept. -/
noncomputable def canonF (f : EX) : EX ⊕ Λ.InnerSrc := by
  classical
  exact if h : ∃ d : {d // Ω.IsCod d}, ιE d.1 = f then canonG ιE α (β.symm h.choose).1
    else .inl f

/-- The ordered inputs of the nodes of the result of a surgery. -/
noncomputable def canonIns : NX ⊕ NΛ → List (EX ⊕ Λ.InnerSrc)
  | .inl x => (X.ins x).map (canonF ιE α β)
  | .inr z => (Λ.ins z).map (canonG ιE α)

/-- The ordered outputs of the nodes of the result of a surgery. -/
noncomputable def canonOuts : NX ⊕ NΛ → List (EX ⊕ Λ.InnerSrc)
  | .inl x => (X.outs x).map .inl
  | .inr z => (Λ.outs z).map (canonG ιE α)

variable (Λ) in
/-- The labels of the edges of the result of a surgery. -/
def canonV₀ : EX ⊕ Λ.InnerSrc → S := Sum.elim X.val.v₀ fun d => Λ.val.v₀ d.1

variable (Λ) in
/-- The labels of the nodes of the result of a surgery. -/
def canonV₁ : NX ⊕ NΛ → G.A := Sum.elim X.val.v₁ Λ.val.v₁

/-- The nodes of the result of a surgery: the nodes of `Γ` outside `Γ'` and the nodes
of `Λ`. -/
def CanonNode (t : NX ⊕ NΛ) : Prop := Sum.elim (fun x => ∀ z, ιN z ≠ x) (fun _ => True) t

/-- The edges of the result of a surgery: the edges of `Γ` whose source is not in `Γ'`
and the edges of `Λ` with an inner source. -/
def CanonEdge (Ω : PGraph NΩ EΩ) (t : EX ⊕ Λ.InnerSrc) : Prop :=
  Sum.elim (fun f => ∀ d, Ω.src d ≠ none → ιE d ≠ f) (fun _ => True) t

theorem canonG_of_src_eq_none {d : EΛ} (h : Λ.src d = none) :
    canonG ιE α d = .inl (ιE (α ⟨d, h⟩).1) := by
  rw [canonG, dite_eq_left h]

theorem canonG_of_src_ne_none {d : EΛ} (h : Λ.src d ≠ none) : canonG ιE α d = .inr ⟨d, h⟩ := by
  rw [canonG, dite_eq_right h]

theorem canonF_of_cod (hι : Function.Injective ιE) (d : {d // Ω.IsCod d}) :
    canonF ιE α β (ιE d.1) = canonG ιE α (β.symm d).1 := by
  have h : ∃ d' : {d // Ω.IsCod d}, ιE d'.1 = ιE d.1 := ⟨d, rfl⟩
  have hd : h.choose = d := Subtype.ext (hι h.choose_spec)
  rw [canonF, dite_eq_left h, hd]

theorem canonF_of_not {f : EX} (h : ∀ d : {d // Ω.IsCod d}, ιE d.1 ≠ f) :
    canonF ιE α β f = .inl f := by
  rw [canonF, dite_eq_right]
  exact fun ⟨d, hd⟩ => h d hd

variable (Ω) in
/-- **The canonical description of the result of a surgery** (proof of Lemma 3.3: "the
nodes of `Γ^Ω_Λ`, its edges, and their incidences are determined by `Γ`, `Γ'`, `Λ`,
`φ ∘ α`, and `φ ∘ β`"): maps of the nodes and edges of `Y` onto the nodes of `X`
outside `ιN(Ω)` together with the nodes of `Λ`, and onto the edges of `X` not starting in
`ιN(Ω)` together with the edges of `Λ` with an inner source, under which the inputs,
outputs, domain, codomain and labels of `Y` are given by `canonIns`, `canonOuts`, …. -/
structure CanonProj {NY : Type u₇} {EY : Type u₈} (Y : Diagram G NY EY) where
  /-- The map of nodes. -/
  pN : NY → NX ⊕ NΛ
  /-- The map of edges. -/
  pE : EY → EX ⊕ Λ.InnerSrc
  pN_inj : Function.Injective pN
  pE_inj : Function.Injective pE
  pN_range : ∀ t, (∃ n, pN n = t) ↔ CanonNode ιN t
  pE_range : ∀ t, (∃ e, pE e = t) ↔ CanonEdge ιE Ω.toPGraph t
  ins : ∀ n, (Y.ins n).map pE = canonIns X ιE α β (pN n)
  outs : ∀ n, (Y.outs n).map pE = canonOuts X ιE α (pN n)
  dom : Y.dom.map pE = X.dom.map .inl
  cod : Y.cod.map pE = X.cod.map (canonF ιE α β)
  v₀ : ∀ e, Y.val.v₀ e = canonV₀ X Λ (pE e)
  v₁ : ∀ n, Y.val.v₁ n = canonV₁ X Λ (pN n)

variable {X ιN ιE α β}

/-- Two diagrams with the same canonical description are isomorphic. -/
noncomputable def CanonProj.iso {NY : Type u₇} {EY : Type u₈} {NY' : Type u₉} {EY' : Type u₁₀}
    {Y : Diagram G NY EY} {Y' : Diagram G NY' EY'} (P : CanonProj X Ω ιN ιE α β Y)
    (P' : CanonProj X Ω ιN ιE α β Y') : Y.Iso Y' :=
  Diagram.Iso.ofProj P.pN P.pE P'.pN P'.pE P.pN_inj P'.pN_inj P.pE_inj P'.pE_inj
    (fun t => (P.pN_range t).trans (P'.pN_range t).symm)
    (fun t => (P.pE_range t).trans (P'.pE_range t).symm)
    (fun n n' h => by rw [P.ins, P'.ins, h]) (fun n n' h => by rw [P.outs, P'.outs, h])
    (by rw [P.dom, P'.dom]) (by rw [P.cod, P'.cod])
    (fun e e' h => by rw [P.v₀, P'.v₀, h]) (fun n n' h => by rw [P.v₁, P'.v₁, h])

end Canon

section MCT

variable {NX : Type u₁} {EX : Type u₂} {X : Diagram G NX EX}
  {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PDiagram G NΩ EΩ} {NΛ : Type u₅} {EΛ : Type u₆}
  {Λ : PDiagram G NΛ EΛ} {NA : Type u₇} {EA : Type u₈} {NC : Type u₉} {EC : Type u₁₀}
  {PA : PDiagram G NA EA} {PC : PDiagram G NC EC} {R : Type u₁₁} (r : R → S)
  (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e})
  (hα : ∀ e, Ω.val.v₀ (α e).1 = Λ.val.v₀ e.1) (hβ : ∀ e, Ω.val.v₀ (β e).1 = Λ.val.v₀ e.1)
  {mΩ₁ : {e // PA.IsCod e} ≃ {e // (Ω.toPGraph.addLoose R).IsDom e}}
  {mΩ₂ : {e // (Ω.toPGraph.addLoose R).IsCod e} ≃ {e // PC.IsDom e}}
  (hΩ₁ : ∀ c, (Ω.addLoose r).val.v₀ (mΩ₁ c).1 = PA.val.v₀ c.1)
  (hΩ₂ : ∀ c, PC.val.v₀ (mΩ₂ c).1 = (Ω.addLoose r).val.v₀ c.1)
  (dA : Enumeration PA.IsDom) (cC : Enumeration PC.IsCod)

include hα hΩ₁ in
theorem swap_h₁ (c : {e // PA.IsCod e}) :
    (Λ.addLoose r).val.v₀ ((mΩ₁.trans (PGraph.liftDom α R).symm) c).1 = PA.val.v₀ c.1 := by
  rw [← v₀_liftDom α hα r, Equiv.trans_apply, Equiv.apply_symm_apply, hΩ₁]

include hβ hΩ₂ in
theorem swap_h₂ (k : {e // (Λ.toPGraph.addLoose R).IsCod e}) :
    PC.val.v₀ (((PGraph.liftCod β R).trans mΩ₂) k).1 = (Λ.addLoose r).val.v₀ k.1 := by
  rw [Equiv.trans_apply, hΩ₂, v₀_liftCod β hβ r]

/-- The three-piece gluing with `Ω ⊎ R` replaced by `Λ ⊎ R`, along the bijections
composed with `α⁻¹` and `β`: the result of the surgery when the three pieces come from a
layer of `Γ` (`surgeryAt`), and the general form of the diagram `h ∘ [Λ^♯] ∘ g` of
Lemma 3.3. -/
noncomputable abbrev threeSwap : Diagram G ((NA ⊕ NΛ) ⊕ NC)
    ((EA ⊕ (Λ.toPGraph.addLoose R).InnerSrc) ⊕ PC.InnerSrc) :=
  Diagram.three PA (Λ.addLoose r) PC (mΩ₁.trans (PGraph.liftDom α R).symm)
    ((PGraph.liftCod β R).trans mΩ₂) (swap_h₁ r α hα hΩ₁) (swap_h₂ r β hβ hΩ₂) dA cC

variable {r hΩ₁ hΩ₂ dA cC} (θ : (Diagram.three PA (Ω.addLoose r) PC mΩ₁ mΩ₂ hΩ₁ hΩ₂ dA cC).Iso X)
  {ιN : NΩ → NX} {ιE : EΩ → EX}

/-- The map of nodes of `threeSwap` in the canonical description. -/
noncomputable def swapN : ((NA ⊕ NΛ) ⊕ NC) → NX ⊕ NΛ
  | .inl (.inl a) => .inl (θ.eN (.inl (.inl a)))
  | .inl (.inr z) => .inr z
  | .inr c => .inl (θ.eN (.inr c))

variable (ιE) in
/-- The map of the edges of `Λ ⊎ R`. -/
noncomputable def swapK : EΛ ⊕ R → EX ⊕ Λ.InnerSrc
  | .inl d => canonG ιE α d
  | .inr ρ => .inl (θ.eE (PGraph.rK (C := PC.toPGraph) mΩ₁ (.inr ρ)))

variable (ιE) in
/-- The map of edges of `threeSwap` in the canonical description. -/
noncomputable def swapE : ((EA ⊕ (Λ.toPGraph.addLoose R).InnerSrc) ⊕ PC.InnerSrc) →
    EX ⊕ Λ.InnerSrc
  | .inl (.inl a) => .inl (θ.eE (PGraph.rA a))
  | .inl (.inr b) => swapK α θ ιE b.1
  | .inr c => .inl (θ.eE (PGraph.rC mΩ₁ mΩ₂ c.1))

variable (hιN : ∀ z, θ.eN (.inl (.inr z)) = ιN z)
  (hιE : ∀ d, θ.eE (PGraph.rK mΩ₁ (.inl d)) = ιE d)

include hιE in
theorem ιE_injective : Function.Injective ιE := by
  intro d d' h
  rw [← hιE, ← hιE] at h
  exact Sum.inl_injective (PGraph.rK_injective (θ.eE.injective h))

include hιE in
theorem swapE_rK (k : EΛ ⊕ R) :
    swapE α θ ιE (PGraph.rK (C := PC.toPGraph) (mΩ₁.trans (PGraph.liftDom α R).symm) k) =
      swapK α θ ιE k := by
  by_cases hk : (Λ.toPGraph.addLoose R).src k = none
  · rw [PGraph.rK_of_src_eq_none hk]
    change Sum.inl (θ.eE (PGraph.rA _)) = _
    rw [Equiv.symm_trans_apply, Equiv.symm_symm]
    rcases k with d | ρ
    · change _ = canonG ιE α d
      rw [canonG_of_src_eq_none ιE α hk, ← hιE]
      have h' : (Ω.toPGraph.addLoose R).src (.inl (α ⟨d, hk⟩).1) = none := (α ⟨d, hk⟩).2
      rw [PGraph.rK_of_src_eq_none h']
      rfl
    · rfl
  · rw [PGraph.rK_of_src_ne_none hk]
    rfl

include hιE in
theorem swapK_eq_canonF (k : {e // (Λ.toPGraph.addLoose R).IsCod e}) :
    swapK α θ ιE k.1 =
      canonF ιE α β (θ.eE (PGraph.rK (C := PC.toPGraph) mΩ₁ (PGraph.liftCod β R k).1)) := by
  rcases k with ⟨d | ρ, hk⟩
  · rw [PGraph.liftCod_inl, hιE, canonF_of_cod ιE α β (ιE_injective θ hιE) (β ⟨d, hk⟩),
      Equiv.symm_apply_apply]
    rfl
  · rw [PGraph.liftCod_inr, canonF_of_not]
    · rfl
    · intro d hd
      rw [← hιE] at hd
      exact Sum.inl_ne_inr (PGraph.rK_injective (θ.eE.injective hd))

include hιE in
theorem swapE_rC (c : EC) :
    swapE α θ ιE (PGraph.rC (mΩ₁.trans (PGraph.liftDom α R).symm)
      ((PGraph.liftCod β R).trans mΩ₂) c) = canonF ιE α β (θ.eE (PGraph.rC mΩ₁ mΩ₂ c)) := by
  by_cases hc : PC.src c = none
  · rw [PGraph.rC_of_src_eq_none hc, PGraph.rC_of_src_eq_none hc, swapE_rK α θ hιE,
      swapK_eq_canonF α β θ hιE]
    congr 4
    rw [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  · rw [PGraph.rC_of_src_ne_none hc, canonF_of_not]
    · rfl
    · intro d hd
      rw [← hιE] at hd
      exact PGraph.rK_ne_rC_of_src_ne_none hc (θ.eE.injective hd)

include hιE in
theorem canonF_rA {a : EA} (ha : PA.tgt a ≠ none) :
    canonF ιE α β (θ.eE (PGraph.rA a)) = .inl (θ.eE (PGraph.rA a)) := by
  refine canonF_of_not ιE α β fun d hd => ?_
  rw [← hιE] at hd
  obtain ⟨hk, rfl⟩ := PGraph.eq_of_rA_eq_rK (θ.eE.injective hd).symm
  exact ha (mΩ₁.symm _).2

theorem swapE_inner (b : (Λ.toPGraph.addLoose R).InnerSrc) :
    ∃ d, ∃ h : Λ.src d ≠ none, b.1 = .inl d ∧ swapE α θ ιE (.inl (.inr b)) = .inr ⟨d, h⟩ := by
  obtain ⟨d | ρ, hb⟩ := b
  · exact ⟨d, hb, rfl, canonG_of_src_ne_none ιE α hb⟩
  · exact (hb rfl).elim

include hιN hιE in
/-- **The canonical description of `threeSwap`**: for a three-piece decomposition `θ` of
`X` whose middle piece is `Ω ⊎ R`, the diagram obtained by replacing `Ω` with `Λ` is
described by `X`, the image `ιN`, `ιE` of `Ω`, `Λ`, `α` and `β` alone. -/
noncomputable def canonProj :
    CanonProj X Ω ιN ιE α β (threeSwap r α β hα hβ hΩ₁ hΩ₂ dA cC) where
  pN := swapN θ
  pE := swapE α θ ιE
  pN_inj := by
    rintro ((a | z) | c) ((a' | z') | c') h <;>
      simp only [swapN, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        EmbeddingLike.apply_eq_iff_eq] at h <;> subst h <;> rfl
  pE_inj := by
    have key : ∀ (b : (Λ.toPGraph.addLoose R).InnerSrc) (f : EX),
        swapE α θ ιE (.inl (.inr b)) ≠ .inl f := by
      intro b f h
      obtain ⟨d, hd, -, h'⟩ := swapE_inner α θ b
      rw [h'] at h
      cases h
    rintro ((a | b) | c) ((a' | b') | c') h
    · simp only [swapE, Sum.inl.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      rw [PGraph.rA_injective h]
    · exact (key b' _ h.symm).elim
    · simp only [swapE, Sum.inl.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact (PGraph.rA_ne_rC_of_src_ne_none c'.2 h).elim
    · exact (key b _ h).elim
    · obtain ⟨d, hd, hb, h₁⟩ := swapE_inner α θ b
      obtain ⟨d', hd', hb', h₂⟩ := swapE_inner α θ b'
      rw [h₁, h₂] at h
      simp only [Sum.inr.injEq, Subtype.mk.injEq] at h
      subst h
      exact congrArg _ (congrArg _ (Subtype.ext (hb.trans hb'.symm)))
    · exact (key b _ h).elim
    · simp only [swapE, Sum.inl.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact (PGraph.rA_ne_rC_of_src_ne_none c.2 h.symm).elim
    · exact (key b' _ h.symm).elim
    · simp only [swapE, Sum.inl.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact congrArg _ (Subtype.ext (PGraph.rC_injective h))
  pN_range := by
    rintro (x | z)
    · constructor
      · rintro ⟨((a | z') | c), hn⟩ z hz <;> simp only [swapN, Sum.inl.injEq, reduceCtorEq] at hn
        · rw [← hz, ← hιN] at hn
          simp at hn
        · rw [← hz, ← hιN] at hn
          simp at hn
      · intro h
        obtain ⟨(a | z) | c, rfl⟩ := θ.eN.surjective x
        · exact ⟨.inl (.inl a), rfl⟩
        · exact (h z (hιN z).symm).elim
        · exact ⟨.inr c, rfl⟩
    · exact iff_of_true ⟨.inl (.inr z), rfl⟩ trivial
  pE_range := by
    rintro (f | d')
    · constructor
      · rintro ⟨((a | b) | c), he⟩ d hd hdf
        · simp only [swapE, Sum.inl.injEq] at he
          rw [← hdf, ← hιE] at he
          obtain ⟨hk, -⟩ := PGraph.eq_of_rA_eq_rK (θ.eE.injective he)
          exact hd hk
        · obtain ⟨d₀, hd₀, -, h'⟩ := swapE_inner α θ b
          rw [h'] at he
          cases he
        · simp only [swapE, Sum.inl.injEq] at he
          rw [← hdf, ← hιE] at he
          obtain ⟨hk, -⟩ := PGraph.eq_of_rK_eq_rC (θ.eE.injective he).symm
          exact c.2 hk
      · intro h
        obtain ⟨m, rfl⟩ := θ.eE.surjective f
        rcases PGraph.three_edge_cases (m₁ := mΩ₁) (m₂ := mΩ₂) m with ⟨a, rfl⟩ |
          ⟨k, hk, rfl⟩ | ⟨c, hc, rfl⟩
        · exact ⟨.inl (.inl a), rfl⟩
        · rcases k with d | ρ
          · exact (h d hk (hιE d).symm).elim
          · exact (hk rfl).elim
        · refine ⟨.inr ⟨c, hc⟩, ?_⟩
          rfl
    · refine iff_of_true ⟨.inl (.inr ⟨.inl d'.1, d'.2⟩), ?_⟩ trivial
      exact canonG_of_src_ne_none ιE α d'.2
  ins := by
    rintro ((a | z) | c)
    · rw [three_ins_A, List.map_map]
      change _ = (X.ins (θ.eN (.inl (.inl a)))).map _
      rw [θ.ins_map, three_ins_A, List.map_map, List.map_map]
      refine List.map_congr_left fun a' ha' => ?_
      have : PA.tgt a' ≠ none := by
        rw [(PA.mem_ins a a').1 ha']
        simp
      exact (canonF_rA α β θ hιE this).symm
    · rw [three_ins_K, List.map_map]
      change (((Λ.ins z).map Sum.inl).map _) = (Λ.ins z).map (canonG ιE α)
      rw [List.map_map]
      exact List.map_congr_left fun d _ => swapE_rK α θ hιE (.inl d)
    · rw [three_ins_C, List.map_map]
      change _ = (X.ins (θ.eN (.inr c))).map _
      rw [θ.ins_map, three_ins_C, List.map_map, List.map_map]
      exact List.map_congr_left fun c' _ => swapE_rC α β θ hιE c'
  outs := by
    rintro ((a | z) | c)
    · rw [three_outs_A, List.map_map]
      change _ = (X.outs (θ.eN (.inl (.inl a)))).map _
      rw [θ.outs_map, three_outs_A, List.map_map, List.map_map]
      rfl
    · rw [three_outs_K, List.map_map]
      change (((Λ.outs z).map Sum.inl).map _) = (Λ.outs z).map (canonG ιE α)
      rw [List.map_map]
      exact List.map_congr_left fun d _ => swapE_rK α θ hιE (.inl d)
    · rw [three_outs_C, List.map_map]
      change _ = (X.outs (θ.eN (.inr c))).map _
      rw [θ.outs_map, three_outs_C, List.map_map, List.map_map]
      refine List.map_congr_left fun c' hc' => ?_
      have hs : PC.src c' ≠ none := by
        rw [(PC.mem_outs c c').1 hc']
        simp
      rw [Function.comp_apply, PGraph.rC_of_src_ne_none hs]
      rfl
  dom := by
    rw [three_dom, θ.dom_map, three_dom, List.map_map, List.map_map, List.map_map]
    rfl
  cod := by
    rw [three_cod, θ.cod_map, three_cod, List.map_map, List.map_map, List.map_map]
    exact List.map_congr_left fun c _ => swapE_rC α β θ hιE c
  v₀ := by
    intro e
    rcases PGraph.three_edge_cases (m₁ := mΩ₁.trans (PGraph.liftDom α R).symm)
      (m₂ := (PGraph.liftCod β R).trans mΩ₂) e with ⟨a, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨c, hc, rfl⟩
    · change _ = X.val.v₀ (θ.eE (PGraph.rA a))
      rw [θ.v₀_map]
      rfl
    · rw [three_v₀_rK, swapE_rK α θ hιE]
      rcases k with d | ρ
      · change _ = canonV₀ X Λ (canonG ιE α d)
        rw [canonG_of_src_ne_none ιE α hk]
        rfl
      · exact (hk rfl).elim
    · rw [three_v₀_rC, PGraph.rC_of_src_ne_none hc]
      change _ = X.val.v₀ (θ.eE (PGraph.rC mΩ₁ mΩ₂ c))
      rw [θ.v₀_map, three_v₀_rC]
  v₁ := by
    rintro ((a | z) | c)
    · change _ = X.val.v₁ (θ.eN _)
      rw [θ.v₁_map]
      rfl
    · rfl
    · change _ = X.val.v₁ (θ.eN _)
      rw [θ.v₁_map]
      rfl

end MCT

end Diagram

end FreeMarkov
