/-
Free Markov categories, Stage 2: consequences of the canonical description of a
surgery (Section 3).

* `surgeryAt_iso`: the result does not depend on the choice of a layer `Γ[L, M]` with
  `Γ' ⊆ Γ[L, M]` and `Γ[L, M]^♭ = Γ'^♭` (proof of Lemma 3.3).
* `surgeryAt_iso_self`: "if there is an isomorphism `Λ → Ω` of polarized graphs that
  induces `α` and `β` then `Γ^Ω_Λ` is isomorphic to `Γ`".
* `recognition`: a diagram glued from three pieces whose middle one is `Λ ⊎ R` is the
  result of a surgery on any diagram isomorphic to the gluing with `Ω ⊎ R` in the middle
  (the "if" half of Lemma 3.3).
* `surgeryAt_reverse`: "a surgery can be reversed (by another surgery)".
* `surgeryAt_of_iso`: surgeries on isomorphic diagrams.
-/
module

public import FreeMarkov.Stage2.Canonical

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁

namespace FreeMarkov

open Relation

namespace PGraph.Iso

variable {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄} {Γ : PGraph N E}
  {Γ' : PGraph N' E'}

/-- Isomorphisms preserve the order of the nodes. -/
theorem lt_map (i : Γ.Iso Γ') {x y : N} (h : Γ.Lt x y) : Γ'.Lt (i.eN x) (i.eN y) := by
  refine transGen_map i.eN (fun a b hab => ?_) h
  obtain ⟨e, h₁, h₂⟩ := hab
  exact ⟨i.eE e, by rw [i.src_map, h₁]; rfl, by rw [i.tgt_map, h₂]; rfl⟩

end PGraph.Iso

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-! ### Surgeries computed with a layer -/

section Layer

variable {N : Type u₁} {E : Type u₂} (Γ : Diagram G N E) {A : Subgraph N E}
  (V : Γ.ValidLayer A) {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PDiagram G NΩ EΩ}
  {NΛ : Type u₅} {EΛ : Type u₆} {Λ : PDiagram G NΛ EΛ}
  (φ : Ω.Iso (Γ.subD A V.edgeAt))
  (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e})
  (hα : ∀ e, Ω.val.v₀ (α e).1 = Λ.val.v₀ e.1) (hβ : ∀ e, Ω.val.v₀ (β e).1 = Λ.val.v₀ e.1)

/-- The canonical description of a surgery computed with any layer: it only depends on
`Γ`, `φ`, `Λ`, `α`, `β`. -/
noncomputable def surgeryAt_canonProj {ιN : NΩ → N} {ιE : EΩ → E}
    (hιN : ∀ z, (φ.eN z).1 = ιN z) (hιE : ∀ d, (φ.eE d).1 = ιE d) :
    CanonProj Γ Ω ιN ιE α β (Γ.surgeryAt V φ α β hα hβ) :=
  canonProj α β hα hβ (Γ.isoDecomp V φ) (fun z => (Γ.isoDecomp_eN V φ _).trans (hιN z))
    (fun d => ((Γ.isoDecomp_eE V φ _).trans (Γ.decompE_rK V φ (.inl d))).trans (hιE d))

/-- **Independence of the layer** (proof of Lemma 3.3): "the construction of `Γ^Ω_Λ` does
not depend on the choice of a layer `Γ[L, M]` with `Γ' ⊆ Γ[L, M]` and
`Γ[L, M]^♭ = Γ'^♭`". -/
noncomputable def surgeryAt_iso (V' : Γ.ValidLayer A) :
    (Γ.surgeryAt V φ α β hα hβ).Iso (Γ.surgeryAt V' φ α β hα hβ) :=
  (Γ.surgeryAt_canonProj V φ α β hα hβ (fun _ => rfl) (fun _ => rfl)).iso
    (Γ.surgeryAt_canonProj V' φ α β hα hβ (fun _ => rfl) (fun _ => rfl))

/-- The surgery of the paper (computed with `Γ'^♯`) is isomorphic to the surgery computed
with any layer as in Lemma 3.2. -/
noncomputable def surgery_iso_surgeryAt (hA : Γ.IsNormal A) :
    (Γ.surgery α β hα hβ hA φ).Iso (Γ.surgeryAt V φ α β hα hβ) :=
  Γ.surgeryAt_iso hA.sharpLayer φ α β hα hβ V

theorem liftDom_eq_of_induces (ψ : Λ.Iso Ω) (hψ : ∀ d, (α d).1 = ψ.eE d.1) {R : Type u₇}
    (k : {k // (Λ.toPGraph.addLoose R).IsDom k}) :
    (Equiv.sumCongr ψ.eE (Equiv.refl R)) k.1 = (PGraph.liftDom α R k).1 := by
  rcases k with ⟨d | ρ, h⟩
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, PGraph.liftDom_inl, Sum.inl.injEq]
    exact (hψ ⟨d, h⟩).symm
  · rfl

theorem liftCod_eq_of_induces (ψ : Λ.Iso Ω) (hψ : ∀ d, (β d).1 = ψ.eE d.1) {R : Type u₇}
    (k : {k // (Λ.toPGraph.addLoose R).IsCod k}) :
    (Equiv.sumCongr ψ.eE (Equiv.refl R)) k.1 = (PGraph.liftCod β R k).1 := by
  rcases k with ⟨d | ρ, h⟩
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, PGraph.liftCod_inl, Sum.inl.injEq]
    exact (hψ ⟨d, h⟩).symm
  · rfl

/-- "If there is an isomorphism `Λ → Ω` of polarized graphs that induces `α` and `β`
then `Γ^Ω_Λ` is isomorphic to `Γ`" (for diagrams: an isomorphism of diagrams). -/
noncomputable def surgeryAt_iso_self (ψ : Λ.Iso Ω) (hψα : ∀ d, (α d).1 = ψ.eE d.1)
    (hψβ : ∀ d, (β d).1 = ψ.eE d.1) : (Γ.surgeryAt V φ α β hα hβ).Iso Γ :=
  (isoMid (ψ.addLoose (Γ.rLabel V))
      (fun c => by
        change _ = (Equiv.sumCongr ψ.eE (Equiv.refl V.R)) _
        rw [liftDom_eq_of_induces α ψ hψα]
        simp [PGraph.ValidLayer.m₁])
      (fun k k' hk => by
        have : k' = PGraph.liftCod β V.R k :=
          Subtype.ext (hk.trans (liftCod_eq_of_induces β ψ hψβ k))
        subst this
        rfl)).trans
    (Γ.isoDecomp V φ)

end Layer

/-! ### Recognition of surgeries (the "if" half of Lemma 3.3) -/

section Recognition

variable {NX : Type u₁} {EX : Type u₂} {X : Diagram G NX EX}
  {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PDiagram G NΩ EΩ} {NΛ : Type u₅} {EΛ : Type u₆}
  {Λ : PDiagram G NΛ EΛ} {NA : Type u₇} {EA : Type u₈} {NC : Type u₉} {EC : Type u₁₀}
  {PA : PDiagram G NA EA} {PC : PDiagram G NC EC} {R : Type u₁₁} {r : R → S}
  (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e})
  (hα : ∀ e, Ω.val.v₀ (α e).1 = Λ.val.v₀ e.1) (hβ : ∀ e, Ω.val.v₀ (β e).1 = Λ.val.v₀ e.1)
  {mΩ₁ : {e // PA.IsCod e} ≃ {e // (Ω.toPGraph.addLoose R).IsDom e}}
  {mΩ₂ : {e // (Ω.toPGraph.addLoose R).IsCod e} ≃ {e // PC.IsDom e}}
  {hΩ₁ : ∀ c, (Ω.addLoose r).val.v₀ (mΩ₁ c).1 = PA.val.v₀ c.1}
  {hΩ₂ : ∀ c, PC.val.v₀ (mΩ₂ c).1 = (Ω.addLoose r).val.v₀ c.1}
  {dA : Enumeration PA.IsDom} {cC : Enumeration PC.IsCod}
  (θ : (Diagram.three PA (Ω.addLoose r) PC mΩ₁ mΩ₂ hΩ₁ hΩ₂ dA cC).Iso X)

/-- The image of `Ω` under a three-piece decomposition: a subgraph of `X`. -/
def imageSub : Subgraph NX EX :=
  ⟨fun x => ∃ z, θ.eN (.inl (.inr z)) = x, fun f => ∃ d, θ.eE (PGraph.rK mΩ₁ (.inl d)) = f⟩

theorem src_map_eq_some {e} {x : NX} (h : X.src (θ.eE e) = some x) :
    (PGraph.three mΩ₁ mΩ₂).src e = some (θ.eN.symm x) := by
  rw [θ.toAIso.toIso.src_map] at h
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Equiv.symm_apply_apply]
  exact hn

theorem tgt_map_eq_some {e} {x : NX} (h : X.tgt (θ.eE e) = some x) :
    (PGraph.three mΩ₁ mΩ₂).tgt e = some (θ.eN.symm x) := by
  rw [θ.toAIso.toIso.tgt_map] at h
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Equiv.symm_apply_apply]
  exact hn

theorem imageSub_edgeAt : X.EdgeAt (imageSub θ) := by
  rintro x ⟨z, rfl⟩ f hf
  obtain ⟨e, rfl⟩ := θ.eE.surjective f
  rcases hf with hf | hf
  · have := src_map_eq_some θ hf
    rw [Equiv.symm_apply_apply, PGraph.three_src_eq_some_K_iff] at this
    obtain ⟨d | ρ, hd, rfl⟩ := this
    · exact ⟨d, rfl⟩
    · cases hd
  · have := tgt_map_eq_some θ hf
    rw [Equiv.symm_apply_apply, PGraph.three_tgt_eq_some_K_iff] at this
    obtain ⟨d | ρ, hd, rfl⟩ := this
    · exact ⟨d, rfl⟩
    · cases hd

theorem lt_of_lt {x y : NX} (h : X.Lt x y) :
    (PGraph.three mΩ₁ mΩ₂).Lt (θ.eN.symm x) (θ.eN.symm y) :=
  θ.symm.toAIso.toIso.lt_map h

/-- The image of the nodes of `A`: a level of `X`. -/
def imageL : Set NX := {x | ∃ a, θ.eN (.inl (.inl a)) = x}

/-- The image of the nodes of `A` and `Ω ⊎ R`: a level of `X`. -/
def imageM : Set NX := {x | ∃ n, θ.eN (.inl n) = x}

theorem isLevel_imageL : X.IsLevel (imageL θ) := by
  rintro x y hxy ⟨a, rfl⟩
  have h := lt_of_lt θ hxy
  rw [Equiv.symm_apply_apply] at h
  obtain ⟨(a' | z) | c, rfl⟩ := θ.eN.surjective x
  · exact ⟨a', rfl⟩
  · rw [Equiv.symm_apply_apply] at h
    exact (PGraph.three_not_lt_K_A z a h).elim
  · rw [Equiv.symm_apply_apply] at h
    exact (PGraph.three_not_lt_C_left c _ h).elim

theorem isLevel_imageM : X.IsLevel (imageM θ) := by
  rintro x y hxy ⟨n, rfl⟩
  have h := lt_of_lt θ hxy
  rw [Equiv.symm_apply_apply] at h
  obtain ⟨n' | c, rfl⟩ := θ.eN.surjective x
  · exact ⟨n', rfl⟩
  · rw [Equiv.symm_apply_apply] at h
    exact (PGraph.three_not_lt_C_left c _ h).elim

theorem imageSub_node_iff (x : NX) :
    (imageSub θ).node x ↔ X.LayerNode (imageL θ) (imageM θ) x := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    rintro ⟨a, ha⟩
    simpa using θ.eN.injective ha
  · rintro ⟨⟨a | z, rfl⟩, hL⟩
    · exact (hL ⟨a, rfl⟩).elim
    · exact ⟨z, rfl⟩

/-- The layer of `X` given by the decomposition: between the images of the nodes of
`A` and of `A ∪ Ω`. -/
def imageLayer : X.ValidLayer (imageSub θ) where
  L := imageL θ
  M := imageM θ
  isLevel_L := isLevel_imageL θ
  isLevel_M := isLevel_imageM θ
  subset := by
    rintro x ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  le := by
    constructor
    · intro x hx
      exact (imageSub_node_iff θ x).1 hx
    · rintro f ⟨d, rfl⟩
      constructor
      · intro x hx
        have h := src_map_eq_some θ hx
        obtain ⟨n', hn'⟩ := PGraph.three_src_rK_eq_some h
        exact ⟨n', by rw [← hn', Equiv.apply_symm_apply]⟩
      · intro y hy ⟨a, ha⟩
        have h := tgt_map_eq_some θ hy
        rw [← ha, Equiv.symm_apply_apply] at h
        exact PGraph.three_tgt_rK_eq_some h a rfl
  flat_eq := PGraph.flat_eq_of_edgeAt (funext fun x => propext (imageSub_node_iff θ x).symm)
    (X.edgeAt_layerSub (isLevel_imageL θ) (isLevel_imageM θ)) (imageSub_edgeAt θ)

theorem imageN_injective : Function.Injective fun z => θ.eN (.inl (.inr z)) := fun z z' h => by
  simpa using θ.eN.injective h

/-- The isomorphism from `Ω` onto its image in `X`. -/
noncomputable def imageIso : Ω.Iso (X.subD (imageSub θ) (imageSub_edgeAt θ)) :=
  PDiagram.Iso.ofProj (fun z => θ.eN (.inl (.inr z))) (fun d => θ.eE (PGraph.rK mΩ₁ (.inl d)))
    Subtype.val Subtype.val (imageN_injective θ) Subtype.val_injective
    (ιE_injective θ (ιE := fun d => θ.eE (PGraph.rK mΩ₁ (.inl d))) fun _ => rfl)
    Subtype.val_injective
    (fun t => ⟨fun ⟨z, h⟩ => ⟨⟨t, z, h⟩, rfl⟩, fun ⟨x, h⟩ => h ▸ x.2⟩)
    (fun t => ⟨fun ⟨d, h⟩ => ⟨⟨t, d, h⟩, rfl⟩, fun ⟨x, h⟩ => h ▸ x.2⟩)
    (by
      intro z n' h
      rw [PGraph.sub_ins_map_val n' fun e he =>
        imageSub_edgeAt θ _ n'.2 e (Or.inr ((X.mem_ins _ e).1 he)), ← h, θ.ins_map,
        three_ins_K, List.map_map]
      change _ = (((Ω.ins z).map Sum.inl).map _)
      rw [List.map_map]
      rfl)
    (by
      intro z n' h
      rw [PGraph.sub_outs_map_val n' fun e he =>
        imageSub_edgeAt θ _ n'.2 e (Or.inl ((X.mem_outs _ e).1 he)), ← h, θ.outs_map,
        three_outs_K, List.map_map]
      change _ = (((Ω.outs z).map Sum.inl).map _)
      rw [List.map_map]
      rfl)
    (by
      intro d e' h
      change _ = X.val.v₀ e'.1
      rw [← h, θ.v₀_map, three_v₀_rK]
      rfl)
    (by
      intro z n' h
      change _ = X.val.v₁ n'.1
      rw [← h, θ.v₁_map]
      rfl)

theorem imageIso_eN (z : NΩ) : ((imageIso θ).eN z).1 = θ.eN (.inl (.inr z)) :=
  equivOfProj_spec _ Subtype.val (imageN_injective θ) Subtype.val_injective _ z

theorem imageIso_eE (d : EΩ) : ((imageIso θ).eE d).1 = θ.eE (PGraph.rK mΩ₁ (.inl d)) :=
  equivOfProj_spec _ Subtype.val
    (ιE_injective θ (ιE := fun d => θ.eE (PGraph.rK mΩ₁ (.inl d))) fun _ => rfl)
    Subtype.val_injective _ d

include θ in
/-- **Recognition of surgeries** (the "if" half of Lemma 3.3): if `X` is isomorphic to
the diagram glued from three pieces whose middle one is `Ω ⊎ R`, then the diagram glued
from the same pieces with `Λ ⊎ R` in the middle (along the bijections composed with
`α⁻¹`, `β`) is isomorphic to the result of an `(Ω / Λ, α, β)`-surgery on `X`; the normal
subgraph is the image of `Ω` ("it need not be `Γ'` itself"). -/
theorem recognition : ∃ (A : Subgraph NX EX) (hA : X.IsNormal A)
    (φ : Ω.Iso (X.subD A hA.edge_at)),
    Nonempty ((threeSwap r α β hα hβ hΩ₁ hΩ₂ dA cC).Iso (X.surgery α β hα hβ hA φ)) :=
  ⟨imageSub θ, (imageLayer θ).isNormal, imageIso θ,
    ⟨(canonProj α β hα hβ θ (fun _ => rfl) (fun _ => rfl)).iso
      (X.surgeryAt_canonProj _ (imageIso θ) α β hα hβ (imageIso_eN θ) (imageIso_eE θ))⟩⟩

end Recognition

/-! ### Reversibility and invariance -/

section Reverse

variable {N : Type u₁} {E : Type u₂} (Γ : Diagram G N E) {A : Subgraph N E}
  (V : Γ.ValidLayer A) {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PDiagram G NΩ EΩ}
  {NΛ : Type u₅} {EΛ : Type u₆} {Λ : PDiagram G NΛ EΛ}
  (φ : Ω.Iso (Γ.subD A V.edgeAt))
  (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}) (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e})
  (hα : ∀ e, Ω.val.v₀ (α e).1 = Λ.val.v₀ e.1) (hβ : ∀ e, Ω.val.v₀ (β e).1 = Λ.val.v₀ e.1)

theorem symm_v₀ {NΩ' : Type u₇} {EΩ' : Type u₈} {NΛ' : Type u₉} {EΛ' : Type u₁₀}
    {Ω' : PDiagram G NΩ' EΩ'} {Λ' : PDiagram G NΛ' EΛ'}
    (α : {e // Λ'.IsDom e} ≃ {e // Ω'.IsDom e}) (hα : ∀ e, Ω'.val.v₀ (α e).1 = Λ'.val.v₀ e.1)
    (e : {e // Ω'.IsDom e}) : Λ'.val.v₀ (α.symm e).1 = Ω'.val.v₀ e.1 := by
  rw [← hα, Equiv.apply_symm_apply]

theorem symm_v₀' {NΩ' : Type u₇} {EΩ' : Type u₈} {NΛ' : Type u₉} {EΛ' : Type u₁₀}
    {Ω' : PDiagram G NΩ' EΩ'} {Λ' : PDiagram G NΛ' EΛ'}
    (β : {e // Λ'.IsCod e} ≃ {e // Ω'.IsCod e}) (hβ : ∀ e, Ω'.val.v₀ (β e).1 = Λ'.val.v₀ e.1)
    (e : {e // Ω'.IsCod e}) : Λ'.val.v₀ (β.symm e).1 = Ω'.val.v₀ e.1 := by
  rw [← hβ, Equiv.apply_symm_apply]

/-- **Reversibility** ("Observe that a surgery can be reversed (by another surgery) in
the sense that the resulting diagram is isomorphic to the one we started with"): an
`(Λ / Ω, α⁻¹, β⁻¹)`-surgery on `Γ^Ω_Λ` gives back `Γ`. -/
theorem surgeryAt_reverse :
    ∃ (A' : Subgraph _ _) (hA' : (Γ.surgeryAt V φ α β hα hβ).IsNormal A')
      (φ' : Λ.Iso ((Γ.surgeryAt V φ α β hα hβ).subD A' hA'.edge_at)),
      Nonempty (((Γ.surgeryAt V φ α β hα hβ).surgery α.symm β.symm (symm_v₀ α hα)
        (symm_v₀' β hβ) hA' φ').Iso Γ) := by
  obtain ⟨A', hA', φ', ⟨i⟩⟩ := recognition (Ω := Λ) (Λ := Ω) α.symm β.symm (symm_v₀ α hα)
    (symm_v₀' β hβ) (Diagram.Iso.refl (Γ.surgeryAt V φ α β hα hβ))
  refine ⟨A', hA', φ', ⟨i.symm.trans ((isoMid (PDiagram.Iso.refl _) ?_ ?_).trans
    (Γ.isoDecomp V φ))⟩⟩
  · intro c
    change _ = ((PGraph.liftDom α.symm V.R).symm ((PGraph.liftDom α V.R).symm _)).1
    rw [← PGraph.liftDom_symm, Equiv.symm_symm, Equiv.apply_symm_apply]
  · intro k k' hk
    have : k' = k := Subtype.ext hk
    subst this
    change _ = (V.codMatch φ.toPIso) ((PGraph.liftCod β V.R) ((PGraph.liftCod β.symm V.R) k'))
    rw [← PGraph.liftCod_symm, Equiv.apply_symm_apply]

/-- **Invariance under isomorphisms** ("If `[Γ] = [Υ]` ... then clearly ..."): a surgery on
`Γ` can be carried out on any diagram isomorphic to `Γ`, with an isomorphic result. -/
theorem surgeryAt_of_iso {N₁ : Type u₇} {E₁ : Type u₈} {Γ₁ : Diagram G N₁ E₁} (ι : Γ.Iso Γ₁) :
    ∃ (A₁ : Subgraph N₁ E₁) (hA₁ : Γ₁.IsNormal A₁) (φ₁ : Ω.Iso (Γ₁.subD A₁ hA₁.edge_at)),
      Nonempty ((Γ.surgeryAt V φ α β hα hβ).Iso (Γ₁.surgery α β hα hβ hA₁ φ₁)) :=
  recognition α β hα hβ ((Γ.isoDecomp V φ).trans ι)

end Reverse

end Diagram

end FreeMarkov
