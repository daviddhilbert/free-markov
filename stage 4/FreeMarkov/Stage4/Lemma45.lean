/-
Free Markov categories, Stage 4: **Lemma 4.5** (dead inputs), the third item and the lemma in full.

"There is a unique morphism `g : a'' → b` in `F_s(G)/S_M` such that `[Γ]/S_M = (g ⊗ ε_{a'}) ∘ τ`,
where `τ : a → a''a'` is the symmetry that moves the letters at the positions in `J` to the end and
does not change the order of the other letters or that of the letters moved; moreover, in every
diagram that represents `g`, every edge in the domain begins a directed path that ends in the
codomain."

* `JoyalStreet.tauM a P`: the symmetry `τ` in `F_s(G)/S_M`, the class of the node-free diagram of
  the permutation `tauPos` (the positions outside `P`, then those in `P`).
* `JoyalStreet.lemma_4_5_unique`: `g ↦ (g ⊗ ε_{a'}) ∘ τ` is injective (through skeletons:
  `glueNodeFreeIso`, `SkeletonIso.of_reanchor`, `SameSkeleton.of_tensor`, Lemma 4.4).
* `JoyalStreet.lemma_4_5_minimal`: existence for a Markov minimal diagram, through the
  decomposition `[Γ] = [Γ''] ∘ [Γ[∅, deadL]]` (Remark 2.4) and `sameSkeleton_lower`.
* `JoyalStreet.lemma_4_5`: the three items.

The third item uses the cited result C1 (through `F_s(G)/S_M`); the first two do not.
-/
module

public import FreeMarkov.Stage4.DeadLevel

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open CategoryTheory StrictSMC Relation

open scoped Classical

/-- In a symmetric strict monoidal category, `g ∘ (1_x ⊗ ε) = (g ⊗ ε)` up to the units. -/
theorem StrictSMC.id_tensor_comp {C : Type*} [Monoid C] [Category C] [StrictSMC C] {x y z : C}
    (g : x ⟶ y) (ε : z ⟶ 1) :
    (𝟙 x ⊗ₛ ε) ≫ eqToHom (mul_one x) ≫ g = (g ⊗ₛ ε) ≫ eqToHom (mul_one y) := by
  have h₁ : g ⊗ₛ ε = (𝟙 x ⊗ₛ ε) ≫ (g ⊗ₛ 𝟙 1) := by
    rw [← tensorHom_comp, Category.id_comp, Category.comp_id]
  rw [h₁, Category.assoc,
    Arrow.comp_eqToHom_eq_of_mk_eq (tensorHom_id_one g) (mul_one x) (mul_one y)]

namespace JoyalStreet

open Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} (J : JoyalStreet G.toFreeGraphMonoid)

theorem cls_comp_eqToHom {a b b' : J.Fs} (f : a ⟶ b) (h : b = b') :
    J.cls (f ≫ eqToHom h) = J.cls f := by
  subst h
  rw [eqToHom_refl, Category.comp_id]

/-- The symmetry `τ : a → a''a'` of `F_s(G)`: the class of the node-free diagram of `tauPos`. -/
noncomputable def tauH (a : FreeMonoid S) (P : ℕ → Prop) :
    DHom G.toFreeGraphMonoid a (liveW a P * deadW a P) :=
  ⟨DClass.mk (permNF (G := G) a (tauPos (wlen a) P) (tauPos_nodup _ _) (mem_tauPos _ _)),
    by rw [DClass.dom_mk, permNF_domWord], by rw [DClass.cod_mk, permNF_tauPos_codWord]⟩

/-- `τ` as a morphism of `F_s(G)`. -/
noncomputable def tauF (a : FreeMonoid S) (P : ℕ → Prop) :
    Fs.of J a ⟶ Fs.of J (liveW a P) * Fs.of J (deadW a P) :=
  J.hom (tauH a P)

/-- `ε_{x_1} ⊗ ⋯ ⊗ ε_{x_k}` as a morphism of `F_s(G)`. -/
noncomputable def dwF (x : FreeMonoid S) : Fs.of J x ⟶ 1 :=
  J.hom (G.discWord x)

theorem projM_dwF (x : FreeMonoid S) :
    J.projM.map (J.dwF x) = J.discardM (J.projM.obj (Fs.of J x)) :=
  J.projM_discWord x

/-- **The symmetry `τ`** of Lemma 4.5 in `F_s(G)/S_M`. -/
noncomputable def tauM (a : FreeMonoid S) (P : ℕ → Prop) :
    J.projM.obj (Fs.of J a) ⟶
      J.projM.obj (Fs.of J (liveW a P)) * J.projM.obj (Fs.of J (deadW a P)) :=
  J.projM.map (J.tauF a P)

/-- The equation `[Γ]/S_M = (g ⊗ ε_{a'}) ∘ τ` of Lemma 4.5, for `f` with `J.cls f = [Γ]`. -/
def IsFactor {a b : FreeMonoid S} (f : Fs.of J a ⟶ Fs.of J b) (P : ℕ → Prop)
    (g : J.projM.obj (Fs.of J (liveW a P)) ⟶ J.projM.obj (Fs.of J b)) : Prop :=
  J.projM.map f = J.tauM a P ≫ (g ⊗ₛ J.discardM (J.projM.obj (Fs.of J (deadW a P)))) ≫
    eqToHom (mul_one _)

theorem isFactor_congr {a b : FreeMonoid S} {f f' : Fs.of J a ⟶ Fs.of J b}
    (hf : J.projM.map f = J.projM.map f') (P : ℕ → Prop)
    (g : J.projM.obj (Fs.of J (liveW a P)) ⟶ J.projM.obj (Fs.of J b)) :
    J.IsFactor f P g ↔ J.IsFactor f' P g := by
  unfold IsFactor
  rw [hf]

theorem projM_surj {a b : J.Fs} (g : J.projM.obj a ⟶ J.projM.obj b) :
    ∃ h : a ⟶ b, J.projM.map h = g :=
  ⟨Quotient.out g, Quotient.out_eq g⟩

/-- `(h ⊗ ε_{a'}) ∘ τ` for a morphism `h` of `F_s(G)`, computed in `F_s(G)`. -/
theorem tau_comp_eq {a b : FreeMonoid S} (P : ℕ → Prop)
    (h : Fs.of J (liveW a P) ⟶ Fs.of J b) :
    J.tauM a P ≫ (J.projM.map h ⊗ₛ J.discardM (J.projM.obj (Fs.of J (deadW a P)))) ≫
        eqToHom (mul_one _) =
      J.projM.map (J.tauF a P ≫ (h ⊗ₛ J.dwF (deadW a P)) ≫ eqToHom (mul_one (Fs.of J b))) := by
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, ← projM_dwF]
  rfl

theorem cls_tau_comp {a b : FreeMonoid S} (P : ℕ → Prop) {N' : Type u₃} {E' : Type u₄}
    [Finite N'] [Finite E'] (Υ : Diagram G.toFreeGraphMonoid N' E')
    (h : Fs.of J (liveW a P) ⟶ Fs.of J b) (hh : J.cls h = DClass.mk Υ)
    (hΘ : (permNF (G := G) a (tauPos (wlen a) P) (tauPos_nodup _ _) (mem_tauPos _ _)).codWord =
      (Υ.tensor (G.discListD (FreeMonoid.toList (deadW a P)))).domWord) :
    J.cls (J.tauF a P ≫ (h ⊗ₛ J.dwF (deadW a P)) ≫ eqToHom (mul_one (Fs.of J b))) =
      DClass.mk ((permNF (G := G) a _ _ _).glue
        (Υ.tensor (G.discListD (FreeMonoid.toList (deadW a P)))) hΘ) := by
  rw [← Category.assoc, cls_comp_eqToHom, cls_comp, cls_tensor, hh]
  change (DClass.mk _).comp ((DClass.mk Υ).tensor (G.discList _).1) = _
  rw [← G.mk_discListD, DClass.mk_tensor, DClass.mk_comp _ _ hΘ]

/-- **Uniqueness in the third item of Lemma 4.5**: `g ↦ (g ⊗ ε_{a'}) ∘ τ` is injective. -/
theorem lemma_4_5_unique {a b : FreeMonoid S} (P : ℕ → Prop)
    (g g' : J.projM.obj (Fs.of J (liveW a P)) ⟶ J.projM.obj (Fs.of J b))
    (h : J.tauM a P ≫ (g ⊗ₛ J.discardM (J.projM.obj (Fs.of J (deadW a P)))) ≫ eqToHom (mul_one _) =
      J.tauM a P ≫ (g' ⊗ₛ J.discardM (J.projM.obj (Fs.of J (deadW a P)))) ≫
        eqToHom (mul_one _)) :
    g = g' := by
  obtain ⟨h₁, rfl⟩ := J.projM_surj g
  obtain ⟨h₂, rfl⟩ := J.projM_surj g'
  rw [tau_comp_eq, tau_comp_eq, quotProj_map_eq_iff] at h
  obtain ⟨n₁, m₁, Υ₁, hΥ₁⟩ := DClass.exists_eq_mk (J.cls h₁)
  obtain ⟨n₂, m₂, Υ₂, hΥ₂⟩ := DClass.exists_eq_mk (J.cls h₂)
  have hd₁ : Υ₁.domWord = liveW a P := by rw [← DClass.dom_mk, ← hΥ₁]; exact J.cls_dom h₁
  have hd₂ : Υ₂.domWord = liveW a P := by rw [← DClass.dom_mk, ← hΥ₂]; exact J.cls_dom h₂
  have hc₁ : Υ₁.codWord = b := by rw [← DClass.cod_mk, ← hΥ₁]; exact J.cls_cod h₁
  have hc₂ : Υ₂.codWord = b := by rw [← DClass.cod_mk, ← hΥ₂]; exact J.cls_cod h₂
  have hDd : (G.discListD (FreeMonoid.toList (deadW a P))).domWord = deadW a P := by
    rw [G.discListD_domWord, FreeMonoid.ofList_toList]
  have hΘ₁ : (permNF (G := G) a (tauPos (wlen a) P) (tauPos_nodup _ _) (mem_tauPos _ _)).codWord =
      (Υ₁.tensor (G.discListD (FreeMonoid.toList (deadW a P)))).domWord := by
    rw [permNF_tauPos_codWord, tensor_domWord, hd₁, hDd]
  have hΘ₂ : (permNF (G := G) a (tauPos (wlen a) P) (tauPos_nodup _ _) (mem_tauPos _ _)).codWord =
      (Υ₂.tensor (G.discListD (FreeMonoid.toList (deadW a P)))).domWord := by
    rw [permNF_tauPos_codWord, tensor_domWord, hd₂, hDd]
  rw [J.cls_tau_comp P Υ₁ h₁ hΥ₁ hΘ₁, J.cls_tau_comp P Υ₂ h₂ hΥ₂ hΘ₂, lemma_4_4_iff] at h
  have h' := ((Iso.sameSkeleton (glueNodeFreeIso hΘ₁)).symm.trans h).trans
    (Iso.sameSkeleton (glueNodeFreeIso hΘ₂))
  obtain ⟨hdw, hcw, π, hπ⟩ := h'
  have hlen := dom_length_eq_of_domWord (hΘ₁.symm.trans hΘ₂)
  have hπ' := SkeletonIso.of_reanchor reorderPos (reorder_getElem? hΘ₁) (reorder_getElem? hΘ₂)
    (reorderPos_surj hΘ₁) hlen hπ
  have hs := SameSkeleton.of_tensor (FreeDDGraphMonoidAux.discListD_isDisc _)
    (FreeDDGraphMonoidAux.discListD_isDisc _)
    ⟨hΘ₁.symm.trans hΘ₂, by rw [tensor_codWord, tensor_codWord, hc₁, hc₂], π, hπ'⟩
    (hd₁.trans hd₂.symm) (hc₁.trans hc₂.symm)
  rw [quotProj_map_eq_iff, hΥ₁, hΥ₂]
  exact lemma_4_4_iff.2 hs

section Minimal

variable {N : Type u₁} {E : Type u₂} [Finite N] [Finite E]

/-- The lower layer `Γ[∅, deadL]` represents `(1_{a''} ⊗ ε_{a'}) ∘ τ` in `F_s(G)/S_M`. -/
theorem projM_lower {Γ : Diagram G.toFreeGraphMonoid N E} (hΓ : Γ.MarkovMinimal)
    (l : Fs.of J Γ.domWord ⟶ Fs.of J (liveW Γ.domWord Γ.Dead))
    (hl : J.cls l = DClass.mk (Γ.lowerD (isLevel_deadL hΓ) (deadEnum hΓ))) :
    J.projM.map l = J.tauM Γ.domWord Γ.Dead ≫
      (𝟙 _ ⊗ₛ J.discardM (J.projM.obj (Fs.of J (deadW Γ.domWord Γ.Dead)))) ≫
        eqToHom (mul_one _) := by
  have e : 𝟙 (J.projM.obj (Fs.of J (liveW Γ.domWord Γ.Dead))) =
      J.projM.map (𝟙 (Fs.of J (liveW Γ.domWord Γ.Dead))) := (J.projM.map_id _).symm
  rw [e, tau_comp_eq, quotProj_map_eq_iff, hl,
    J.cls_tau_comp Γ.Dead (idD G.toFreeGraphMonoid (liveW Γ.domWord Γ.Dead)) _ (J.cls_id _)
      (tauHΘ Γ.domWord Γ.Dead), lemma_4_4_iff]
  exact (sameSkeleton_lower hΓ).trans (Iso.sameSkeleton (glueNodeFreeIso (tauHΘ _ _))).symm

/-- **Existence in the third item of Lemma 4.5, for a Markov minimal diagram**, with the "moreover"
clause: `g` is the class of `Γ'' = Γ[deadL, Γ̇]`, and no diagram representing `g` has a dead edge
in its domain. -/
theorem lemma_4_5_minimal {Γ : Diagram G.toFreeGraphMonoid N E} (hΓ : Γ.MarkovMinimal)
    {a b : FreeMonoid S} (f : Fs.of J a ⟶ Fs.of J b) (hf : J.cls f = DClass.mk Γ) :
    ∃ g, J.IsFactor f Γ.Dead g ∧
      ∀ {N' : Type u₃} {E' : Type u₄} [Finite N'] [Finite E'] (Υ : Diagram G.toFreeGraphMonoid N' E')
        (h : Fs.of J (liveW a Γ.Dead) ⟶ Fs.of J b), J.cls h = DClass.mk Υ →
        J.projM.map h = g → ∀ j, ¬ Υ.Dead j := by
  have ha : Γ.domWord = a := by rw [← DClass.dom_mk, ← hf]; exact J.cls_dom f
  have hb : Γ.codWord = b := by rw [← DClass.cod_mk, ← hf]; exact J.cls_cod f
  subst ha hb
  set hL := isLevel_deadL hΓ
  set oL := deadEnum hΓ
  let l : Fs.of J Γ.domWord ⟶ Fs.of J (liveW Γ.domWord Γ.Dead) :=
    J.hom ⟨DClass.mk (Γ.lowerD hL oL), by rw [DClass.dom_mk, lowerD_domWord hΓ],
      by rw [DClass.cod_mk, lowerD_codWord hΓ]⟩
  let u : Fs.of J (liveW Γ.domWord Γ.Dead) ⟶ Fs.of J Γ.codWord :=
    J.hom ⟨DClass.mk (Γ.upperD hL oL), by rw [DClass.dom_mk, upperD_domWord hΓ],
      by rw [DClass.cod_mk, upperD_codWord hΓ]⟩
  have hf' : f = l ≫ u := Subtype.ext (hf.trans (Γ.mk_eq_comp_lower_upper hL oL))
  refine ⟨J.projM.map u, ?_, fun Υ h hh hu j => ?_⟩
  · unfold IsFactor
    rw [hf', Functor.map_comp, J.projM_lower hΓ l rfl, Category.assoc, Category.assoc,
      StrictSMC.id_tensor_comp]
  · rw [quotProj_map_eq_iff, hh] at hu
    rw [lemma_4_5_dead hu]
    exact not_dead_upper hΓ j

end Minimal

section General

variable {N : Type u₁} {E : Type u₂} [Finite N] [Finite E]

/-- **Lemma 4.5** (dead inputs). Let `Γ` be a diagram from `a` to `b` representing the morphism `f`
of `F_s(G)`, and `J = Γ.Dead` the positions of the edges of `dom(Γ)` that are not the origin of a
consumer.
* `j ∉ J` iff a directed path begins with the `j`-th edge of `dom(Γ)` and ends in `cod(Γ)`;
* `J` is the same for all the diagrams in the `S_M`-congruence class of `Γ`;
* there is a unique `g : a'' → b` in `F_s(G)/S_M` with `[Γ]/S_M = (g ⊗ ε_{a'}) ∘ τ`, and in every
  diagram that represents `g` every edge of the domain begins a directed path that ends in the
  codomain. -/
theorem lemma_4_5 {Γ : Diagram G.toFreeGraphMonoid N E} {a b : FreeMonoid S}
    (f : Fs.of J a ⟶ Fs.of J b) (hf : J.cls f = DClass.mk Γ) :
    (∀ j < Γ.dom.length, ¬ Γ.Dead j ↔ ∃ k : ℕ, Γ.toAGraph.HasPath (.edge j) (.edge k)) ∧
    (∀ {N' : Type u₃} {E' : Type u₄} [Finite N'] [Finite E'] (Υ : Diagram G.toFreeGraphMonoid N' E'),
      SRel G.markovTemplates (DClass.mk Γ) (DClass.mk Υ) → ∀ j, Γ.Dead j ↔ Υ.Dead j) ∧
    (∃! g, J.IsFactor f Γ.Dead g) ∧
    (∀ g, J.IsFactor f Γ.Dead g → ∀ {N' : Type u₃} {E' : Type u₄} [Finite N'] [Finite E']
      (Υ : Diagram G.toFreeGraphMonoid N' E') (h : Fs.of J (liveW a Γ.Dead) ⟶ Fs.of J b),
      J.cls h = DClass.mk Υ → J.projM.map h = g →
      ∀ j < Υ.dom.length, ∃ k : ℕ, Υ.toAGraph.HasPath (.edge j) (.edge k)) := by
  obtain ⟨n, m, Γ₀, hΓ₀, hΓΓ₀⟩ := lemma_4_4_exists_minimal (DClass.mk Γ)
  obtain ⟨hdw, hcw, -⟩ := lemma_4_3 hΓΓ₀
  have hdead : Γ.Dead = Γ₀.Dead := funext fun j => propext (lemma_4_5_dead hΓΓ₀ j)
  let f₀ : Fs.of J a ⟶ Fs.of J b :=
    J.hom ⟨DClass.mk Γ₀, by rw [DClass.dom_mk, ← hdw, ← DClass.dom_mk, ← hf]; exact J.cls_dom f,
      by rw [DClass.cod_mk, ← hcw, ← DClass.cod_mk, ← hf]; exact J.cls_cod f⟩
  have hff₀ : J.projM.map f = J.projM.map f₀ := by
    rw [quotProj_map_eq_iff, hf]
    exact hΓΓ₀
  obtain ⟨g₀, hg₀, hmore⟩ := J.lemma_4_5_minimal hΓ₀ f₀ rfl
  refine ⟨fun j hj => lemma_4_5_path Γ hj, fun Υ h j => lemma_4_5_dead h j, ?_, ?_⟩
  · rw [hdead]
    refine ⟨g₀, (J.isFactor_congr hff₀ _ _).2 hg₀, fun g hg => ?_⟩
    replace hg : J.IsFactor f Γ₀.Dead g := hg
    rw [J.isFactor_congr hff₀] at hg
    exact J.lemma_4_5_unique Γ₀.Dead _ _ (hg.symm.trans hg₀)
  · rw [hdead]
    intro g hg N' E' _ _ Υ h hh hhg j hj
    rw [J.isFactor_congr hff₀] at hg
    have hgg : g = g₀ := J.lemma_4_5_unique Γ₀.Dead _ _ (hg.symm.trans hg₀)
    exact (lemma_4_5_path Υ hj).1 (hmore Υ h hh (hhg.trans hgg) j)

end General

end JoyalStreet

end FreeMarkov
