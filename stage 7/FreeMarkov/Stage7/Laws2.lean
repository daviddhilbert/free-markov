/-
Free Markov categories, Stage 7: the laws of `F_s(G)` on classes, continued: the interchange
law, the naturality of the symmetry and the hexagon.  No cited result is used.
-/
module

public import FreeMarkov.Stage7.Laws

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

namespace PEmb

variable {NX : Type u₇} {EX : Type u₈} {X : Diagram G NX EX}

theorem idD_ιE_mem (a : FreeMonoid S) (l : List EX) (hl : l.Nodup)
    (hv : l.map X.val.v₀ = FreeMonoid.toList a) (d) : (PEmb.idD a l hl hv).ιE d ∈ l :=
  List.getElem_mem _

theorem braidD_ιE_mem (a b : FreeMonoid S) (l₁ l₂ : List EX) (hl : (l₁ ++ l₂).Nodup)
    (hv₁ : l₁.map X.val.v₀ = FreeMonoid.toList a) (hv₂ : l₂.map X.val.v₀ = FreeMonoid.toList b)
    (d) : (PEmb.braidD a b l₁ l₂ hl hv₁ hv₂).ιE d ∈ l₁ ++ l₂ := by
  rcases d with i | j
  · exact List.mem_append_left _ (List.getElem_mem _)
  · exact List.mem_append_right _ (List.getElem_mem _)

end PEmb

theorem map_append_split {α β γ : Type*} {l₁ : List α} {l₂ : List β} {f : α → γ} {g : β → γ}
    {A B : List γ} (h : l₁.map f ++ l₂.map g = A ++ B) (hl : l₁.length = A.length) :
    l₁.map f = A ∧ l₂.map g = B :=
  List.append_inj h (by rw [List.length_map, hl])

end Diagram

namespace DClass

open Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-! ### The interchange law -/

section Interchange

variable {N₁ : Type u₁} {E₁ : Type u₂} {N₂ : Type u₃} {E₂ : Type u₄} {N₃ : Type u₅} {E₃ : Type u₆}
  {N₄ : Type u₇} {E₄ : Type u₈} [Finite N₁] [Finite E₁] [Finite N₂] [Finite E₂] [Finite N₃]
  [Finite E₃] [Finite N₄] [Finite E₄]

theorem mk_interchange (Γ : Diagram G N₁ E₁) (Γ' : Diagram G N₂ E₂) (Δ : Diagram G N₃ E₃)
    (Δ' : Diagram G N₄ E₄) (h₁ : Γ.codWord = Γ'.domWord) (h₂ : Δ.codWord = Δ'.domWord)
    (h : (Γ.tensor Δ).codWord = (Γ'.tensor Δ').domWord) :
    mk ((Γ.glue Γ' h₁).tensor (Δ.glue Δ' h₂)) = mk ((Γ.tensor Δ).glue (Γ'.tensor Δ') h) := by
  set X := (Γ.tensor Δ).glue (Γ'.tensor Δ') h
  let eΓ : PEmb Γ X := (PEmb.tensorL Γ Δ).comp (PEmb.glueL _ _ h)
  let eΓ' : PEmb Γ' X := (PEmb.tensorL Γ' Δ').comp (PEmb.glueR _ _ h)
  let eΔ : PEmb Δ X := (PEmb.tensorR Γ Δ).comp (PEmb.glueL _ _ h)
  let eΔ' : PEmb Δ' X := (PEmb.tensorR Γ' Δ').comp (PEmb.glueR _ _ h)
  have key := PEmb.dom_map_gIn (Γ.tensor Δ) (Γ'.tensor Δ') h
  simp only [Diagram.tensor, AGraph.tensor, List.map_append, List.map_map] at key
  obtain ⟨k₁, k₂⟩ := map_append_split key (by
    rw [List.length_map]; exact (cod_length_eq_dom_length h₁).symm)
  have hc₁ : Γ.cod.map eΓ.ιE = Γ'.dom.map eΓ'.ιE := k₁.symm
  have hc₂ : Δ.cod.map eΔ.ιE = Δ'.dom.map eΔ'.ιE := k₂.symm
  have hdom₁ : ∀ d, Γ.src d = none → ∀ z, X.src (eΓ.ιE d) ≠ some (eΓ'.ιN z) := by
    intro d hd z
    simp [X, eΓ, eΓ', PEmb.comp, PEmb.glueL, PEmb.glueR, PEmb.tensorL, Diagram.glue, AGraph.glue,
      Diagram.tensor, AGraph.tensor, PGraph.tensor, hd]
  have hdom₂ : ∀ d, Δ.src d = none → ∀ z, X.src (eΔ.ιE d) ≠ some (eΔ'.ιN z) := by
    intro d hd z
    simp [X, eΔ, eΔ', PEmb.comp, PEmb.glueL, PEmb.glueR, PEmb.tensorR, Diagram.glue, AGraph.glue,
      Diagram.tensor, AGraph.tensor, PGraph.tensor, hd]
  let g₁ := PEmb.glueS eΓ eΓ' h₁ hc₁ (fun _ _ => Sum.inl_ne_inr) hdom₁
  let g₂ := PEmb.glueS eΔ eΔ' h₂ hc₂ (fun _ _ => Sum.inl_ne_inr) hdom₂
  have hN : ∀ z z', g₁.ιN z ≠ g₂.ιN z' := by
    rintro (z | z) (z' | z') <;> simp [g₁, g₂, eΓ, eΓ', eΔ, eΔ', PEmb.glueS, PEmb.glue,
      PEmb.comp, PEmb.glueL, PEmb.glueR, PEmb.tensorL, PEmb.tensorR]
  have hE : ∀ d d', g₁.ιE d ≠ g₂.ιE d' := by
    have inner : ∀ e : E₂ ⊕ E₄, (Γ'.tensor Δ').src e ≠ none →
        ∃ b, PEmb.gIn h e = Sum.inr b := fun e he => ⟨_, PGraph.glueIn_of_ne_none _ he⟩
    rintro (d | d) (d' | d') hdd
    · simp [g₁, g₂, eΓ, eΔ, PEmb.glueS, PEmb.glue, PEmb.comp, PEmb.glueL, PEmb.tensorL,
        PEmb.tensorR] at hdd
    · obtain ⟨b, hb⟩ := inner (Sum.inr d'.1) (by
        simpa [Diagram.tensor, AGraph.tensor, PGraph.tensor] using d'.2)
      simp only [g₁, g₂, eΓ, eΔ', PEmb.glueS, PEmb.glue, PEmb.comp, PEmb.glueL, PEmb.glueR,
        PEmb.tensorL, PEmb.tensorR, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, hb] at hdd
      exact Sum.inl_ne_inr hdd
    · obtain ⟨b, hb⟩ := inner (Sum.inl d.1) (by
        simpa [Diagram.tensor, AGraph.tensor, PGraph.tensor] using d.2)
      simp only [g₁, g₂, eΓ', eΔ, PEmb.glueS, PEmb.glue, PEmb.comp, PEmb.glueL, PEmb.glueR,
        PEmb.tensorL, PEmb.tensorR, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, hb] at hdd
      exact Sum.inr_ne_inl hdd
    · simp only [g₁, g₂, eΓ', eΔ', PEmb.glueS, PEmb.glue, PEmb.comp, PEmb.glueR,
        PEmb.tensorL, PEmb.tensorR, Sum.elim_inr, Function.comp_apply] at hdd
      exact Sum.inl_ne_inr (PGraph.glueIn_injective _ hdd)
  let e := PEmb.tensor g₁ g₂ hN hE
  refine e.mk_eq ?_ ?_ ?_ ?_
  · simp only [Nat.card_sum]; omega
  · have c₁ := card_glue_edges Γ Γ' h₁
    have c₂ := card_glue_edges Δ Δ' h₂
    have c₃ := card_glue_edges (Γ.tensor Δ) (Γ'.tensor Δ') h
    have c₄ : (Γ'.tensor Δ').dom.length = Γ'.dom.length + Δ'.dom.length := by
      simp [Diagram.tensor, AGraph.tensor]
    simp only [Nat.card_sum] at c₁ c₂ c₃ ⊢
    omega
  · refine (PEmb.tensor_dom g₁ g₂ hN hE).trans ?_
    have d₁ : (Γ.glue Γ' h₁).dom.map g₁.ιE = Γ.dom.map eΓ.ιE := PEmb.glueS_dom _ _ _ _ _ _
    have d₂ : (Δ.glue Δ' h₂).dom.map g₂.ιE = Δ.dom.map eΔ.ιE := PEmb.glueS_dom _ _ _ _ _ _
    simp only [X, Diagram.glue,
      AGraph.glue, Diagram.tensor, AGraph.tensor, List.map_append, List.map_map]
    rfl
  · refine (PEmb.tensor_cod g₁ g₂ hN hE).trans ?_
    have d₁ : (Γ.glue Γ' h₁).cod.map g₁.ιE = Γ'.cod.map eΓ'.ιE := PEmb.glueS_cod _ _ _ _ _ _
    have d₂ : (Δ.glue Δ' h₂).cod.map g₂.ιE = Δ'.cod.map eΔ'.ιE := PEmb.glueS_cod _ _ _ _ _ _
    rw [d₁, d₂]
    simp only [X, eΓ', eΔ', PEmb.comp, PEmb.glueR, PEmb.tensorL, PEmb.tensorR,
      Diagram.glue, AGraph.glue, Diagram.tensor, AGraph.tensor, List.map_append, List.map_map]
    rfl

end Interchange

/-! ### Naturality of the symmetry -/

section Natural

variable {N₁ : Type u₁} {E₁ : Type u₂} {N₂ : Type u₃} {E₂ : Type u₄} [Finite N₁] [Finite E₁]
  [Finite N₂] [Finite E₂]

theorem mk_braid_natural (Γ : Diagram G N₁ E₁) (Δ : Diagram G N₂ E₂)
    (h : (Γ.tensor Δ).codWord = (braidD G Γ.codWord Δ.codWord).domWord)
    (h' : (braidD G Γ.domWord Δ.domWord).codWord = (Δ.tensor Γ).domWord) :
    mk ((Γ.tensor Δ).glue (braidD G Γ.codWord Δ.codWord) h) =
      mk ((braidD G Γ.domWord Δ.domWord).glue (Δ.tensor Γ) h') := by
  set X := (braidD G Γ.domWord Δ.domWord).glue (Δ.tensor Γ) h'
  let eΓ : PEmb Γ X := (PEmb.tensorR Δ Γ).comp (PEmb.glueR _ _ h')
  let eΔ : PEmb Δ X := (PEmb.tensorL Δ Γ).comp (PEmb.glueR _ _ h')
  have hE : ∀ d d', eΓ.ιE d ≠ eΔ.ιE d' := fun d d' hdd =>
    Sum.inr_ne_inl (PGraph.glueIn_injective _ hdd)
  let inner := PEmb.tensor eΓ eΔ (fun _ _ => by simp [eΓ, eΔ, PEmb.comp, PEmb.glueR,
    PEmb.tensorL, PEmb.tensorR]) hE
  have kc : (Γ.tensor Δ).cod.map inner.ιE = Γ.cod.map eΓ.ιE ++ Δ.cod.map eΔ.ιE :=
    PEmb.tensor_cod _ _ _ _
  have hl : (Γ.cod.map eΓ.ιE ++ Δ.cod.map eΔ.ιE).Nodup := by
    rw [← kc]; exact (Γ.tensor Δ).cod_nodup.map inner.injE
  have hv₁ : (Γ.cod.map eΓ.ιE).map X.val.v₀ = FreeMonoid.toList Γ.codWord := by
    rw [List.map_map]
    exact (List.map_congr_left fun d _ => eΓ.v₀ d).trans (toList_eq_map_v₀_cod Γ rfl)
  have hv₂ : (Δ.cod.map eΔ.ιE).map X.val.v₀ = FreeMonoid.toList Δ.codWord := by
    rw [List.map_map]
    exact (List.map_congr_left fun d _ => eΔ.v₀ d).trans (toList_eq_map_v₀_cod Δ rfl)
  let eB := PEmb.braidD Γ.codWord Δ.codWord _ _ hl hv₁ hv₂
  have kB₁ : (braidD G Γ.codWord Δ.codWord).dom.map eB.ιE =
      Γ.cod.map eΓ.ιE ++ Δ.cod.map eΔ.ιE := PEmb.braidD_dom _ _ _ _ _ _ _
  have kB₂ : (braidD G Γ.codWord Δ.codWord).cod.map eB.ιE =
      Δ.cod.map eΔ.ιE ++ Γ.cod.map eΓ.ιE := PEmb.braidD_cod _ _ _ _ _ _ _
  let e := PEmb.glueS inner eB h (kc.trans kB₁.symm) (fun _ z => z.elim) (fun _ _ z => z.elim)
  refine e.mk_eq ?_ ?_ ?_ ?_
  · simp only [Nat.card_sum, Nat.card_of_isEmpty]; omega
  · have c₁ := card_glue_edges (Γ.tensor Δ) (braidD G Γ.codWord Δ.codWord) h
    have c₂ := card_glue_edges (braidD G Γ.domWord Δ.domWord) (Δ.tensor Γ) h'
    have c₃ : (braidD G Γ.codWord Δ.codWord).dom.length = wlen Γ.codWord + wlen Δ.codWord := by
      simp [braidD, nodeFree, braidDom]
    have c₄ : (Δ.tensor Γ).dom.length = wlen Δ.domWord + wlen Γ.domWord := by
      simp [Diagram.tensor, AGraph.tensor, dom_length]
    have c₅ := Γ.cod_length
    have c₆ := Δ.cod_length
    simp only [Nat.card_sum, Nat.card_fin] at c₁ c₂ ⊢
    omega
  · refine (PEmb.glueS_dom _ _ _ _ _ _).trans ?_
    have kd : (Γ.tensor Δ).dom.map inner.ιE = Γ.dom.map eΓ.ιE ++ Δ.dom.map eΔ.ιE :=
      PEmb.tensor_dom _ _ _ _
    rw [kd]
    have key := PEmb.dom_map_gIn (braidD G Γ.domWord Δ.domWord) (Δ.tensor Γ) h'
    have bc : (braidD G Γ.domWord Δ.domWord).cod = braidCod Γ.domWord Δ.domWord := rfl
    have bd : (braidD G Γ.domWord Δ.domWord).dom = braidDom Γ.domWord Δ.domWord := rfl
    rw [bc] at key
    simp only [Diagram.tensor, AGraph.tensor, braidCod, List.map_append, List.map_map] at key
    obtain ⟨k₁, k₂⟩ := map_append_split key (by simp [dom_length])
    have ed : X.dom = (braidDom Γ.domWord Δ.domWord).map Sum.inl := by
      simp only [X, Diagram.glue, AGraph.glue, bd]
    have k₁' : Δ.dom.map eΔ.ιE = _ := k₁
    have k₂' : Γ.dom.map eΓ.ιE = _ := k₂
    rw [ed, k₁', k₂']
    simp only [braidDom, List.map_append, List.map_map]
    rfl
  · refine (PEmb.glueS_cod _ _ _ _ _ _).trans ?_
    rw [kB₂]
    simp only [X, eΓ, eΔ, PEmb.comp, PEmb.glueR, PEmb.tensorL, PEmb.tensorR, Diagram.glue,
      AGraph.glue, Diagram.tensor, AGraph.tensor, List.map_append, List.map_map]
    rfl

end Natural

/-! ### The hexagon -/

theorem mk_hexagon (a b c : FreeMonoid S)
    (h : ((braidD G a b).tensor (idD G c)).codWord = ((idD G b).tensor (braidD G a c)).domWord) :
    mk (((braidD G a b).tensor (idD G c)).glue ((idD G b).tensor (braidD G a c)) h) =
      mk (braidD G a (b * c)) := by
  set X := braidD G a (b * c)
  let A : List (Fin (wlen a) ⊕ Fin (wlen (b * c))) := (List.finRange _).map Sum.inl
  let B : List (Fin (wlen a) ⊕ Fin (wlen (b * c))) := (posL b c).map Sum.inr
  let C : List (Fin (wlen a) ⊕ Fin (wlen (b * c))) := (posR b c).map Sum.inr
  have hABC : (A ++ (B ++ C)).Nodup := by
    have := X.dom_nodup
    simp only [X, braidD, nodeFree, braidDom] at this
    rwa [← posL_append_posR b c, List.map_append] at this
  have hvA : A.map X.val.v₀ = FreeMonoid.toList a := by
    simp only [A, X, braidD, nodeFree, List.map_map]
    exact map_letters_finRange a
  have hvB : B.map X.val.v₀ = FreeMonoid.toList b := by
    simp only [B, X, braidD, nodeFree, List.map_map]
    exact posL_map b c
  have hvC : C.map X.val.v₀ = FreeMonoid.toList c := by
    simp only [C, X, braidD, nodeFree, List.map_map]
    exact posR_map b c
  have n₁ : (A ++ B).Nodup := hABC.sublist (by simp)
  have n₂ : (A ++ C).Nodup := hABC.sublist (by simp)
  have nB : B.Nodup := hABC.sublist (by simp)
  have nC : C.Nodup := hABC.sublist (by simp)
  have dABC : ∀ x ∈ A ++ B, ∀ y ∈ C, x ≠ y := by
    have : ((A ++ B) ++ C).Nodup := by rwa [List.append_assoc]
    exact (List.nodup_append.1 this).2.2
  have dBAC : ∀ x ∈ B, ∀ y ∈ A ++ C, x ≠ y := by
    have : (B ++ (A ++ C)).Nodup := by
      refine (List.perm_append_comm_assoc _ _ _).nodup_iff.1 ?_
      simpa [List.append_assoc] using hABC
    exact (List.nodup_append.1 this).2.2
  let e₁ := PEmb.tensor (PEmb.braidD (X := X) a b A B n₁ hvA hvB) (PEmb.idD c C nC hvC)
    (fun _ z => z.elim) (fun d d' => dABC _ (PEmb.braidD_ιE_mem _ _ _ _ _ _ _ d) _
      (PEmb.idD_ιE_mem _ _ _ _ d'))
  let e₂ := PEmb.tensor (PEmb.idD (X := X) b B nB hvB) (PEmb.braidD a c A C n₂ hvA hvC)
    (fun z => z.elim) (fun d d' => dBAC _ (PEmb.idD_ιE_mem _ _ _ _ d) _
      (PEmb.braidD_ιE_mem _ _ _ _ _ _ _ d'))
  have k₁ : ((braidD G a b).tensor (idD G c)).cod.map e₁.ιE = (B ++ A) ++ C := by
    refine (PEmb.tensor_cod _ _ _ _).trans ?_
    rw [PEmb.braidD_cod, PEmb.idD_cod]
  have k₂ : ((idD G b).tensor (braidD G a c)).dom.map e₂.ιE = B ++ (A ++ C) := by
    refine (PEmb.tensor_dom _ _ _ _).trans ?_
    rw [PEmb.idD_dom, PEmb.braidD_dom]
  let e := PEmb.glueS e₁ e₂ h (by rw [k₁, k₂, List.append_assoc])
    (fun _ z => by rcases z with z | z <;> exact z.elim)
    (fun _ _ z => by rcases z with z | z <;> exact z.elim)
  refine e.mk_eq ?_ ?_ ?_ ?_
  · simp
  · have c₁ := card_glue_edges ((braidD G a b).tensor (idD G c))
      ((idD G b).tensor (braidD G a c)) h
    have c₂ : ((idD G b).tensor (braidD G a c)).dom.length = wlen b + (wlen a + wlen c) := by
      simp [Diagram.tensor, AGraph.tensor, idD, braidD, nodeFree, braidDom]
    simp only [Nat.card_sum, Nat.card_fin] at c₁ ⊢
    rw [wlen_mul]
    omega
  · refine (PEmb.glueS_dom _ _ _ _ _ _).trans ?_
    refine (PEmb.tensor_dom _ _ _ _).trans ?_
    rw [PEmb.braidD_dom, PEmb.idD_dom]
    simp only [X, braidD, nodeFree, braidDom, A, B, C, List.append_assoc, ← List.map_append,
      posL_append_posR]
  · refine (PEmb.glueS_cod _ _ _ _ _ _).trans ?_
    refine (PEmb.tensor_cod _ _ _ _).trans ?_
    rw [PEmb.idD_cod, PEmb.braidD_cod]
    simp only [X, braidD, nodeFree, braidCod, A, B, C, ← List.append_assoc, ← List.map_append,
      posL_append_posR]

end DClass

end FreeMarkov
