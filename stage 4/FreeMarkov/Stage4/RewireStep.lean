/-
Free Markov categories, Stage 4: the swap and the rotation are surgeries with (4.3) and (4.1).

* `canonProj_of_rewire`: a diagram `Y` on the nodes and edges of `X`, which agrees with `X`
  outside an embedded `Ω` and contains an embedded `Λ` on the same nodes, matching the domain and
  codomain of `Ω` through `α`, `β`, has the canonical description of the result of the surgery.
* `tStep_swap`, `tStep_rotate`; the set `T_C` of the templates (4.1), (4.3) (`congTemplates`).
-/
module

public import FreeMarkov.Stage4.Rewire

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆

namespace FreeMarkov

open Relation

namespace FreeDDGraphMonoid

variable {S : Type w} (G : FreeDDGraphMonoid.{w, v} S)

/-- The templates (4.1), (4.3) before reversal. -/
def congBase : Set (Template.{0} G.toFreeGraphMonoid) := Set.range G.coassT ∪ Set.range G.cocommT

/-- **The templates of Markov congruence**: (4.1), (4.3), their reverses and the empty template
("they become isomorphic upon surgeries with the templates (4.1), (4.3)"). -/
def congTemplates : Set (Template.{0} G.toFreeGraphMonoid) :=
  insert (Template.empty G.toFreeGraphMonoid) (G.congBase ∪ Template.symm '' G.congBase)

theorem congTemplates_isSymmetric : Template.IsSymmetric G.congTemplates where
  empty_mem := Set.mem_insert _ _
  symm_mem τ hτ := by
    rcases hτ with rfl | hτ | ⟨σ, hσ, rfl⟩
    · exact Set.mem_insert _ _
    · exact Or.inr (Or.inr ⟨τ, hτ, rfl⟩)
    · rw [Template.symm_symm]
      exact Or.inr (Or.inl hσ)

theorem congTemplates_subset : G.congTemplates ⊆ G.markovTemplates := by
  have hb : G.congBase ⊆ G.baseMarkovTemplates := by
    rintro τ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩)))
    · exact Or.inl (Or.inr ⟨a, rfl⟩)
  rintro τ (rfl | hτ | ⟨σ, hσ, rfl⟩)
  · exact Set.mem_insert _ _
  · exact Or.inr (Or.inl (hb hτ))
  · exact Or.inr (Or.inr ⟨σ, hb hσ, rfl⟩)

theorem coassT_mem_cong (a : S) : G.coassT a ∈ G.congTemplates :=
  Or.inr (Or.inl (Or.inl ⟨a, rfl⟩))

theorem cocommT_mem_cong (a : S) : G.cocommT a ∈ G.congTemplates :=
  Or.inr (Or.inl (Or.inr ⟨a, rfl⟩))

end FreeDDGraphMonoid

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S}

theorem PEmb.exists_inner_iff {N : Type u₁} {E : Type u₂} {NX : Type u₃} {EX : Type u₄}
    {D : Diagram G.toFreeGraphMonoid N E} {X : Diagram G.toFreeGraphMonoid NX EX} (e : PEmb D X)
    (f : EX) : (∃ δ, D.src δ ≠ none ∧ e.ιE δ = f) ↔ ∃ z, X.src f = some (e.ιN z) := by
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hδ
    exact ⟨z, e.src_some hz⟩
  · rintro ⟨z, hz⟩
    rw [← X.mem_outs, e.outs] at hz
    obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 hz
    exact ⟨δ, by rw [(D.mem_outs z δ).1 hδ]; exact Option.some_ne_none _, rfl⟩

section Rewire

variable {N : Type u₁} {E : Type u₂} {NΩ : Type u₃} {EΩ : Type u₄} {NΛ : Type u₅} {EΛ : Type u₆}
  {X Y : Diagram G.toFreeGraphMonoid N E} {Ω : PDiagram G.toFreeGraphMonoid NΩ EΩ}
  {Λ : PDiagram G.toFreeGraphMonoid NΛ EΛ} {ιN : NΩ → N} {ιE : EΩ → E} {κN : NΛ → N} {κE : EΛ → E}
  {α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}} {β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}}

open scoped Classical in
/-- The map of nodes of a rewiring. -/
noncomputable def rwPN (κN : NΛ → N) (y : N) : N ⊕ NΛ :=
  if h : ∃ z, κN z = y then .inr h.choose else .inl y

open scoped Classical in
/-- The map of edges of a rewiring. -/
noncomputable def rwPE (Λ : PDiagram G.toFreeGraphMonoid NΛ EΛ) (κE : EΛ → E) (e : E) :
    E ⊕ Λ.InnerSrc :=
  if h : ∃ l, Λ.src l ≠ none ∧ κE l = e then .inr ⟨h.choose, h.choose_spec.1⟩ else .inl e

theorem rwPN_out {y : N} (hy : ∀ z, κN z ≠ y) : rwPN κN y = .inl y := by
  classical
  simp only [rwPN, dite_eq_right (not_exists.2 hy)]

theorem rwPE_out {e : E} (he : ∀ l, Λ.src l ≠ none → κE l ≠ e) : rwPE Λ κE e = .inl e := by
  classical
  simp only [rwPE]
  rw [dite_eq_right]
  rintro ⟨l, hl, hle⟩
  exact he l hl hle

open scoped Classical in
/-- **Recognition of a rewiring as a surgery.** -/
noncomputable def canonProj_of_rewire (eΩ : Emb X Ω ιN ιE) (eΛ : Emb Y Λ κN κE)
    (hN : ∀ x, (∃ z, ιN z = x) ↔ ∃ z, κN z = x)
    (hinner : ∀ e, (∃ δ, Ω.src δ ≠ none ∧ ιE δ = e) ↔ ∃ l, Λ.src l ≠ none ∧ κE l = e)
    (hα : ∀ l : {l // Λ.IsDom l}, κE l.1 = ιE (α l).1)
    (hβ : ∀ l : {l // Λ.IsCod l}, κE l.1 = ιE (β l).1)
    (hins : Y.ins = X.ins) (houts : ∀ x, (∀ z, ιN z ≠ x) → Y.outs x = X.outs x)
    (hdom : Y.dom = X.dom) (hcod : Y.cod = X.cod) (hv₀ : Y.val.v₀ = X.val.v₀)
    (hv₁ : ∀ x, (∀ z, ιN z ≠ x) → Y.val.v₁ x = X.val.v₁ x) :
    CanonProj X Ω ιN ιE α β Y := by
  -- the maps
  let pN : N → N ⊕ NΛ := rwPN κN
  let pE : E → E ⊕ Λ.InnerSrc := rwPE Λ κE
  have pN_κ : ∀ z, pN (κN z) = .inr z := by
    intro z
    have h : ∃ z', κN z' = κN z := ⟨z, rfl⟩
    simp only [pN, rwPN, dite_eq_left h]
    exact congrArg Sum.inr (eΛ.injN h.choose_spec)
  have pN_out : ∀ y, (∀ z, κN z ≠ y) → pN y = .inl y := fun y hy => rwPN_out hy
  have pE_κ : ∀ (l : EΛ) (hl : Λ.src l ≠ none), pE (κE l) = .inr ⟨l, hl⟩ := by
    intro l hl
    have h : ∃ l', Λ.src l' ≠ none ∧ κE l' = κE l := ⟨l, hl, rfl⟩
    simp only [pE, rwPE, dite_eq_left h]
    exact congrArg Sum.inr (Subtype.ext (eΛ.injE h.choose_spec.2))
  have pE_out : ∀ e, (∀ l, Λ.src l ≠ none → κE l ≠ e) → pE e = .inl e := fun e he => rwPE_out he
  -- the edges of `Λ` go to their canonical images
  have pE_canonG : ∀ l, pE (κE l) = canonG ιE α l := by
    intro l
    by_cases hl : Λ.src l = none
    · rw [canonG_of_src_eq_none ιE α hl, pE_out _ (fun l' hl' h => by
        rw [eΛ.injE h] at hl'; exact hl' hl), hα ⟨l, hl⟩]
    · rw [canonG_of_src_ne_none ιE α hl, pE_κ l hl]
  -- an edge of `X` not ending in `Ω`
  have pE_canonF : ∀ e, (∀ z, X.tgt e ≠ some (ιN z)) → pE e = canonF ιE α β e := by
    intro e he
    by_cases hc : ∃ c : {c // Ω.IsCod c}, ιE c.1 = e
    · obtain ⟨c, rfl⟩ := hc
      rw [canonF_of_cod ιE α β eΩ.injE c, ← pE_canonG]
      congr 1
      rw [hβ, Equiv.apply_symm_apply]
    · push Not at hc
      rw [canonF_of_not ιE α β hc]
      refine pE_out e fun l hl hle => ?_
      obtain ⟨δ, hδ, hδe⟩ := (hinner e).2 ⟨l, hl, hle⟩
      cases ht : Ω.tgt δ with
      | none => exact hc ⟨δ, ht⟩ hδe
      | some z => exact he z (hδe ▸ eΩ.tgt_some ht)
  have hκ_out : ∀ x, (∀ z, ιN z ≠ x) → ∀ z, κN z ≠ x := fun x hx z hz =>
    (not_exists.2 hx) ((hN x).2 ⟨z, hz⟩)
  exact
  { pN := pN
    pE := pE
    pN_inj := by
      intro y y' h
      by_cases hy : ∃ z, κN z = y
      · obtain ⟨z, rfl⟩ := hy
        by_cases hy' : ∃ z, κN z = y'
        · obtain ⟨z', rfl⟩ := hy'
          rw [pN_κ, pN_κ, Sum.inr.injEq] at h
          rw [h]
        · rw [pN_κ, pN_out y' (not_exists.1 hy')] at h; cases h
      · by_cases hy' : ∃ z, κN z = y'
        · obtain ⟨z', rfl⟩ := hy'
          rw [pN_κ, pN_out y (not_exists.1 hy)] at h; cases h
        · rw [pN_out y (not_exists.1 hy), pN_out y' (not_exists.1 hy'), Sum.inl.injEq] at h
          exact h
    pE_inj := by
      intro e e' h
      by_cases he : ∃ l, Λ.src l ≠ none ∧ κE l = e
      · obtain ⟨l, hl, rfl⟩ := he
        by_cases he' : ∃ l, Λ.src l ≠ none ∧ κE l = e'
        · obtain ⟨l', hl', rfl⟩ := he'
          rw [pE_κ l hl, pE_κ l' hl', Sum.inr.injEq, Subtype.mk.injEq] at h
          rw [h]
        · rw [pE_κ l hl, pE_out e' (fun l' hl' h' => he' ⟨l', hl', h'⟩)] at h; cases h
      · by_cases he' : ∃ l, Λ.src l ≠ none ∧ κE l = e'
        · obtain ⟨l', hl', rfl⟩ := he'
          rw [pE_κ l' hl', pE_out e (fun l hl h' => he ⟨l, hl, h'⟩)] at h; cases h
        · rw [pE_out e (fun l hl h' => he ⟨l, hl, h'⟩), pE_out e' (fun l hl h' => he' ⟨l, hl, h'⟩),
            Sum.inl.injEq] at h
          exact h
    pN_range := by
      rintro (x | z)
      · constructor
        · rintro ⟨y, hy⟩ z hz
          by_cases h : ∃ z', κN z' = y
          · obtain ⟨z', rfl⟩ := h
            rw [pN_κ] at hy; cases hy
          · rw [pN_out y (not_exists.1 h), Sum.inl.injEq] at hy
            subst hy
            exact h ((hN _).1 ⟨z, hz⟩)
        · intro hx
          exact ⟨x, pN_out x (hκ_out x hx)⟩
      · exact iff_of_true ⟨κN z, pN_κ z⟩ trivial
    pE_range := by
      rintro (f | ⟨l, hl⟩)
      · constructor
        · rintro ⟨e, he⟩ δ hδ hδf
          by_cases h : ∃ l, Λ.src l ≠ none ∧ κE l = e
          · obtain ⟨l, hl, rfl⟩ := h
            rw [pE_κ l hl] at he; cases he
          · rw [pE_out e (fun l hl h' => h ⟨l, hl, h'⟩), Sum.inl.injEq] at he
            subst he
            exact h ((hinner _).1 ⟨δ, hδ, hδf⟩)
        · intro hf
          refine ⟨f, pE_out f fun l hl hlf => ?_⟩
          obtain ⟨δ, hδ, hδf⟩ := (hinner f).2 ⟨l, hl, hlf⟩
          exact hf δ hδ hδf
      · exact iff_of_true ⟨κE l, pE_κ l hl⟩ trivial
    ins := by
      intro y
      by_cases h : ∃ z, κN z = y
      · obtain ⟨z, rfl⟩ := h
        rw [pN_κ, eΛ.ins, List.map_map]
        exact List.map_congr_left fun l _ => pE_canonG l
      · rw [pN_out y (not_exists.1 h), hins]
        have hy : ∀ z, ιN z ≠ y := fun z hz => h ((hN y).1 ⟨z, hz⟩)
        exact List.map_congr_left fun e he => pE_canonF e fun z hz => by
          rw [(X.mem_ins y e).1 he, Option.some.injEq] at hz
          exact hy z hz.symm
    outs := by
      intro y
      by_cases h : ∃ z, κN z = y
      · obtain ⟨z, rfl⟩ := h
        rw [pN_κ, eΛ.outs, List.map_map]
        exact List.map_congr_left fun l _ => pE_canonG l
      · have hy : ∀ z, ιN z ≠ y := fun z hz => h ((hN y).1 ⟨z, hz⟩)
        rw [pN_out y (not_exists.1 h)]
        show (Y.outs y).map pE = (X.outs y).map Sum.inl
        rw [houts y hy]
        refine List.map_congr_left fun e he => pE_out e fun l hl hle => ?_
        obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hl
        have h₁ := eΛ.src_some hz
        rw [hle] at h₁
        have h₂ : Y.src e = some y := (Y.mem_outs y e).1 (by rw [houts y hy]; exact he)
        rw [h₂, Option.some.injEq] at h₁
        exact h ⟨z, h₁.symm⟩
    dom := by
      rw [hdom]
      refine List.map_congr_left fun e he => pE_out e fun l hl hle => ?_
      obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hl
      have h₁ := eΛ.src_some hz
      rw [hle, (Y.mem_dom e).1 (by rw [hdom]; exact he)] at h₁
      cases h₁
    cod := by
      rw [hcod]
      refine List.map_congr_left fun e he => pE_canonF e fun z hz => ?_
      rw [(X.mem_cod e).1 he] at hz
      cases hz
    v₀ := by
      intro e
      by_cases h : ∃ l, Λ.src l ≠ none ∧ κE l = e
      · obtain ⟨l, hl, rfl⟩ := h
        rw [pE_κ l hl]
        exact eΛ.v₀ l
      · rw [pE_out e (fun l hl h' => h ⟨l, hl, h'⟩), hv₀]
        rfl
    v₁ := by
      intro y
      by_cases h : ∃ z, κN z = y
      · obtain ⟨z, rfl⟩ := h
        rw [pN_κ]
        exact eΛ.v₁ z
      · rw [pN_out y (not_exists.1 h)]
        exact hv₁ y fun z hz => h ((hN y).1 ⟨z, hz⟩) }

open scoped Classical in
theorem rwPE_canonG (eΛ : Emb Y Λ κN κE) (hα : ∀ l : {l // Λ.IsDom l}, κE l.1 = ιE (α l).1)
    (l : EΛ) : rwPE Λ κE (κE l) = canonG ιE α l := by
  by_cases hl : Λ.src l = none
  · rw [canonG_of_src_eq_none ιE α hl, rwPE_out (fun l' hl' h => by
      rw [eΛ.injE h] at hl'; exact hl' hl), hα ⟨l, hl⟩]
  · rw [canonG_of_src_ne_none ιE α hl]
    have h : ∃ l', Λ.src l' ≠ none ∧ κE l' = κE l := ⟨l, hl, rfl⟩
    simp only [rwPE, dite_eq_left h]
    exact congrArg Sum.inr (Subtype.ext (eΛ.injE h.choose_spec.2))

theorem rwPE_canonF (eΩ : Emb X Ω ιN ιE) (eΛ : Emb Y Λ κN κE)
    (hinner : ∀ e, (∃ δ, Ω.src δ ≠ none ∧ ιE δ = e) ↔ ∃ l, Λ.src l ≠ none ∧ κE l = e)
    (hα : ∀ l : {l // Λ.IsDom l}, κE l.1 = ιE (α l).1)
    (hβ : ∀ l : {l // Λ.IsCod l}, κE l.1 = ιE (β l).1) (e : E)
    (he : ∀ z, X.tgt e ≠ some (ιN z)) : rwPE Λ κE e = canonF ιE α β e := by
  by_cases hc : ∃ c : {c // Ω.IsCod c}, ιE c.1 = e
  · obtain ⟨c, rfl⟩ := hc
    rw [canonF_of_cod ιE α β eΩ.injE c, ← rwPE_canonG eΛ hα]
    congr 1
    rw [hβ, Equiv.apply_symm_apply]
  · push Not at hc
    rw [canonF_of_not ιE α β hc]
    refine rwPE_out fun l hl hle => ?_
    obtain ⟨δ, hδ, hδe⟩ := (hinner e).2 ⟨l, hl, hle⟩
    cases ht : Ω.tgt δ with
    | none => exact hc ⟨δ, ht⟩ hδe
    | some z => exact he z (hδe ▸ eΩ.tgt_some ht)

theorem rwPE_inl (eΩ : Emb X Ω ιN ιE)
    (hinner : ∀ e, (∃ δ, Ω.src δ ≠ none ∧ ιE δ = e) ↔ ∃ l, Λ.src l ≠ none ∧ κE l = e) (e : E)
    (he : ∀ z, X.src e ≠ some (ιN z)) : rwPE Λ κE e = .inl e := by
  refine rwPE_out fun l hl hle => ?_
  obtain ⟨δ, hδ, rfl⟩ := (hinner e).2 ⟨l, hl, hle⟩
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hδ
  exact he z (eΩ.src_some hz)

theorem rwPN_inl (hN : ∀ x, (∃ z, ιN z = x) ↔ ∃ z, κN z = x) (x : N) (hx : ∀ z, ιN z ≠ x) :
    rwPN κN x = .inl x :=
  rwPN_out fun z hz => (not_exists.2 hx) ((hN x).2 ⟨z, hz⟩)

theorem canonProj_of_rewire_pN (eΩ : Emb X Ω ιN ιE) (eΛ : Emb Y Λ κN κE)
    (hN : ∀ x, (∃ z, ιN z = x) ↔ ∃ z, κN z = x)
    (hinner : ∀ e, (∃ δ, Ω.src δ ≠ none ∧ ιE δ = e) ↔ ∃ l, Λ.src l ≠ none ∧ κE l = e)
    (hα : ∀ l : {l // Λ.IsDom l}, κE l.1 = ιE (α l).1)
    (hβ : ∀ l : {l // Λ.IsCod l}, κE l.1 = ιE (β l).1)
    (hins : Y.ins = X.ins) (houts : ∀ x, (∀ z, ιN z ≠ x) → Y.outs x = X.outs x)
    (hdom : Y.dom = X.dom) (hcod : Y.cod = X.cod) (hv₀ : Y.val.v₀ = X.val.v₀)
    (hv₁ : ∀ x, (∀ z, ιN z ≠ x) → Y.val.v₁ x = X.val.v₁ x) :
    (canonProj_of_rewire eΩ eΛ hN hinner hα hβ hins houts hdom hcod hv₀ hv₁).pN = rwPN κN := rfl

theorem canonProj_of_rewire_pE (eΩ : Emb X Ω ιN ιE) (eΛ : Emb Y Λ κN κE)
    (hN : ∀ x, (∃ z, ιN z = x) ↔ ∃ z, κN z = x)
    (hinner : ∀ e, (∃ δ, Ω.src δ ≠ none ∧ ιE δ = e) ↔ ∃ l, Λ.src l ≠ none ∧ κE l = e)
    (hα : ∀ l : {l // Λ.IsDom l}, κE l.1 = ιE (α l).1)
    (hβ : ∀ l : {l // Λ.IsCod l}, κE l.1 = ιE (β l).1)
    (hins : Y.ins = X.ins) (houts : ∀ x, (∀ z, ιN z ≠ x) → Y.outs x = X.outs x)
    (hdom : Y.dom = X.dom) (hcod : Y.cod = X.cod) (hv₀ : Y.val.v₀ = X.val.v₀)
    (hv₁ : ∀ x, (∀ z, ιN z ≠ x) → Y.val.v₁ x = X.val.v₁ x) :
    (canonProj_of_rewire eΩ eΛ hN hinner hα hβ hins houts hdom hcod hv₀ hv₁).pE = rwPE Λ κE := rfl

end Rewire

end Diagram

end FreeMarkov
