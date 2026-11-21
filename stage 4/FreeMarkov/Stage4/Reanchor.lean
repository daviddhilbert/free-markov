/-
Free Markov categories, Stage 4: tools for the third item of Lemma 4.5.

* `reanchor`: the same graph with the domain reordered; gluing a node-free diagram of a permutation
  on the left of `Θ` gives `Θ` with its domain reordered (`glueNodeFreeIso`).
* Skeletons of reordered diagrams (`SkeletonIso.of_reanchor`).
-/
module

public import FreeMarkov.Stage4.Lemma45b

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

/-- The diagram `Θ` with its domain ordered by the list `l`. -/
def reanchor (Θ : Diagram G.toFreeGraphMonoid N E) (l : List E) (hl : l.Perm Θ.dom) :
    Diagram G.toFreeGraphMonoid N E where
  toPGraph := Θ.toPGraph
  dom := l
  cod := Θ.cod
  dom_nodup := hl.nodup_iff.2 Θ.dom_nodup
  cod_nodup := Θ.cod_nodup
  mem_dom e := by rw [hl.mem_iff]; exact Θ.mem_dom e
  mem_cod := Θ.mem_cod
  val := Θ.val

section Reanchor

variable {Θ : Diagram G.toFreeGraphMonoid N E} {l : List E} {hl : l.Perm Θ.dom}

theorem reanchor_live (x : N) : (Θ.reanchor l hl).Live x ↔ Θ.Live x := Iff.rfl
theorem reanchor_isOrigin (q e : E) : (Θ.reanchor l hl).IsOrigin q e ↔ Θ.IsOrigin q e := Iff.rfl

end Reanchor

/-- **Skeletons of reordered diagrams.** If the domains of `Θ₁`, `Θ₂` are reordered in the same way
(`l₁[j] = Θ₁.dom[ρ j]`, `l₂[j] = Θ₂.dom[ρ j]` with `ρ` onto the positions), a skeleton bijection of
the reordered diagrams is one of `Θ₁`, `Θ₂`. -/
theorem SkeletonIso.of_reanchor {Θ₁ : Diagram G.toFreeGraphMonoid N E}
    {Θ₂ : Diagram G.toFreeGraphMonoid N' E'} {l₁ : List E} {l₂ : List E'} {hl₁ : l₁.Perm Θ₁.dom}
    {hl₂ : l₂.Perm Θ₂.dom} (ρ : ℕ → ℕ) (h₁ : ∀ j, l₁[j]? = Θ₁.dom[ρ j]?)
    (h₂ : ∀ j, l₂[j]? = Θ₂.dom[ρ j]?) (hρ : ∀ k < Θ₁.dom.length, ∃ j, ρ j = k)
    (hlen : Θ₁.dom.length = Θ₂.dom.length)
    {π : {x // (Θ₁.reanchor l₁ hl₁).Live x} ≃ {y // (Θ₂.reanchor l₂ hl₂).Live y}}
    (h : SkeletonIso (Θ₁.reanchor l₁ hl₁) (Θ₂.reanchor l₂ hl₂) π) : SkeletonIso Θ₁ Θ₂ π := by
  have hm : ∀ e e', OriginsMatch (Γ := Θ₁.reanchor l₁ hl₁) (Υ := Θ₂.reanchor l₂ hl₂) π e e' →
      OriginsMatch (Γ := Θ₁) (Υ := Θ₂) π e e' := by
    intro e e' hmm
    refine ⟨fun k => ?_, fun y j => hmm.2 y j⟩
    by_cases hk : k < Θ₁.dom.length
    · obtain ⟨j, rfl⟩ := hρ _ hk
      have := hmm.1 j
      simp only [OriginAt] at this ⊢
      rwa [show (Θ₁.reanchor l₁ hl₁).dom = l₁ from rfl, show (Θ₂.reanchor l₂ hl₂).dom = l₂ from rfl,
        h₁, h₂] at this
    · simp only [OriginAt, List.getElem?_eq_none (not_lt.1 hk),
        List.getElem?_eq_none (hlen ▸ not_lt.1 hk : Θ₂.dom.length ≤ k)]
      simp
  exact ⟨h.val_eq, fun i e e' he he' => hm e e' (h.cod_match i e e' he he'),
    fun x i e e' he he' => hm e e' (h.ins_match x i e e' he he')⟩

/-! ### Gluing a node-free diagram of a permutation on the left -/

section GlueNodeFree

variable (a : FreeMonoid S) (c : List (Fin (wlen a))) (hc : c.Nodup) (hc' : ∀ i, i ∈ c)

/-- The node-free diagram from `a` whose codomain lists the positions of `a` in the order `c`. -/
def permNF : Diagram G.toFreeGraphMonoid Empty (Fin (wlen a)) :=
  nodeFree (G := G.toFreeGraphMonoid) (letters a) (List.finRange _) c (List.nodup_finRange _)
    (List.mem_finRange) hc hc'

theorem permNF_domWord : (permNF (G := G) a c hc hc').domWord = a := ofList_map_letters a

theorem permNF_codWord :
    (permNF (G := G) a c hc hc').codWord = FreeMonoid.ofList (c.map (letters a)) := rfl

include hc hc' in
theorem length_c : c.length = wlen a := by
  have h₁ : c.length ≤ (List.finRange (wlen a)).length :=
    (List.Nodup.subperm hc fun i _ => List.mem_finRange i).length_le
  have h₂ : (List.finRange (wlen a)).length ≤ c.length :=
    (List.Nodup.subperm (List.nodup_finRange _) fun i _ => hc' i).length_le
  simp at h₁ h₂
  omega

variable {a c hc hc'} (Θ : Diagram G.toFreeGraphMonoid N E)
  (hΘ : (permNF (G := G) a c hc hc').codWord = Θ.domWord)

include hΘ in
theorem length_dom_eq : Θ.dom.length = c.length := by
  have := congrArg List.length (FreeMonoid.ofList.injective hΘ)
  rw [List.length_map, List.length_map] at this
  exact this.symm

include hΘ in
theorem idxOf_lt (i : Fin (wlen a)) : c.idxOf i < Θ.dom.length := by
  rw [length_dom_eq Θ hΘ]
  exact List.idxOf_lt_length_of_mem (hc' i)

/-- The reordered domain. -/
noncomputable def reorder : List E :=
  (List.finRange (wlen a)).map fun i => Θ.dom[c.idxOf i]'(idxOf_lt Θ hΘ i)

end GlueNodeFree

section GlueIso

variable {a : FreeMonoid S} {c : List (Fin (wlen a))} {hc : c.Nodup} {hc' : ∀ i, i ∈ c}
  {Θ : Diagram G.toFreeGraphMonoid N E} (hΘ : (permNF (G := G) a c hc hc').codWord = Θ.domWord)
include hΘ

omit hΘ in
include hc' in
theorem getElem_idxOf (i : Fin (wlen a)) : c[c.idxOf i]'(List.idxOf_lt_length_of_mem (hc' i)) = i :=
  List.getElem_idxOf _

omit hΘ in
include hc in
theorem idxOf_getElem (k : ℕ) (hk : k < c.length) : c.idxOf c[k] = k :=
  List.Nodup.idxOf_getElem hc k hk

theorem v₀_reorder (i : Fin (wlen a)) :
    Θ.val.v₀ (Θ.dom[c.idxOf i]'(idxOf_lt Θ hΘ i)) = letters a i := by
  have h' : c.map (letters a) = Θ.dom.map Θ.val.v₀ := FreeMonoid.ofList.injective hΘ
  have := getElem_eq_of_map_eq (letters a) Θ.val.v₀ h' (c.idxOf i)
    (List.idxOf_lt_length_of_mem (hc' i)) (idxOf_lt Θ hΘ i)
  rw [← this, getElem_idxOf (hc' := hc')]

theorem reorder_perm : (reorder Θ hΘ).Perm Θ.dom := by
  refine (List.perm_ext_iff_of_nodup ?_ Θ.dom_nodup).2 fun e => ?_
  · refine (List.nodup_finRange _).map fun i i' h => ?_
    have := (Θ.dom_nodup.getElem_inj_iff).1 h
    rw [← getElem_idxOf (hc' := hc') i, ← getElem_idxOf (hc' := hc') i']
    simp only [this]
  · simp only [reorder, List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact List.getElem_mem _
    · intro he
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
      have hk' : k < c.length := length_dom_eq Θ hΘ ▸ hk
      refine ⟨c[k], ?_⟩
      simp only [idxOf_getElem (hc := hc) k hk']

/-- The positions of the reordered domain. -/
noncomputable def reorderPos (j : ℕ) : ℕ :=
  if h : j < wlen a then c.idxOf (⟨j, h⟩ : Fin (wlen a)) else j

theorem reorder_getElem? (j : ℕ) : (reorder Θ hΘ)[j]? = Θ.dom[reorderPos (c := c) j]? := by
  unfold reorderPos
  split_ifs with h
  · have hj : j < (List.finRange (wlen a)).length := by rw [List.length_finRange]; exact h
    simp only [reorder, List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem_finRange,
      Option.map_some]
    rw [List.getElem?_eq_getElem (idxOf_lt Θ hΘ _)]
    rfl
  · have h₁ : (reorder Θ hΘ)[j]? = none := by
      rw [List.getElem?_eq_none]
      simp only [reorder, List.length_map, List.length_finRange]
      omega
    rw [h₁, List.getElem?_eq_none]
    rw [length_dom_eq Θ hΘ, length_c a c hc hc']
    omega

theorem reorderPos_surj (k : ℕ) (hk : k < Θ.dom.length) : ∃ j, reorderPos (c := c) j = k := by
  have hk' : k < c.length := length_dom_eq Θ hΘ ▸ hk
  refine ⟨(c[k] : Fin (wlen a)).1, ?_⟩
  simp only [reorderPos, (c[k]).2, dite_true, Fin.eta, idxOf_getElem (hc := hc) k hk']

theorem glueIn_nodeFree (d : E) :
    Sum.elim (fun i => Θ.dom[c.idxOf i]'(idxOf_lt Θ hΘ i)) (fun e : Θ.InnerSrc => e.1)
      (PGraph.glueIn ((permNF (G := G) a c hc hc').toAGraph.matching Θ.toAGraph
        (length_eq_of_codWord_eq hΘ)) d) = d := by
  by_cases hd : Θ.src d = none
  · rw [PGraph.glueIn_of_eq_none _ hd, Sum.elim_inl]
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ((Θ.mem_dom d).2 hd)
    have hk' : k < c.length := length_dom_eq Θ hΘ ▸ hk
    have hm := Enumeration.matching_getElem (permNF (G := G) a c hc hc').toAGraph.codEnum
      Θ.toAGraph.domEnum (length_eq_of_codWord_eq hΘ) k hk'
    have hm' : (permNF (G := G) a c hc hc').toAGraph.matching Θ.toAGraph (length_eq_of_codWord_eq hΘ)
        ⟨c[k], (permNF (G := G) a c hc hc').toAGraph.codEnum.mem_of_mem (List.getElem_mem hk')⟩ =
        ⟨Θ.dom[k], hd⟩ := Subtype.ext hm
    rw [← hm', Equiv.symm_apply_apply]
    simp only [idxOf_getElem (hc := hc) k hk']
  · rw [PGraph.glueIn_of_ne_none _ hd]
    rfl

/-- **Gluing a node-free diagram of a permutation on the left reorders the domain.** -/
noncomputable def glueNodeFreeIso :
    ((permNF (G := G) a c hc hc').glue Θ hΘ).Iso (Θ.reanchor (reorder Θ hΘ) (reorder_perm hΘ)) :=
  Iso.ofProj (Sum.elim Empty.elim id) (Sum.elim (fun i => Θ.dom[c.idxOf i]'(idxOf_lt Θ hΘ i))
      (fun e : Θ.InnerSrc => e.1)) id id
    (by rintro (x | x) (y | y) h <;> first | exact x.elim | exact y.elim | rw [show x = y from h])
    Function.injective_id
    (by
      rintro (i | ⟨e, he⟩) (i' | ⟨e', he'⟩) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · have := (Θ.dom_nodup.getElem_inj_iff).1 h
        rw [← getElem_idxOf (hc' := hc') i, ← getElem_idxOf (hc' := hc') i']
        simp only [this]
      · exact (he' (by rw [← h]; exact (Θ.mem_dom _).1 (List.getElem_mem _))).elim
      · exact (he (by rw [h]; exact (Θ.mem_dom _).1 (List.getElem_mem _))).elim
      · exact congrArg Sum.inr (Subtype.ext h))
    Function.injective_id
    (fun t => ⟨fun _ => ⟨t, rfl⟩, fun _ => ⟨.inr t, rfl⟩⟩)
    (fun t => ⟨fun _ => ⟨t, rfl⟩, fun _ => by
      by_cases ht : Θ.src t = none
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ((Θ.mem_dom t).2 ht)
        have hk' : k < c.length := length_dom_eq Θ hΘ ▸ hk
        exact ⟨.inl c[k], by simp only [Sum.elim_inl, idxOf_getElem (hc := hc) k hk']⟩
      · exact ⟨.inr ⟨t, ht⟩, rfl⟩⟩)
    (by
      rintro (x | x) y h
      · exact x.elim
      · simp only [Sum.elim_inr, id] at h
        subst h
        show ((Θ.ins x).map _).map _ = (Θ.ins x).map id
        rw [List.map_map, List.map_id]
        exact (List.map_congr_left fun d _ => glueIn_nodeFree hΘ d).trans (List.map_id _))
    (by
      rintro (x | x) y h
      · exact x.elim
      · simp only [Sum.elim_inr, id] at h
        subst h
        show ((Θ.outs x).map _).map _ = (Θ.outs x).map id
        rw [List.map_map, List.map_id]
        exact (List.map_congr_left fun d _ => glueIn_nodeFree hΘ d).trans (List.map_id _))
    (by
      show (((List.finRange _).map Sum.inl).map _) = (reorder Θ hΘ).map id
      rw [List.map_map, List.map_id]
      rfl)
    (by
      show ((Θ.cod.map _).map _) = Θ.cod.map id
      rw [List.map_map, List.map_id]
      exact (List.map_congr_left fun d _ => glueIn_nodeFree hΘ d).trans (List.map_id _))
    (by
      rintro (i | e) e' h
      · simp only [Sum.elim_inl, id] at h
        subst h
        exact (v₀_reorder hΘ i).symm
      · simp only [Sum.elim_inr, id] at h
        subst h
        rfl)
    (by
      rintro (x | x) y h
      · exact x.elim
      · simp only [Sum.elim_inr, id] at h
        subst h
        rfl)

end GlueIso

end Diagram

end FreeMarkov
