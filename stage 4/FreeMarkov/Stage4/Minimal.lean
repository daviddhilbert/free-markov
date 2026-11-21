/-
Free Markov categories, Stage 4: Markov minimal diagrams and the first claim of Lemma 4.4.

"Call the diagram `Γ` Markov minimal if the value of every node in `Δ_Γ` is a discard."

"For the first claim, suppose that `Γ` is not Markov minimal. We show that a Markov surgery on
`Γ` results in a diagram with fewer nodes whose values are not discards, which is enough. Let
`x` be maximal in `Γ̇` among the nodes in `Δ_Γ` whose values are not discards. ... So, if `v(x)`
is a duplicate then one of its outputs ends at a discard, and a surgery with (4.2) removes `x`
and this discard. If `v(x) = f` is not a duplicate then all the outputs of `x`, if any, end at
discards, and a surgery with (4.4) replaces `x` and these discards with discards on the inputs
of `x`."
-/
module

public import FreeMarkov.Stage4.EmbStep

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S}

/-- **Markov minimal** (Section 4): "the value of every node in `Δ_Γ` is a discard". -/
def MarkovMinimal {N : Type u₁} {E : Type u₂} (Γ : Diagram G.toFreeGraphMonoid N E) : Prop :=
  ∀ x, Γ.QuasiTerminal x → Γ.val.IsDisc x

/-- The number of nodes whose value is not a discard. -/
noncomputable def ndCount {N : Type u₁} {E : Type u₂} (Γ : Diagram G.toFreeGraphMonoid N E) : ℕ :=
  Nat.card {x // ¬ Γ.val.IsDisc x}

theorem ndCount_iso {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}
    {Γ : Diagram G.toFreeGraphMonoid N E} {Υ : Diagram G.toFreeGraphMonoid N' E'} (i : Γ.Iso Υ) :
    Γ.ndCount = Υ.ndCount :=
  Nat.card_congr (i.eN.subtypeEquiv fun x => by
    unfold Valuation.IsDisc
    rw [i.v₁_map])

theorem dup_ne_disc (a b : S) : G.dup a ≠ G.disc b := by
  intro h
  have := G.t_dup a
  rw [h, G.t_disc] at this
  exact absurd (congrArg (fun w => (FreeMonoid.toList w).length) this) (by simp)

variable {NX : Type u₁} {EX : Type u₂} {X : Diagram G.toFreeGraphMonoid NX EX}

/-! ### Embedding facts -/

namespace PEmb

theorem src_some {N : Type u₃} {E : Type u₄} {D : Diagram G.toFreeGraphMonoid N E} (e : PEmb D X)
    {d : E} {z : N} (h : D.src d = some z) : X.src (e.ιE d) = some (e.ιN z) := by
  rw [← X.mem_outs, e.outs]
  exact List.mem_map_of_mem ((D.mem_outs z d).2 h)

theorem oneNode_mem (x : NX) {f : G.A} (hx : X.val.v₁ x = f) (d) :
    (oneNode x hx).ιE d ∈ X.ins x ∨ (oneNode x hx).ιE d ∈ X.outs x := by
  rcases d with i | j
  · exact Or.inl (List.getElem_mem _)
  · exact Or.inr (List.getElem_mem _)

theorem idD_mem (a : FreeMonoid S) (l : List EX) (hl : l.Nodup)
    (hv : l.map X.val.v₀ = FreeMonoid.toList a) (d) : (idD a l hl hv).ιE d ∈ l :=
  List.getElem_mem _

variable {N : Type u₅} {E : Type u₆} {N' : Type u₇} {E' : Type u₈}
  {Γ : Diagram G.toFreeGraphMonoid N E} {Ω : Diagram G.toFreeGraphMonoid N' E'}

/-- Gluing with the disjointness of edges derived from the sources of the domain edges of the
first piece. -/
def glue' (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (h : Γ.codWord = Ω.domWord)
    (hc : Γ.cod.map e₁.ιE = Ω.dom.map e₂.ιE) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hdom : ∀ d, Γ.src d = none → ∀ z, X.src (e₁.ιE d) ≠ some (e₂.ιN z)) :
    PEmb (Γ.glue Ω h) X :=
  glue e₁ e₂ h hc hN fun d d' hdd => by
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 d'.2
    have h₂ := e₂.src_some hz
    cases hds : Γ.src d with
    | none => exact hdom d hds z (hdd ▸ h₂)
    | some z₁ =>
      have h₁ := e₁.src_some hds
      rw [hdd, h₂, Option.some.injEq] at h₁
      exact hN _ _ h₁.symm

theorem glue'_dom (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (h : Γ.codWord = Ω.domWord)
    (hc : Γ.cod.map e₁.ιE = Ω.dom.map e₂.ιE) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hdom : ∀ d, Γ.src d = none → ∀ z, X.src (e₁.ιE d) ≠ some (e₂.ιN z)) :
    (Γ.glue Ω h).dom.map (glue' e₁ e₂ h hc hN hdom).ιE = Γ.dom.map e₁.ιE :=
  glue_dom _ _ _ _ _ _

theorem glue'_cod (e₁ : PEmb Γ X) (e₂ : PEmb Ω X) (h : Γ.codWord = Ω.domWord)
    (hc : Γ.cod.map e₁.ιE = Ω.dom.map e₂.ιE) (hN : ∀ z z', e₁.ιN z ≠ e₂.ιN z')
    (hdom : ∀ d, Γ.src d = none → ∀ z, X.src (e₁.ιE d) ≠ some (e₂.ιN z)) :
    (Γ.glue Ω h).cod.map (glue' e₁ e₂ h hc hN hdom).ιE = Ω.cod.map e₂.ιE :=
  glue_cod _ _ _ _ _ _

end PEmb

/-- A gluing whose first piece is a one-node diagram has no loose edges. -/
theorem oneNode_glue_noLoose {N' : Type u₃} {E' : Type u₄} (f : G.A)
    (Ω : Diagram G.toFreeGraphMonoid N' E') (h : (Diagram.oneNode (G := G.toFreeGraphMonoid) f).codWord = Ω.domWord)
    (d) : ((Diagram.oneNode f).glue Ω h).src d ≠ none ∨ ((Diagram.oneNode f).glue Ω h).tgt d ≠ none := by
  rcases d with (i | j) | d
  · right
    simp [Diagram.glue, AGraph.glue, PGraph.glueTgt, Diagram.oneNode, PGraph.oneNode]
  · left
    simp [Diagram.glue, AGraph.glue, Diagram.oneNode, PGraph.oneNode]
  · left
    simpa [Diagram.glue, AGraph.glue] using d.2

/-! ### The discards of (4.4) -/

namespace FreeDDGraphMonoidAux

open FreeDDGraphMonoid

theorem discListD_isDisc (l : List S) (z : FreeDDGraphMonoid.discN l) :
    (G.discListD l).val.IsDisc z := by
  induction l with
  | nil => exact z.elim
  | cons a l ih =>
    rcases z with z | z
    · exact ⟨a, rfl⟩
    · exact ih z

end FreeDDGraphMonoidAux

/-- The embedding of `ε_{a_1} ⊗ ⋯ ⊗ ε_{a_n}` at discards `ys` whose inputs are `es`, with the
images of its nodes and edges and of its domain ordering. -/
noncomputable def discListEmb : (l : List S) → (ys : List NX) → (es : List EX) →
    (hy : ys.length = l.length) → (he : es.length = l.length) → ys.Nodup → es.Nodup →
    (∀ (k : ℕ) (hk : k < l.length), X.val.v₁ (ys[k]'(by omega)) = G.disc l[k]) →
    (∀ (k : ℕ) (hk : k < l.length), X.ins (ys[k]'(by omega)) = [es[k]'(by omega)]) →
    {e : PEmb (G.discListD l) X // (∀ z, e.ιN z ∈ ys) ∧ (∀ d, e.ιE d ∈ es) ∧
      (G.discListD l).dom.map e.ιE = es}
  | [], ys, es, hy, he, _, _, _, _ =>
    ⟨PEmb.idD 1 [] List.nodup_nil rfl, fun z => z.elim, fun d => (List.not_mem_nil (PEmb.idD_mem
      (X := X) 1 [] List.nodup_nil rfl d)).elim, by
        rw [List.length_eq_zero_iff.1 he]
        exact PEmb.idD_dom (X := X) 1 [] List.nodup_nil rfl⟩
  | a :: l, y :: ys, e :: es, hy, he, hyn, hen, hv, hi =>
    let r := discListEmb l ys es (by simpa using hy) (by simpa using he) (List.nodup_cons.1 hyn).2
        (List.nodup_cons.1 hen).2 (fun k hk => hv (k + 1) (by simp; omega))
        (fun k hk => hi (k + 1) (by simp; omega))
    have hy₀ : X.val.v₁ y = G.disc a := hv 0 (by simp)
    have hiy : X.ins y = [e] := hi 0 (by simp)
    have hoy : X.outs y = [] := X.val.outs_eq_nil_of_disc hy₀
    ⟨PEmb.tensor (PEmb.oneNode y hy₀) r.1 (fun _ z' h => (List.nodup_cons.1 hyn).1
        (by rw [show y = r.1.ιN z' from h]; exact r.2.1 z'))
      (fun d d' h => by
        rcases PEmb.oneNode_mem y hy₀ d with hd | hd
        · rw [hiy, List.mem_singleton] at hd
          exact (List.nodup_cons.1 hen).1 (hd ▸ h ▸ r.2.2.1 d')
        · rw [hoy] at hd; cases hd),
      by
        rintro (z | z)
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (r.2.1 z),
      by
        rintro (d | d)
        · rcases PEmb.oneNode_mem y hy₀ d with hd | hd
          · rw [hiy, List.mem_singleton] at hd
            show (PEmb.oneNode y hy₀).ιE d ∈ e :: es
            rw [hd]; exact List.mem_cons_self
          · rw [hoy] at hd; cases hd
        · exact List.mem_cons_of_mem _ (r.2.2.1 d),
      by
        show ((G.discD a).tensor (G.discListD l)).dom.map _ = _
        rw [PEmb.tensor_dom, PEmb.oneNode_dom, hiy, r.2.2.2]
        rfl⟩
  | _ :: _, [], _, hy, _, _, _, _, _ => False.elim (by simp at hy)
  | _ :: _, _ :: _, [], _, he, _, _, _, _ => False.elim (by simp at he)


/-! ### The embeddings of (4.2) and (4.4) -/

/-- (4.2) at a duplicate `x` whose second output `e₁` ends at a discard `y`. -/
noncomputable def counitEmb {x y : NX} {a : S} (hx : X.val.v₁ x = G.dup a) (hy : X.val.v₁ y = G.disc a)
    {e₀ e₁ : EX} (hxo : X.outs x = [e₀, e₁]) (hyi : X.ins y = [e₁]) : PEmb (G.counitΩD a) X := by
  have hne : e₀ ≠ e₁ := by
    have := X.outs_nodup x
    rw [hxo] at this
    simpa using this
  have hv : [e₀].map X.val.v₀ = FreeMonoid.toList (FreeMonoid.of a) := by
    obtain ⟨f₀, f₁, h, h₀, -⟩ := X.val.outs_eq_of_t_dup hx
    rw [hxo] at h
    simp only [List.cons.injEq] at h
    rw [h.1]
    simp [h₀]
  have hoy : X.outs y = [] := X.val.outs_eq_nil_of_disc hy
  have hxy : x ≠ y := fun h => dup_ne_disc (G := G) a a (by rw [← hx, ← hy, h])
  refine PEmb.glue' (PEmb.oneNode x hx)
    (PEmb.tensor (PEmb.idD (FreeMonoid.of a) [e₀] (List.nodup_singleton _) hv) (PEmb.oneNode y hy)
      (fun z => z.elim) (fun d d' h => ?_)) _ ?_ ?_ ?_
  · have h₁ := PEmb.idD_mem (X := X) (FreeMonoid.of a) [e₀] (List.nodup_singleton _) hv d
    rw [List.mem_singleton] at h₁
    rcases PEmb.oneNode_mem y hy d' with h₂ | h₂
    · rw [hyi, List.mem_singleton, ← h, h₁] at h₂
      exact hne h₂
    · rw [hoy] at h₂; cases h₂
  · rw [PEmb.oneNode_cod, PEmb.tensor_dom, PEmb.idD_dom, PEmb.oneNode_dom, hxo, hyi]
    rfl
  · rintro - (z | z)
    · exact z.elim
    · exact hxy
  · rintro d - (z | z) h
    · exact z.elim
    · have h' : X.src ((PEmb.oneNode x hx).ιE d) = some y := h
      rw [← X.mem_outs, hoy] at h'
      cases h'

/-- (4.2), right counitality, at a duplicate `x` whose first output `e₀` ends at a discard `y`. -/
noncomputable def counitEmb' {x y : NX} {a : S} (hx : X.val.v₁ x = G.dup a) (hy : X.val.v₁ y = G.disc a)
    {e₀ e₁ : EX} (hxo : X.outs x = [e₀, e₁]) (hyi : X.ins y = [e₀]) : PEmb (G.counitΩ'D a) X := by
  have hne : e₀ ≠ e₁ := by
    have := X.outs_nodup x
    rw [hxo] at this
    simpa using this
  have hv : [e₁].map X.val.v₀ = FreeMonoid.toList (FreeMonoid.of a) := by
    obtain ⟨f₀, f₁, h, -, h₁⟩ := X.val.outs_eq_of_t_dup hx
    rw [hxo] at h
    simp only [List.cons.injEq] at h
    rw [h.2.1]
    simp [h₁]
  have hoy : X.outs y = [] := X.val.outs_eq_nil_of_disc hy
  have hxy : x ≠ y := fun h => dup_ne_disc (G := G) a a (by rw [← hx, ← hy, h])
  refine PEmb.glue' (PEmb.oneNode x hx)
    (PEmb.tensor (PEmb.oneNode y hy) (PEmb.idD (FreeMonoid.of a) [e₁] (List.nodup_singleton _) hv)
      (fun _ z => z.elim) (fun d d' h => ?_)) _ ?_ ?_ ?_
  · have h₁ := PEmb.idD_mem (X := X) (FreeMonoid.of a) [e₁] (List.nodup_singleton _) hv d'
    rw [List.mem_singleton] at h₁
    rcases PEmb.oneNode_mem y hy d with h₂ | h₂
    · rw [hyi, List.mem_singleton, h, h₁] at h₂
      exact hne h₂.symm
    · rw [hoy] at h₂; cases h₂
  · rw [PEmb.oneNode_cod, PEmb.tensor_dom, PEmb.idD_dom, PEmb.oneNode_dom, hxo, hyi]
    rfl
  · rintro - (z | z)
    · exact hxy
    · exact z.elim
  · rintro d - (z | z) h
    · have h' : X.src ((PEmb.oneNode x hx).ιE d) = some y := h
      rw [← X.mem_outs, hoy] at h'
      cases h'
    · exact z.elim

/-- (4.4) at a node `x` all of whose outputs end at discards `ys`. -/
noncomputable def natEmb {x : NX} {f : G.A} (hx : X.val.v₁ x = f) (ys : List NX)
    (hy : ys.length = (FreeMonoid.toList (G.t f)).length) (hyn : ys.Nodup)
    (hv : ∀ (k : ℕ) (hk : k < (FreeMonoid.toList (G.t f)).length),
      X.val.v₁ (ys[k]'(by omega)) = G.disc (FreeMonoid.toList (G.t f))[k])
    (hi : ∀ (k : ℕ) (hk : k < (FreeMonoid.toList (G.t f)).length),
      X.ins (ys[k]'(by omega)) = [(X.outs x)[k]'(by rw [length_outs_eq, hx]; exact hk)])
    (hxys : x ∉ ys) :
    {e : PEmb (G.natΩD f) X // e.ιN (.inl ()) = x ∧ ∀ z, e.ιN (.inr z) ∈ ys} := by
  have he : (X.outs x).length = (FreeMonoid.toList (G.t f)).length := by
    rw [length_outs_eq, hx]
  let r := discListEmb (FreeMonoid.toList (G.t f)) ys (X.outs x) hy he hyn (X.outs_nodup x) hv hi
  refine ⟨PEmb.glue' (PEmb.oneNode x hx) r.1 _ ?_ ?_ ?_, rfl, fun z => r.2.1 z⟩
  · rw [PEmb.oneNode_cod, r.2.2.2]
  · intro _ z h
    exact hxys (by rw [show x = r.1.ιN z from h]; exact r.2.1 z)
  · intro d _ z h
    obtain ⟨k, hk, hkz⟩ := List.getElem_of_mem (r.2.1 z)
    have hd := hv k (by omega)
    rw [hkz] at hd
    rw [← X.mem_outs, X.val.outs_eq_nil_of_disc hd] at h
    cases h

/-! ### Removing nodes reduces the count -/

section Count

variable {NΩ : Type u₃} {EΩ : Type u₄} {NΛ : Type*} {EΛ : Type*} {NY : Type*} {EY : Type*}
  {Ω : PDiagram G.toFreeGraphMonoid NΩ EΩ} {Λ : PDiagram G.toFreeGraphMonoid NΛ EΛ}
  {ιN : NΩ → NX} {ιE : EΩ → EX}
  {α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}} {β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}}
  {Y : Diagram G.toFreeGraphMonoid NY EY}

theorem finite_of_canonProj [Finite NX] [Finite EX] [Finite NΛ] [Finite EΛ]
    (P : CanonProj X Ω ιN ιE α β Y) : Finite NY ∧ Finite EY :=
  ⟨Finite.of_injective _ P.pN_inj, Finite.of_injective _ P.pE_inj⟩

theorem ndCount_lt [Finite NX] (P : CanonProj X Ω ιN ιE α β Y) (hΛ : ∀ z, Λ.val.IsDisc z)
    (z₁ : NΩ) (h₁ : ¬ X.val.IsDisc (ιN z₁)) [Finite NY] : Y.ndCount < X.ndCount := by
  classical
  have key : ∀ n : {n // ¬ Y.val.IsDisc n}, ∃ x, P.pN n.1 = .inl x := by
    rintro ⟨n, hn⟩
    rcases h : P.pN n with x | z
    · exact ⟨x, rfl⟩
    · refine (hn ?_).elim
      obtain ⟨a, ha⟩ := hΛ z
      refine ⟨a, ?_⟩
      rw [P.v₁, h]
      exact ha
  let F : {n // ¬ Y.val.IsDisc n} → {x // ¬ X.val.IsDisc x} := fun n =>
    ⟨(key n).choose, fun hd => n.2 (by
      unfold Valuation.IsDisc at hd ⊢
      rw [P.v₁, (key n).choose_spec]
      exact hd)⟩
  have hF : Function.Injective F := by
    intro n n' h
    have h' : (key n).choose = (key n').choose := congrArg Subtype.val h
    have := (key n).choose_spec
    rw [h', ← (key n').choose_spec] at this
    exact Subtype.ext (P.pN_inj this)
  have hns : ¬ Function.Surjective F := by
    intro hs
    obtain ⟨n, hn⟩ := hs ⟨ιN z₁, h₁⟩
    have h₂ := (key n).choose_spec
    have h₃ : (key n).choose = ιN z₁ := congrArg Subtype.val hn
    have hc := (P.pN_range (P.pN n.1)).1 ⟨_, rfl⟩
    rw [h₂] at hc
    exact hc z₁ h₃.symm
  have := Fintype.ofFinite {n // ¬ Y.val.IsDisc n}
  have := Fintype.ofFinite {x // ¬ X.val.IsDisc x}
  unfold ndCount
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_not_surjective F hF hns

end Count

end Diagram

end FreeMarkov
