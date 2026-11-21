/-
Free Markov categories, Stage 4: a surgery with a template satisfying `StepCond` (in both
directions) does not change the skeleton.

"Isomorphic diagrams have the same skeleton, so for the first claim it is enough to consider the
case that `Υ` is the result of a Markov surgery on `Γ` ... The nodes and the edges of `Γ` outside
`Γ'` are also nodes and edges of `Υ`, and the edges in `dom(Γ')`, `cod(Γ')` are identified with
those in `dom(Λ)`, `cod(Λ)`."

The bijection of live nodes is the one given by the canonical description; it is injective by
`live_forward`, and onto because the reverse surgery gives an injection the other way.
-/
module

public import FreeMarkov.Stage4.StepAnalysis

@[expose] public section

universe u w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S}

section Canon

variable {NX : Type u₁} {EX : Type u₂} {NΩ : Type u₃} {EΩ : Type u₄} {NΛ : Type u₅} {EΛ : Type u₆}
  {NY : Type u₇} {EY : Type u₈} {NY' : Type u₉} {EY' : Type u₁₀}
  {X : Diagram G.toFreeGraphMonoid NX EX} {Ω : PDiagram G.toFreeGraphMonoid NΩ EΩ}
  {Λ : PDiagram G.toFreeGraphMonoid NΛ EΛ} {ιN : NΩ → NX} {ιE : EΩ → EX}
  {α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}} {β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}}
  {Y : Diagram G.toFreeGraphMonoid NY EY} {Y' : Diagram G.toFreeGraphMonoid NY' EY'}

/-- A canonical description transported along an isomorphism. -/
def CanonProj.ofIso (P : CanonProj X Ω ιN ιE α β Y) (j : Y.Iso Y') :
    CanonProj X Ω ιN ιE α β Y' where
  pN := P.pN ∘ j.eN.symm
  pE := P.pE ∘ j.eE.symm
  pN_inj := P.pN_inj.comp j.eN.symm.injective
  pE_inj := P.pE_inj.comp j.eE.symm.injective
  pN_range t := ⟨fun ⟨n, h⟩ => (P.pN_range t).1 ⟨_, h⟩, fun h => by
    obtain ⟨n, hn⟩ := (P.pN_range t).2 h
    exact ⟨j.eN n, by simp [hn]⟩⟩
  pE_range t := ⟨fun ⟨e, h⟩ => (P.pE_range t).1 ⟨_, h⟩, fun h => by
    obtain ⟨e, he⟩ := (P.pE_range t).2 h
    exact ⟨j.eE e, by simp [he]⟩⟩
  ins n := by
    have := j.symm.ins_map n
    rw [← List.map_map, show Y'.ins n = Y'.toAGraph.toPGraph.ins n from rfl]
    erw [this.symm]
    exact P.ins _
  outs n := by
    have := j.symm.outs_map n
    rw [← List.map_map]
    erw [this.symm]
    exact P.outs _
  dom := by
    rw [← List.map_map]
    erw [j.symm.dom_map.symm]
    exact P.dom
  cod := by
    rw [← List.map_map]
    erw [j.symm.cod_map.symm]
    exact P.cod
  v₀ e := by
    show Y'.val.v₀ e = X.canonV₀ Λ (P.pE (j.eE.symm e))
    rw [← P.v₀]
    exact (j.symm.v₀_map e).symm
  v₁ n := by
    show Y'.val.v₁ n = X.canonV₁ Λ (P.pN (j.eN.symm n))
    rw [← P.v₁]
    exact (j.symm.v₁_map n).symm

theorem getElem?_eq_iff_of_map {α' : Type*} {β' : Type*} {γ' : Type*} {l : List α'} {l' : List β'}
    {p : β' → γ'} {q : α' → γ'} (hp : Function.Injective p) (hq : Function.Injective q)
    (h : l'.map p = l.map q) {a : α'} {b : β'} (hab : p b = q a) (j : ℕ) :
    l[j]? = some a ↔ l'[j]? = some b := by
  have h' := congrArg (fun l => l[j]?) h
  simp only [List.getElem?_map] at h'
  constructor
  · intro ha
    rw [ha, Option.map_some, ← hab] at h'
    obtain ⟨b', hb', hpb⟩ := Option.map_eq_some_iff.1 h'
    rw [hb', hp hpb]
  · intro hb
    rw [hb, Option.map_some, hab] at h'
    obtain ⟨a', ha', hqa⟩ := Option.map_eq_some_iff.1 h'.symm
    rw [ha', hq hqa]

variable (hE : Emb X Ω ιN ιE) (P : CanonProj X Ω ιN ιE α β Y) (hC : StepCond Ω Λ α β)
include hE P hC

/-- The live nodes of `X` in `Y`. -/
noncomputable def liveMap [Finite EX] (x : {x // X.Live x}) : {y // Y.Live y} :=
  ⟨(P.exists_node (canonNode_inl (live_outside hE hC x.2))).choose,
    live_forward hE P hC x.2 (P.exists_node (canonNode_inl (live_outside hE hC x.2))).choose_spec⟩

theorem liveMap_spec [Finite EX] (x : {x // X.Live x}) : P.pN (liveMap hE P hC x).1 = .inl x.1 :=
  (P.exists_node (canonNode_inl (live_outside hE hC x.2))).choose_spec

theorem liveMap_injective [Finite EX] : Function.Injective (liveMap hE P hC) := by
  intro x x' h
  have h₁ := liveMap_spec hE P hC x
  rw [h, liveMap_spec hE P hC x', Sum.inl.injEq] at h₁
  exact Subtype.ext h₁.symm

theorem card_live_le [Finite EX] [Finite NY] :
    Nat.card {x // X.Live x} ≤ Nat.card {y // Y.Live y} :=
  Nat.card_le_card_of_injective _ (liveMap_injective hE P hC)

/-- Origins of corresponding consumers match. -/
theorem originsMatch_of_step [Finite EX] [Finite EY] [Finite NY]
    (hcard : Nat.card {y // Y.Live y} ≤ Nat.card {x // X.Live x}) {g : EX} {g' : EY}
    (hg : X.Consumer g) (hgo : ∀ z, X.tgt g ≠ some (ιN z)) (hpe : P.pE g' = canonF ιE α β g) :
    OriginsMatch (Equiv.ofBijective _ ((liveMap_injective hE P hC).bijective_of_nat_card_le hcard))
      g g' := by
  obtain ⟨q, hq⟩ := PGraph.exists_isOrigin X.dupCond g
  have hgc := hg.reachCod
  obtain ⟨e₁, he₁⟩ := P.exists_edge (canonEdge_inl hE (origin_outside hE hC hq hgc))
  have hY : Y.IsOrigin e₁ g' := origin_forward hE P hC hq hgc hgo he₁ hpe
  have hX : ∀ q', X.IsOrigin q' g ↔ q' = q := fun q' =>
    ⟨fun h => PGraph.isOrigin_unique X.dupCond h hq, fun h => h ▸ hq⟩
  have hY' : ∀ e', Y.IsOrigin e' g' ↔ e' = e₁ := fun e' =>
    ⟨fun h => PGraph.isOrigin_unique Y.dupCond h hY, fun h => h ▸ hY⟩
  refine ⟨fun j => ?_, fun y j => ?_⟩
  · simp only [OriginAt, hX, hY', exists_eq_right]
    exact getElem?_eq_iff_of_map P.pE_inj Sum.inl_injective P.dom he₁ j
  · simp only [OriginAt, hX, hY', exists_eq_right, Equiv.ofBijective_apply]
    have hn : P.pN (liveMap hE P hC y).1 = .inl y.1 := liveMap_spec hE P hC y
    refine getElem?_eq_iff_of_map P.pE_inj Sum.inl_injective ?_ he₁ j
    rw [P.outs, hn]
    rfl

/-- **The skeleton bijection of a surgery step.** -/
theorem skeletonIso_of_step [Finite EX] [Finite EY] [Finite NY]
    (hcard : Nat.card {y // Y.Live y} ≤ Nat.card {x // X.Live x}) :
    SkeletonIso X Y
      (Equiv.ofBijective _ ((liveMap_injective hE P hC).bijective_of_nat_card_le hcard)) where
  val_eq x := by
    show Y.val.v₁ (liveMap hE P hC x).1 = _
    rw [P.v₁, liveMap_spec hE P hC x]
    rfl
  cod_match i g g' hg hg' := by
    refine originsMatch_of_step hE P hC hcard (Or.inl ((X.mem_cod g).1 (List.mem_of_getElem? hg)))
      (fun z hz => ?_) ?_
    · rw [(X.mem_cod g).1 (List.mem_of_getElem? hg)] at hz; cases hz
    · have h' := congrArg (fun l => l[i]?) P.cod
      simp only [List.getElem?_map, hg, hg', Option.map_some, Option.some.injEq] at h'
      exact h'
  ins_match x i g g' hg hg' := by
    have hgx : X.tgt g = some x.1 := (X.mem_ins x.1 g).1 (List.mem_of_getElem? hg)
    refine originsMatch_of_step hE P hC hcard (Or.inr ⟨x.1, hgx, x.2⟩)
      (fun z hz => live_outside hE hC x.2 z (by rw [hgx, Option.some.injEq] at hz; exact hz.symm)) ?_
    have hn : P.pN (liveMap hE P hC x).1 = .inl x.1 := liveMap_spec hE P hC x
    have h' := congrArg (fun l => l[i]?) (P.ins (liveMap hE P hC x).1)
    rw [hn] at h'
    simp only [List.getElem?_map, canonIns] at h'
    simp only [Equiv.ofBijective_apply] at hg'
    rw [hg', hg] at h'
    simpa using h'

end Canon

/-! ### Surgery steps -/

section Step

variable {T : Set (Template.{u} G.toFreeGraphMonoid)}
  {N : Type u₁} {E : Type u₂} {N' : Type u₃} {E' : Type u₄}
  {X : Diagram G.toFreeGraphMonoid N E} {Υ : Diagram G.toFreeGraphMonoid N' E'}

/-- The data of a surgery step: an embedding of `Ω` and a canonical description of the result. -/
theorem TStep.canon (h : TStep T X Υ) :
    ∃ τ ∈ T, ∃ (ιN : τ.NΩ → N) (ιE : τ.EΩ → E), Emb X τ.Ω ιN ιE ∧
      Nonempty (CanonProj X τ.Ω ιN ιE τ.α τ.β Υ) := by
  obtain ⟨τ, hτ, A, hA, φ, ⟨j⟩⟩ := h
  exact ⟨τ, hτ, _, _, emb_of_iso X A hA.edge_at φ,
    ⟨(X.surgeryAt_canonProj hA.sharpLayer φ τ.α τ.β τ.hα τ.hβ (fun _ => rfl) (fun _ => rfl)).ofIso j⟩⟩

theorem TStep.card_live_le [Finite E] [Finite N'] (hT : ∀ τ ∈ T, StepCond τ.Ω τ.Λ τ.α τ.β)
    (h : TStep T X Υ) : Nat.card {x // X.Live x} ≤ Nat.card {y // Υ.Live y} := by
  obtain ⟨τ, hτ, ιN, ιE, hE, ⟨P⟩⟩ := h.canon
  exact Diagram.card_live_le hE P (hT τ hτ)

/-- **A surgery step with templates satisfying `StepCond` keeps the skeleton.** -/
theorem TStep.sameSkeleton [Finite N] [Finite E] [Finite N'] [Finite E']
    (hT : ∀ τ ∈ T, StepCond τ.Ω τ.Λ τ.α τ.β) (hTs : ∀ τ ∈ T, τ.symm ∈ T) (h : TStep T X Υ) :
    SameSkeleton X Υ := by
  have hcard := (h.symm hTs).card_live_le hT
  obtain ⟨τ, hτ, ιN, ιE, hE, ⟨P⟩⟩ := h.canon
  exact ⟨h.domWord_eq.symm, h.codWord_eq.symm, _, skeletonIso_of_step hE P (hT τ hτ) hcard⟩

end Step

end Diagram

end FreeMarkov
