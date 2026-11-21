/-
Free Markov categories, Stage 4: live nodes and origins through one surgery (proof of
Lemma 4.3).

The result `Y` of a surgery on `X` is described by Stage 2's canonical description
(`CanonProj X Ω ιN ιE α β Y`): the nodes of `Y` are the nodes of `X` outside the image of `Ω`
and the nodes of `Λ`; its edges are the edges of `X` not starting in the image of `Ω` and the
edges of `Λ` with an inner source.  Under three conditions on the template (`StepCond`: no node
of `Ω` that is not a duplicate has an output reaching the codomain of `Ω`; directed paths and
chains through duplicates from the domain to the codomain of `Ω` are also found in `Λ`), this
file shows:

* the live nodes of `X` lie outside the image of `Ω` and are live in `Y` (`live_forward`);
* the origin of a consumer of `X` is carried to the origin of the corresponding consumer of
  `Y` (`origin_forward`).

"Therefore a directed path in `Γ` that ends in `cod(Γ)` and passes through `Γ'` may be
rerouted through `Λ` ... and following an edge backward through `Γ'` or through `Λ` leads to
the same edge, so the consumers have the same origins in `Γ` and in `Υ`."
-/
module

public import FreeMarkov.Stage4.Item1

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S}

/-- An embedding of the diagram `Ω` into `X` as a subgraph all of whose edges at its nodes
are its own (what an isomorphism `Ω ≅ Γ'` with a normal subgraph `Γ' ⊆ X` provides). -/
structure Emb {NX : Type u₁} {EX : Type u₂} {NΩ : Type u₃} {EΩ : Type u₄}
    (X : Diagram G.toFreeGraphMonoid NX EX) (Ω : PDiagram G.toFreeGraphMonoid NΩ EΩ)
    (ιN : NΩ → NX) (ιE : EΩ → EX) : Prop where
  injN : Function.Injective ιN
  injE : Function.Injective ιE
  ins : ∀ z, X.ins (ιN z) = (Ω.ins z).map ιE
  outs : ∀ z, X.outs (ιN z) = (Ω.outs z).map ιE
  v₀ : ∀ d, X.val.v₀ (ιE d) = Ω.val.v₀ d
  v₁ : ∀ z, X.val.v₁ (ιN z) = Ω.val.v₁ z

/-- The embedding given by an isomorphism of `Ω` with a subgraph whose edges at its nodes are
all its own. -/
theorem emb_of_iso {NX : Type u₁} {EX : Type u₂} {NΩ : Type u₃} {EΩ : Type u₄}
    (X : Diagram G.toFreeGraphMonoid NX EX) {Ω : PDiagram G.toFreeGraphMonoid NΩ EΩ}
    (A : Subgraph NX EX) (h : X.EdgeAt A) (φ : Ω.Iso (X.subD A h)) :
    Emb X Ω (fun z => (φ.eN z).1) (fun d => (φ.eE d).1) where
  injN := Subtype.val_injective.comp φ.eN.injective
  injE := Subtype.val_injective.comp φ.eE.injective
  ins z := by
    rw [← PGraph.sub_ins_map_val (φ.eN z) fun e he => h _ (φ.eN z).2 e (Or.inr ((X.mem_ins _ e).1 he)),
      show (X.sub A.node A.edge).ins (φ.eN z) = (Ω.ins z).map φ.eE from φ.ins_map z, List.map_map]
    rfl
  outs z := by
    rw [← PGraph.sub_outs_map_val (φ.eN z) fun e he =>
        h _ (φ.eN z).2 e (Or.inl ((X.mem_outs _ e).1 he)),
      show (X.sub A.node A.edge).outs (φ.eN z) = (Ω.outs z).map φ.eE from φ.outs_map z, List.map_map]
    rfl
  v₀ d := φ.v₀_map d
  v₁ z := φ.v₁_map z

section Analysis

variable {NX : Type u₁} {EX : Type u₂} {NΩ : Type u₃} {EΩ : Type u₄} {NΛ : Type u₅} {EΛ : Type u₆}
  {NY : Type u₇} {EY : Type u₈}
  {X : Diagram G.toFreeGraphMonoid NX EX} {Ω : PDiagram G.toFreeGraphMonoid NΩ EΩ}
  {Λ : PDiagram G.toFreeGraphMonoid NΛ EΛ} {ιN : NΩ → NX} {ιE : EΩ → EX}
  {α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e}} {β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}}
  {Y : Diagram G.toFreeGraphMonoid NY EY}

/-! ### Consequences of an embedding -/

namespace Emb

variable (hE : Emb X Ω ιN ιE)
include hE

theorem src_some {d : EΩ} {z : NΩ} (h : Ω.src d = some z) : X.src (ιE d) = some (ιN z) := by
  rw [← X.mem_outs, hE.outs]
  exact List.mem_map_of_mem ((Ω.mem_outs z d).2 h)

theorem tgt_some {d : EΩ} {z : NΩ} (h : Ω.tgt d = some z) : X.tgt (ιE d) = some (ιN z) := by
  rw [← X.mem_ins, hE.ins]
  exact List.mem_map_of_mem ((Ω.mem_ins z d).2 h)

theorem src_none {d : EΩ} (h : Ω.src d = none) (z : NΩ) : X.src (ιE d) ≠ some (ιN z) := by
  intro h'
  rw [← X.mem_outs, hE.outs, List.mem_map_of_injective hE.injE, Ω.mem_outs, h] at h'
  cases h'

theorem tgt_none {d : EΩ} (h : Ω.tgt d = none) (z : NΩ) : X.tgt (ιE d) ≠ some (ιN z) := by
  intro h'
  rw [← X.mem_ins, hE.ins, List.mem_map_of_injective hE.injE, Ω.mem_ins, h] at h'
  cases h'

theorem eq_of_src {e : EX} {z : NΩ} (h : X.src e = some (ιN z)) : ∃ d, Ω.src d = some z ∧ ιE d = e := by
  rw [← X.mem_outs, hE.outs] at h
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
  exact ⟨d, (Ω.mem_outs z d).1 hd, rfl⟩

theorem eq_of_tgt {e : EX} {z : NΩ} (h : X.tgt e = some (ιN z)) : ∃ d, Ω.tgt d = some z ∧ ιE d = e := by
  rw [← X.mem_ins, hE.ins] at h
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
  exact ⟨d, (Ω.mem_ins z d).1 hd, rfl⟩

theorem isDup_iff (z : NΩ) : X.val.IsDup (ιN z) ↔ Ω.val.IsDup z := by
  unfold Valuation.IsDup
  rw [hE.v₁]

theorem step {d d' : EΩ} (h : Ω.Step d d') : X.Step (ιE d) (ιE d') := by
  obtain ⟨z, hz, hz'⟩ := h
  exact ⟨ιN z, hE.tgt_some hz, hE.src_some hz'⟩

theorem reflTransGen_step {d d' : EΩ} (h : ReflTransGen Ω.Step d d') :
    ReflTransGen X.Step (ιE d) (ιE d') := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ h ih => exact ih.tail (hE.step h)

theorem dupStep {d d' : EΩ} (h : Ω.DupStep Ω.val.IsDup d d') :
    X.DupStep X.val.IsDup (ιE d) (ιE d') := by
  obtain ⟨z, hDz, hz, hz'⟩ := h
  exact ⟨ιN z, (hE.isDup_iff z).2 hDz, hE.tgt_some hz, hE.src_some hz'⟩

theorem reflTransGen_step_dup {d d' : EΩ} (h : ReflTransGen (Ω.DupStep Ω.val.IsDup) d d') :
    ReflTransGen (X.DupStep X.val.IsDup) (ιE d) (ιE d') := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ h ih => exact ih.tail (hE.dupStep h)

/-- A directed path from an edge of `Ω` to the codomain of `X` leaves `Ω` through an edge of its
codomain. -/
theorem exit {d : EΩ} (h : X.ReachCod (ιE d)) :
    ∃ c, Ω.tgt c = none ∧ ReflTransGen Ω.Step d c ∧ X.ReachCod (ιE c) := by
  obtain ⟨c, hc, hc'⟩ := h
  suffices key : ∀ g, ReflTransGen X.Step g c → ∀ d, g = ιE d →
      ∃ c', Ω.tgt c' = none ∧ ReflTransGen Ω.Step d c' ∧ X.ReachCod (ιE c') from
    key _ hc d rfl
  intro g hg
  induction hg using ReflTransGen.head_induction_on with
  | refl =>
    rintro d rfl
    refine ⟨d, ?_, ReflTransGen.refl, PGraph.reachCod_of_tgt_none hc'⟩
    cases h : Ω.tgt d with
    | none => rfl
    | some z => rw [hE.tgt_some h] at hc'; cases hc'
  | @head a b hab hbc ih =>
    rintro d rfl
    cases hd : Ω.tgt d with
    | none => exact ⟨d, hd, ReflTransGen.refl, ⟨c, ReflTransGen.head hab hbc, hc'⟩⟩
    | some z =>
      obtain ⟨x, hx, hx'⟩ := hab
      rw [hE.tgt_some hd, Option.some.injEq] at hx
      subst hx
      obtain ⟨d', hd', rfl⟩ := hE.eq_of_src hx'
      obtain ⟨c', h₁, h₂, h₃⟩ := ih d' rfl
      exact ⟨c', h₁, ReflTransGen.head ⟨z, hd, hd'⟩ h₂, h₃⟩

/-- A chain through duplicates from an edge of `Ω` to an edge ending outside `Ω` leaves `Ω`
through an edge of its codomain. -/
theorem chain_exit {d : EΩ} {g : EX} (h : ReflTransGen (X.DupStep X.val.IsDup) (ιE d) g)
    (hg : ∀ z, X.tgt g ≠ some (ιN z)) :
    ∃ c, Ω.tgt c = none ∧ ReflTransGen (Ω.DupStep Ω.val.IsDup) d c ∧
      (ιE c = g ∨ ∃ f, (∀ z, X.src f ≠ some (ιN z)) ∧ X.DupStep X.val.IsDup (ιE c) f ∧
        ReflTransGen (X.DupStep X.val.IsDup) f g) := by
  suffices key : ∀ a, ReflTransGen (X.DupStep X.val.IsDup) a g → ∀ d, a = ιE d →
      ∃ c, Ω.tgt c = none ∧ ReflTransGen (Ω.DupStep Ω.val.IsDup) d c ∧
        (ιE c = g ∨ ∃ f, (∀ z, X.src f ≠ some (ιN z)) ∧ X.DupStep X.val.IsDup (ιE c) f ∧
          ReflTransGen (X.DupStep X.val.IsDup) f g) from key _ h d rfl
  intro a ha
  induction ha using ReflTransGen.head_induction_on with
  | refl =>
    rintro d rfl
    refine ⟨d, ?_, ReflTransGen.refl, Or.inl rfl⟩
    cases h : Ω.tgt d with
    | none => rfl
    | some z => exact (hg z (hE.tgt_some h)).elim
  | @head a b hab hbc ih =>
    rintro d rfl
    cases hd : Ω.tgt d with
    | none =>
      refine ⟨d, hd, ReflTransGen.refl, Or.inr ⟨b, fun z hz => ?_, hab, hbc⟩⟩
      obtain ⟨x, -, hx, hx'⟩ := hab
      rw [hx'] at hz
      rw [Option.some.injEq] at hz
      subst hz
      exact hE.tgt_none hd z hx
    | some z =>
      obtain ⟨x, hDx, hx, hx'⟩ := hab
      rw [hE.tgt_some hd, Option.some.injEq] at hx
      subst hx
      obtain ⟨d', hd', rfl⟩ := hE.eq_of_src hx'
      obtain ⟨c', h₁, h₂, h₃⟩ := ih d' rfl
      exact ⟨c', h₁, ReflTransGen.head ⟨z, (hE.isDup_iff z).1 hDx, hd, hd'⟩ h₂, h₃⟩

end Emb

/-! ### Consequences of the canonical description -/

namespace CanonProj

variable (P : CanonProj X Ω ιN ιE α β Y)
include P

theorem mem_ins_iff (n : NY) (e : EY) :
    e ∈ Y.ins n ↔ P.pE e ∈ canonIns X ιE α β (P.pN n) := by
  rw [← P.ins, List.mem_map_of_injective P.pE_inj]

theorem mem_outs_iff (n : NY) (e : EY) :
    e ∈ Y.outs n ↔ P.pE e ∈ canonOuts X ιE α (P.pN n) := by
  rw [← P.outs, List.mem_map_of_injective P.pE_inj]

theorem mem_cod_iff (e : EY) : e ∈ Y.cod ↔ P.pE e ∈ X.cod.map (canonF ιE α β) := by
  rw [← P.cod, List.mem_map_of_injective P.pE_inj]

theorem mem_dom_iff (e : EY) : e ∈ Y.dom ↔ P.pE e ∈ X.dom.map .inl := by
  rw [← P.dom, List.mem_map_of_injective P.pE_inj]

theorem exists_edge {t : EX ⊕ Λ.InnerSrc} (ht : CanonEdge ιE Ω.toPGraph t) : ∃ e, P.pE e = t :=
  (P.pE_range t).2 ht

theorem exists_node {t : NX ⊕ NΛ} (ht : CanonNode ιN t) : ∃ n, P.pN n = t :=
  (P.pN_range t).2 ht

theorem isDup_iff (n : NY) : Y.val.IsDup n ↔
    Sum.elim (fun x => X.val.IsDup x) (fun z => Λ.val.IsDup z) (P.pN n) := by
  unfold Valuation.IsDup
  rw [P.v₁]
  rcases P.pN n with x | z <;> rfl

/-- Consecutive edges at a canonical node give consecutive edges of `Y`. -/
theorem step_of_canon {c : NX ⊕ NΛ} (hc : CanonNode ιN c) {e e' : EY}
    (he : P.pE e ∈ canonIns X ιE α β c) (he' : P.pE e' ∈ canonOuts X ιE α c) : Y.Step e e' := by
  obtain ⟨n, rfl⟩ := P.exists_node hc
  exact Y.step_of_mem ((P.mem_ins_iff n e).2 he) ((P.mem_outs_iff n e').2 he')

theorem dupStep_of_canon {c : NX ⊕ NΛ} (hc : CanonNode ιN c)
    (hD : Sum.elim (fun x => X.val.IsDup x) (fun z => Λ.val.IsDup z) c) {e e' : EY}
    (he : P.pE e ∈ canonIns X ιE α β c) (he' : P.pE e' ∈ canonOuts X ιE α c) :
    Y.DupStep Y.val.IsDup e e' := by
  obtain ⟨n, rfl⟩ := P.exists_node hc
  obtain ⟨y, hy, hy'⟩ := Y.step_of_mem ((P.mem_ins_iff n e).2 he) ((P.mem_outs_iff n e').2 he')
  refine ⟨y, ?_, hy, hy'⟩
  have : n = y := by
    have := (Y.mem_ins n e).1 ((P.mem_ins_iff n e).2 he)
    rw [hy, Option.some.injEq] at this
    exact this.symm
  subst this
  exact (P.isDup_iff n).2 hD

end CanonProj

theorem canonEdge_canonG (hE : Emb X Ω ιN ιE) (d : EΛ) : CanonEdge ιE Ω.toPGraph (canonG ιE α d) := by
  by_cases h : Λ.src d = none
  · rw [canonG_of_src_eq_none ιE α h]
    intro d' hd' heq
    have := hE.injE heq
    subst this
    exact hd' (α ⟨d, h⟩).2
  · rw [canonG_of_src_ne_none ιE α h]
    trivial

theorem canonEdge_inl (hE : Emb X Ω ιN ιE) {f : EX} (hf : ∀ z, X.src f ≠ some (ιN z)) :
    CanonEdge ιE Ω.toPGraph (.inl f : EX ⊕ Λ.InnerSrc) := by
  intro d hd heq
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hd
  exact hf z (heq ▸ hE.src_some hz)

theorem canonNode_inl {x : NX} (hx : ∀ z, ιN z ≠ x) : CanonNode ιN (.inl x : NX ⊕ NΛ) := hx

theorem canonNode_inr (z : NΛ) : CanonNode ιN (.inr z : NX ⊕ NΛ) := trivial

theorem canonF_of_not_mem {f : EX} (hf : ∀ d, ιE d ≠ f) : canonF ιE α β f = .inl f :=
  canonF_of_not ιE α β fun d => hf d.1

/-- Directed paths in `Λ` give directed paths in `Y`. -/
theorem lam_reflTransGen (hE : Emb X Ω ιN ιE) (P : CanonProj X Ω ιN ιE α β Y) {d d' : EΛ}
    (h : ReflTransGen Λ.Step d d') {e e' : EY} (he : P.pE e = canonG ιE α d)
    (he' : P.pE e' = canonG ιE α d') : ReflTransGen Y.Step e e' := by
  induction h generalizing e' with
  | refl => rw [← he] at he'; rw [P.pE_inj he']
  | @tail b c _ hbc ih =>
    obtain ⟨eb, heb⟩ := P.exists_edge (canonEdge_canonG (α := α) hE b)
    refine (ih heb).tail ?_
    obtain ⟨z, hz, hz'⟩ := hbc
    refine P.step_of_canon (canonNode_inr z) ?_ ?_
    · rw [heb]
      exact List.mem_map_of_mem ((Λ.mem_ins z b).2 hz)
    · rw [he']
      exact List.mem_map_of_mem ((Λ.mem_outs z c).2 hz')

/-- Chains through duplicates in `Λ` give chains through duplicates in `Y`. -/
theorem lam_reflTransGen_dup (hE : Emb X Ω ιN ιE) (P : CanonProj X Ω ιN ιE α β Y) {d d' : EΛ}
    (h : ReflTransGen (Λ.DupStep Λ.val.IsDup) d d') {e e' : EY} (he : P.pE e = canonG ιE α d)
    (he' : P.pE e' = canonG ιE α d') : ReflTransGen (Y.DupStep Y.val.IsDup) e e' := by
  induction h generalizing e' with
  | refl => rw [← he] at he'; rw [P.pE_inj he']
  | @tail b c _ hbc ih =>
    obtain ⟨eb, heb⟩ := P.exists_edge (canonEdge_canonG (α := α) hE b)
    refine (ih heb).tail ?_
    obtain ⟨z, hDz, hz, hz'⟩ := hbc
    refine P.dupStep_of_canon (canonNode_inr z) hDz ?_ ?_
    · rw [heb]
      exact List.mem_map_of_mem ((Λ.mem_ins z b).2 hz)
    · rw [he']
      exact List.mem_map_of_mem ((Λ.mem_outs z c).2 hz')

/-! ### The conditions on a template -/

variable (Ω Λ α β) in
/-- The conditions on a template used in the proof of Lemma 4.3: no node of `Ω` whose value is not
a duplicate has an output reaching the codomain of `Ω`, and directed paths and chains through
duplicates from the domain to the codomain of `Ω` have counterparts in `Λ`. -/
structure StepCond : Prop where
  live : ∀ z, Ω.val.IsDup z ∨ ∀ d ∈ Ω.outs z, ¬ Ω.toPGraph.ReachCod d
  path : ∀ (b : {e // Ω.IsDom e}) (c : {e // Ω.IsCod e}), ReflTransGen Ω.Step b.1 c.1 →
    ReflTransGen Λ.Step (α.symm b).1 (β.symm c).1
  chain : ∀ (b : {e // Ω.IsDom e}) (c : {e // Ω.IsCod e}),
    ReflTransGen (Ω.DupStep Ω.val.IsDup) b.1 c.1 →
      ReflTransGen (Λ.DupStep Λ.val.IsDup) (α.symm b).1 (β.symm c).1

variable (hE : Emb X Ω ιN ιE) (P : CanonProj X Ω ιN ιE α β Y) (hC : StepCond Ω Λ α β)
include hE P hC

/-- **Rerouting directed paths through `Λ`.** An edge of `X` starting outside `Ω` that reaches
the codomain gives an edge of `Y` reaching the codomain. -/
theorem reach_forward [Finite EX] (f : EX) (hf : ∀ z, X.src f ≠ some (ιN z)) (h : X.ReachCod f)
    {e : EY} (he : P.pE e = .inl f) : Y.ReachCod e := by
  induction f using X.wellFounded_down.induction generalizing e with
  | _ f ih =>
    -- continuing from an edge `g` of `X` ending outside `Ω`, whose image in `Y` is `canonF g`
    have cont : ∀ g, (∀ z, X.tgt g ≠ some (ιN z)) → X.ReachCod g → ReflTransGen X.Step f g →
        ∀ e₂, P.pE e₂ = canonF ιE α β g → Y.ReachCod e₂ := by
      intro g hg hgc hfg e₂ he₂
      cases hgt : X.tgt g with
      | none =>
        exact PGraph.reachCod_of_tgt_none ((Y.mem_cod e₂).1 ((P.mem_cod_iff e₂).2
          (he₂ ▸ List.mem_map_of_mem ((X.mem_cod g).2 hgt))))
      | some x =>
        obtain (h' | ⟨x', hx', f', hf', hf'c⟩) := (PGraph.reachCod_iff g).1 hgc
        · rw [hgt] at h'; cases h'
        rw [hgt, Option.some.injEq] at hx'
        subst hx'
        have hxo : ∀ z, ιN z ≠ x := fun z hz => hg z (hz ▸ hgt)
        have hf'o : ∀ z, X.src f' ≠ some (ιN z) := fun z hz => hxo z (by
          rw [(X.mem_outs x f').1 hf', Option.some.injEq] at hz; exact hz.symm)
        obtain ⟨e', he'⟩ := P.exists_edge (canonEdge_inl hE hf'o)
        have hst : Y.Step e₂ e' := P.step_of_canon (canonNode_inl hxo)
          (by rw [he₂]; exact List.mem_map_of_mem ((X.mem_ins x g).2 hgt))
          (by rw [he']; exact List.mem_map_of_mem hf')
        exact (ih f' (TransGen.tail' hfg ⟨x, hgt, (X.mem_outs x f').1 hf'⟩) hf'o hf'c he').of_step hst
    by_cases him : ∃ b, ιE b = f
    · obtain ⟨b, rfl⟩ := him
      have hb : Ω.src b = none := by
        cases hbs : Ω.src b with
        | none => rfl
        | some z => exact (hf z (hE.src_some hbs)).elim
      obtain ⟨c, hc, hbc, hcc⟩ := hE.exit h
      have hΛ := hC.path ⟨b, hb⟩ ⟨c, hc⟩ hbc
      obtain ⟨e₂, he₂⟩ := P.exists_edge (canonEdge_canonG (α := α) hE (β.symm ⟨c, hc⟩).1)
      have hpath := lam_reflTransGen hE P hΛ (e := e) (e' := e₂)
        (by rw [he, canonG_of_src_eq_none ιE α (α.symm ⟨b, hb⟩).2]; simp) he₂
      rw [← canonF_of_cod ιE α β hE.injE ⟨c, hc⟩] at he₂
      exact (cont (ιE c) (hE.tgt_none hc) hcc (hE.reflTransGen_step hbc) e₂ he₂).of_reflTransGen hpath
    · push Not at him
      have hfo : ∀ z, X.tgt f ≠ some (ιN z) := fun z hz => by
        obtain ⟨d, -, hd⟩ := hE.eq_of_tgt hz
        exact him d hd
      exact cont f hfo h ReflTransGen.refl e (by rw [he, canonF_of_not_mem him])

omit P in
/-- **The live nodes of `X` lie outside `Ω`.** -/
theorem live_outside [Finite EX] {x : NX} (hx : X.Live x) (z : NΩ) : ιN z ≠ x := by
  rintro rfl
  obtain ⟨hD, f, hf, hfc⟩ := hx
  obtain ⟨d, hd, rfl⟩ := hE.eq_of_src ((X.mem_outs _ f).1 hf)
  obtain ⟨c, hc, hdc, -⟩ := hE.exit hfc
  rcases hC.live z with h | h
  · exact hD ((hE.isDup_iff z).2 h)
  · exact h d ((Ω.mem_outs z d).2 hd) ⟨c, hdc, hc⟩

/-- **Live nodes are kept.** -/
theorem live_forward [Finite EX] {x : NX} (hx : X.Live x) {n : NY} (hn : P.pN n = .inl x) :
    Y.Live n := by
  obtain ⟨hD, f, hf, hfc⟩ := hx
  have hxo := live_outside hE hC ⟨hD, f, hf, hfc⟩
  have hfo : ∀ z, X.src f ≠ some (ιN z) := fun z hz => hxo z (by
    rw [(X.mem_outs x f).1 hf, Option.some.injEq] at hz; exact hz.symm)
  obtain ⟨e, he⟩ := P.exists_edge (canonEdge_inl hE hfo)
  refine ⟨fun h => hD ?_, e, (P.mem_outs_iff n e).2 ?_, reach_forward hE P hC f hfo hfc he⟩
  · rw [P.isDup_iff, hn] at h; exact h
  · rw [hn, he]; exact List.mem_map_of_mem hf

omit P in
/-- The origin of an edge reaching the codomain starts outside `Ω`. -/
theorem origin_outside [Finite EX] {q g : EX} (hq : X.IsOrigin q g) (hg : X.ReachCod g) (z : NΩ) :
    X.src q ≠ some (ιN z) := by
  intro hz
  obtain ⟨d, hd, rfl⟩ := hE.eq_of_src hz
  have hqc : X.ReachCod (ιE d) := hg.of_reflTransGen (PGraph.reflTransGen_step_of_dup hq.1)
  obtain ⟨c, hc, hdc, -⟩ := hE.exit hqc
  rcases hC.live z with h | h
  · exact hq.2 _ hz ((hE.isDup_iff z).2 h)
  · exact h d ((Ω.mem_outs z d).2 hd) ⟨c, hdc, hc⟩

/-- **Following edges backward through duplicates.** A chain through duplicates in `X` from an
edge starting outside `Ω` to an edge ending outside `Ω` gives a chain in `Y`. -/
theorem chain_forward [Finite EX] (h : EX) (hh : ∀ z, X.src h ≠ some (ιN z)) {g : EX}
    (hg : ∀ z, X.tgt g ≠ some (ιN z)) (hhg : ReflTransGen (X.DupStep X.val.IsDup) h g)
    {e₁ e₂ : EY} (he₁ : P.pE e₁ = .inl h) (he₂ : P.pE e₂ = canonF ιE α β g) :
    ReflTransGen (Y.DupStep Y.val.IsDup) e₁ e₂ := by
  induction h using X.wellFounded_down.induction generalizing e₁ with
  | _ h ih =>
    -- one step at a node outside `Ω`, then continue
    have cont : ∀ (a f : EX) (ea : EY), (∀ z, X.src f ≠ some (ιN z)) →
        P.pE ea = canonF ιE α β a → X.DupStep X.val.IsDup a f → ReflTransGen X.Step h a →
        ReflTransGen (X.DupStep X.val.IsDup) f g → ReflTransGen (Y.DupStep Y.val.IsDup) ea e₂ := by
      intro a f ea hf hea haf hha hfg
      obtain ⟨x, hDx, hx, hx'⟩ := haf
      have hxo : ∀ z, ιN z ≠ x := fun z hz => hf z (hz ▸ hx')
      obtain ⟨ef, hef⟩ := P.exists_edge (canonEdge_inl hE hf)
      have hst : Y.DupStep Y.val.IsDup ea ef := P.dupStep_of_canon (canonNode_inl hxo) hDx
        (by rw [hea]; exact List.mem_map_of_mem ((X.mem_ins x a).2 hx))
        (by rw [hef]; exact List.mem_map_of_mem ((X.mem_outs x f).2 hx'))
      exact ReflTransGen.head hst (ih f (TransGen.tail' hha ⟨x, hx, hx'⟩) hf hfg hef)
    by_cases him : ∃ b, ιE b = h
    · obtain ⟨b, rfl⟩ := him
      have hb : Ω.src b = none := by
        cases hbs : Ω.src b with
        | none => rfl
        | some z => exact (hh z (hE.src_some hbs)).elim
      obtain ⟨c, hc, hbc, hcont⟩ := hE.chain_exit hhg hg
      have hΛ := hC.chain ⟨b, hb⟩ ⟨c, hc⟩ hbc
      obtain ⟨e₃, he₃⟩ := P.exists_edge (canonEdge_canonG (α := α) hE (β.symm ⟨c, hc⟩).1)
      have hch := lam_reflTransGen_dup hE P hΛ (e := e₁) (e' := e₃)
        (by rw [he₁, canonG_of_src_eq_none ιE α (α.symm ⟨b, hb⟩).2]; simp) he₃
      rw [← canonF_of_cod ιE α β hE.injE ⟨c, hc⟩] at he₃
      refine hch.trans ?_
      rcases hcont with rfl | ⟨f, hf, hcf, hfg⟩
      · rw [← he₂] at he₃; rw [P.pE_inj he₃]
      · exact cont (ιE c) f e₃ hf he₃ hcf
          (PGraph.reflTransGen_step_of_dup (hE.reflTransGen_step_dup hbc)) hfg
    · push Not at him
      rw [← canonF_of_not_mem (α := α) (β := β) him] at he₁
      rcases hhg.cases_head with rfl | ⟨f, hhf, hfg⟩
      · rw [← he₂] at he₁; rw [P.pE_inj he₁]
      · refine cont h f e₁ (fun z hz => ?_) he₁ hhf ReflTransGen.refl hfg
        obtain ⟨x, -, hx, hx'⟩ := hhf
        rw [hx', Option.some.injEq] at hz
        subst hz
        obtain ⟨d, -, hd⟩ := hE.eq_of_tgt hx
        exact him d hd

/-- **Origins of consumers are kept.** -/
theorem origin_forward [Finite EX] {q g : EX} (hq : X.IsOrigin q g) (hgc : X.ReachCod g)
    (hg : ∀ z, X.tgt g ≠ some (ιN z)) {e₁ e₂ : EY} (he₁ : P.pE e₁ = .inl q)
    (he₂ : P.pE e₂ = canonF ιE α β g) : Y.IsOrigin e₁ e₂ := by
  refine ⟨chain_forward hE P hC q (origin_outside hE hC hq hgc) hg hq.1 he₁ he₂, ?_⟩
  intro n hn hD
  have hmem := (P.mem_outs_iff n e₁).1 ((Y.mem_outs n e₁).2 hn)
  rw [he₁] at hmem
  rw [P.isDup_iff] at hD
  rcases hpn : P.pN n with x | z
  · rw [hpn] at hmem hD
    obtain ⟨q', hq', hqq⟩ := List.mem_map.1 hmem
    rw [Sum.inl.injEq] at hqq
    subst hqq
    exact hq.2 x ((X.mem_outs x _).1 hq') hD
  · rw [hpn] at hmem
    obtain ⟨d, hd, hdq⟩ := List.mem_map.1 hmem
    have hds : Λ.src d = some z := (Λ.mem_outs z d).1 hd
    rw [canonG_of_src_ne_none ιE α (by rw [hds]; exact Option.some_ne_none _)] at hdq
    cases hdq

end Analysis

end Diagram

end FreeMarkov
