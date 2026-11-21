/-
Free Markov categories, Stage 4: surgeries at embedded templates.

* `rangeSub`: the subgraph formed by the image of an embedding.
* `Emb.isNormal_of_root`: a criterion for this subgraph to be normal (Definition 3.1): every
  node of the image is reached from a root node of the image, every other node of the image has
  all its inputs from nodes of the image, and `Ω` has no loose edges.
* `Emb.tStep`: a template `τ ∈ T` whose `Ω` embeds as a normal subgraph gives a `T`-surgery
  step, with the canonical description of its result.
-/
module

public import FreeMarkov.Stage4.Embed

@[expose] public section

universe w v u u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S}
  {NX : Type u₁} {EX : Type u₂} {X : Diagram G.toFreeGraphMonoid NX EX}

theorem PEmb.toEmb {N : Type u₃} {E : Type u₄} {D : Diagram G.toFreeGraphMonoid N E}
    (e : PEmb D X) : Emb X D.toPDiagram e.ιN e.ιE :=
  ⟨e.injN, e.injE, e.ins, e.outs, e.v₀, e.v₁⟩

variable {NΩ : Type u₃} {EΩ : Type u₄} {Ω : PDiagram G.toFreeGraphMonoid NΩ EΩ}
  {ιN : NΩ → NX} {ιE : EΩ → EX}

/-- The image of an embedding, as a subgraph. -/
def rangeSub (ιN : NΩ → NX) (ιE : EΩ → EX) : Subgraph NX EX :=
  ⟨fun x => ∃ z, ιN z = x, fun e => ∃ d, ιE d = e⟩

namespace Emb

variable (hE : Emb X Ω ιN ιE)
include hE

theorem edgeAt : X.EdgeAt (rangeSub ιN ιE) := by
  rintro x ⟨z, rfl⟩ e (h | h)
  · obtain ⟨d, -, hd⟩ := hE.eq_of_src h
    exact ⟨d, hd⟩
  · obtain ⟨d, -, hd⟩ := hE.eq_of_tgt h
    exact ⟨d, hd⟩

omit hE in
/-- The nodes between the root and a node of the image are in the image. -/
theorem mem_of_between {z₀ : NΩ}
    (hin : ∀ z, z ≠ z₀ → ∀ e ∈ X.ins (ιN z), ∃ z', X.src e = some (ιN z')) {n y : NX}
    (hy : ∃ z, ιN z = y) (hn : X.Le (ιN z₀) n) (hny : X.Lt n y) : ∃ z, ιN z = n := by
  revert hy
  induction hny with
  | single h =>
    intro hy
    obtain ⟨e, he₁, he₂⟩ := h
    obtain ⟨z, rfl⟩ := hy
    by_cases hz : z = z₀
    · subst hz
      exact (X.lt_irrefl _ (hn.trans_lt (X.lt_of_edge he₁ he₂))).elim
    · obtain ⟨z', hz'⟩ := hin z hz e ((X.mem_ins _ e).2 he₂)
      rw [he₁, Option.some.injEq] at hz'
      exact ⟨z', hz'.symm⟩
  | @tail m y' hnm hm ih =>
    intro hy
    obtain ⟨e, he₁, he₂⟩ := hm
    obtain ⟨z, rfl⟩ := hy
    by_cases hz : z = z₀
    · subst hz
      exact (X.lt_irrefl _ (hn.trans_lt (hnm.tail ⟨e, he₁, he₂⟩))).elim
    · obtain ⟨z', hz'⟩ := hin z hz e ((X.mem_ins _ e).2 he₂)
      rw [he₁, Option.some.injEq] at hz'
      exact ih ⟨z', hz'.symm⟩

/-- **A criterion for normality.** -/
theorem isNormal_of_root (z₀ : NΩ) (hroot : ∀ z, X.Le (ιN z₀) (ιN z))
    (hin : ∀ z, z ≠ z₀ → ∀ e ∈ X.ins (ιN z), ∃ z', X.src e = some (ιN z'))
    (hloose : ∀ d, Ω.src d ≠ none ∨ Ω.tgt d ≠ none) : X.IsNormal (rangeSub ιN ιE) where
  path_loose p _ e _ _ _ _ he _ hl := by
    rw [PGraph.sub_isLoose_iff_looseIn] at hl
    obtain ⟨d, rfl⟩ := he
    rcases hloose d with h | h
    · obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 h
      exact hl.1 _ (hE.src_some hz) ⟨z, rfl⟩
    · obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 h
      exact hl.2 _ (hE.tgt_some hz) ⟨z, rfl⟩
  edge_at := hE.edgeAt
  path_mem p hp x y hx hy hxA hyA e he := by
    obtain ⟨⟨z, hz, hxz⟩, ⟨z', hz', hz'y⟩⟩ := X.toPGraph.src_tgt_of_mem_path hp hx hy he
    have hr : ∀ n, X.Le x n → X.Le n y → ∃ w, ιN w = n := by
      intro n hxn hny
      obtain ⟨w, rfl⟩ := hxA
      rcases hny with hny | rfl
      · exact mem_of_between hin hyA ((hroot w).trans hxn) hny
      · exact hyA
    have hzz' : X.Le z z' := Or.inl (X.lt_of_edge hz hz')
    have hzA := hr z hxz (hzz'.trans hz'y)
    refine ⟨hE.edgeAt z hzA e (Or.inl hz), fun w hw => ?_, fun w hw => ?_⟩
    · rw [hz, Option.some.injEq] at hw; exact hw ▸ hzA
    · rw [hz', Option.some.injEq] at hw
      subst hw
      exact hr _ (hxz.trans hzz') hz'y

/-- The isomorphism of `Ω` with the image of an embedding. -/
noncomputable def isoSub (h : X.EdgeAt (rangeSub ιN ιE)) :
    Ω.Iso (X.subD (rangeSub ιN ιE) h) :=
  PDiagram.Iso.ofProj ιN ιE Subtype.val Subtype.val hE.injN Subtype.val_injective hE.injE
    Subtype.val_injective (fun t => ⟨fun ⟨z, hz⟩ => ⟨⟨t, z, hz⟩, rfl⟩, fun ⟨n, hn⟩ => hn ▸ n.2⟩)
    (fun t => ⟨fun ⟨d, hd⟩ => ⟨⟨t, d, hd⟩, rfl⟩, fun ⟨e, he⟩ => he ▸ e.2⟩)
    (fun z n hzn => by
      rw [← hE.ins, hzn]
      exact (PGraph.sub_ins_map_val n fun e he => h _ n.2 e (Or.inr ((X.mem_ins _ e).1 he))).symm)
    (fun z n hzn => by
      rw [← hE.outs, hzn]
      exact (PGraph.sub_outs_map_val n fun e he => h _ n.2 e (Or.inl ((X.mem_outs _ e).1 he))).symm)
    (fun d e hde => by rw [← hE.v₀, hde]; rfl)
    (fun z n hzn => by rw [← hE.v₁, hzn]; rfl)

theorem isoSub_eN (h : X.EdgeAt (rangeSub ιN ιE)) (z : NΩ) : ((hE.isoSub h).eN z).1 = ιN z :=
  equivOfProj_spec ιN Subtype.val hE.injN Subtype.val_injective _ z

theorem isoSub_eE (h : X.EdgeAt (rangeSub ιN ιE)) (d : EΩ) : ((hE.isoSub h).eE d).1 = ιE d :=
  equivOfProj_spec ιE Subtype.val hE.injE Subtype.val_injective _ d

end Emb

/-- **A surgery at an embedded template.** If `Ω` of a template `τ ∈ T` embeds as a normal
subgraph, the surgery is a `T`-surgery step and its result has the canonical description given
by the embedding. -/
theorem Emb.tStep {T : Set (Template.{u} G.toFreeGraphMonoid)} {τ : Template.{u} G.toFreeGraphMonoid}
    (hτ : τ ∈ T) {ιN : τ.NΩ → NX} {ιE : τ.EΩ → EX} (hE : Emb X τ.Ω ιN ιE)
    (hA : X.IsNormal (rangeSub ιN ιE)) :
    ∃ (NY : Type (max u u₁)) (EY : Type (max u u₂)) (Y : Diagram G.toFreeGraphMonoid NY EY),
      TStep T X Y ∧ Nonempty (CanonProj X τ.Ω ιN ιE τ.α τ.β Y) := by
  refine ⟨_, _, X.surgery τ.α τ.β τ.hα τ.hβ hA (hE.isoSub hA.edge_at),
    ⟨τ, hτ, _, hA, hE.isoSub hA.edge_at, ⟨Iso.refl _⟩⟩, ⟨?_⟩⟩
  exact X.surgeryAt_canonProj hA.sharpLayer _ τ.α τ.β τ.hα τ.hβ (hE.isoSub_eN hA.edge_at)
    (hE.isoSub_eE hA.edge_at)

end Diagram

end FreeMarkov
