/-
Free Markov categories, Stage 4: **Lemma 4.3**.

"Suppose that `(Γ, v)`, `(Υ, w)` are anchored diagrams belonging to the same `S_M`-congruence
class. Then they have the same skeleton, say, via the bijection `π`. Consequently,
* `π` extends to a bijection `Δ̃_Γ → Δ̃_Υ` compatible with the valuations ...;
* for all live nodes `x`, `y` of `Γ`, there is a directed path in `Γ` from `x` to `y` if and only
  if there is one in `Υ` from `π(x)` to `π(y)`, and the same holds for the directed paths that
  begin with the `i`-th edge in the domain instead of beginning at `x`, `π(x)`, or end with the
  `j`-th edge in the codomain instead of ending at `y`, `π(y)`;
* the same holds for the splitter paths between two ends each of which is a live node or an
  edge in the codomain."

`lemma_4_3` is the whole statement; `lemma_4_3_sameSkeleton` its first sentence, and
`skeletonIso_items` the three items for any skeleton bijection.  No cited result is used.
-/
module

public import FreeMarkov.Stage4.TemplateFacts

@[expose] public section

universe w v u₁ u₂ u₃ u₄ u₅ u₆

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄} {N'' : Type u₅} {E'' : Type u₆}
  {Γ : Diagram G.toFreeGraphMonoid N E} {Υ : Diagram G.toFreeGraphMonoid N' E'}
  {Θ : Diagram G.toFreeGraphMonoid N'' E''}

/-! ### "Have the same skeleton" is an equivalence relation -/

theorem OriginsMatch.trans {π : {x // Γ.Live x} ≃ {y // Υ.Live y}}
    {π' : {x // Υ.Live x} ≃ {y // Θ.Live y}} {e : E} {e' : E'} {e'' : E''}
    (h : OriginsMatch π e e') (h' : OriginsMatch π' e' e'') : OriginsMatch (π.trans π') e e'' :=
  ⟨fun j => (h.1 j).trans (h'.1 j), fun y j => (h.2 y j).trans (h'.2 (π y) j)⟩

theorem SkeletonIso.trans (hc : Υ.codWord = Θ.codWord) {π : {x // Γ.Live x} ≃ {y // Υ.Live y}}
    {π' : {x // Υ.Live x} ≃ {y // Θ.Live y}} (h : SkeletonIso Γ Υ π) (h' : SkeletonIso Υ Θ π') :
    SkeletonIso Γ Θ (π.trans π') where
  val_eq x := (h'.val_eq (π x)).trans (h.val_eq x)
  cod_match i e e'' he he'' := by
    obtain ⟨e', he'⟩ := exists_getElem?_of_length_eq (cod_length_eq_of_codWord hc).symm he''
    exact (h.cod_match i e e' he he').trans (h'.cod_match i e' e'' he' he'')
  ins_match x i e e'' he he'' := by
    obtain ⟨e', he'⟩ := exists_getElem?_of_length_eq
      (ins_length_eq_of_val (h'.val_eq (π x))) he''
    exact (h.ins_match x i e e' he he').trans (h'.ins_match (π x) i e' e'' he' he'')

theorem SameSkeleton.trans (h : SameSkeleton Γ Υ) (h' : SameSkeleton Υ Θ) : SameSkeleton Γ Θ := by
  obtain ⟨hd, hc, π, hπ⟩ := h
  obtain ⟨hd', hc', π', hπ'⟩ := h'
  exact ⟨hd.trans hd', hc.trans hc', _, hπ.trans hc' hπ'⟩

/-! ### Markov surgeries keep the skeleton -/

theorem TStep.sameSkeleton_markov [Finite N] [Finite E] [Finite N'] [Finite E']
    (h : TStep G.markovTemplates Γ Υ) : SameSkeleton Γ Υ :=
  h.sameSkeleton G.markovTemplates_stepCond G.markovTemplates_isSymmetric.symm_mem

/-- **Isomorphic diagrams have the same skeleton.** -/
theorem Iso.sameSkeleton [Finite N] [Finite E] [Finite N'] [Finite E'] (i : Γ.Iso Υ) :
    SameSkeleton Γ Υ :=
  (TStep.of_iso G.markovTemplates_isSymmetric.empty_mem i).sameSkeleton_markov

theorem SameSkeleton.refl [Finite N] [Finite E] (Γ : Diagram G.toFreeGraphMonoid N E) :
    SameSkeleton Γ Γ :=
  (Iso.refl Γ).sameSkeleton

theorem TEquiv.sameSkeleton {a b : FinDiag G.toFreeGraphMonoid} (h : TEquiv G.markovTemplates a b) :
    SameSkeleton a.2 b.2 := by
  induction h with
  | refl => exact SameSkeleton.refl _
  | tail _ h ih => exact ih.trans h.sameSkeleton_markov

/-- **Lemma 4.3, first sentence.** Anchored diagrams in the same `S_M`-congruence class have the
same skeleton. -/
theorem lemma_4_3_sameSkeleton [Finite N] [Finite E] [Finite N'] [Finite E']
    (h : SRel G.markovTemplates (DClass.mk Γ) (DClass.mk Υ)) : SameSkeleton Γ Υ := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  obtain ⟨i⟩ := (Quotient.exact ha : Nonempty (a.2.Iso Γ.toFin))
  obtain ⟨j⟩ := (Quotient.exact hb : Nonempty (b.2.Iso Υ.toFin))
  exact (Γ.isoToFin.trans i.symm).sameSkeleton.trans
    ((TEquiv.sameSkeleton hab).trans (j.trans Υ.isoToFin.symm).sameSkeleton)

/-! ### The three items -/

/-- **The three items of Lemma 4.3** hold for every skeleton bijection `π`. -/
theorem skeletonIso_items [Finite N] [Finite E] [Finite N'] [Finite E']
    (hd : Γ.domWord = Υ.domWord) (hc : Γ.codWord = Υ.codWord) {π : {x // Γ.Live x} ≃ {y // Υ.Live y}}
    (h : SkeletonIso Γ Υ π) :
    (∃ π' : {x // ¬ Γ.QuasiTerminal x} ≃ {y // ¬ Υ.QuasiTerminal y},
      (∀ x, Υ.val.v₁ (π' x).1 = Γ.val.v₁ x.1) ∧
        ∀ x : {x // Γ.Live x}, (π' ⟨x.1, x.2.not_quasiTerminal⟩).1 = (π x).1) ∧
    (∀ s t : PEnd {x // Γ.Live x}, Γ.toAGraph.HasPath (s.map Subtype.val) (t.map Subtype.val) ↔
      Υ.toAGraph.HasPath (liftEnd π s) (liftEnd π t)) ∧
    (∀ t t' : PEnd {x // Γ.Live x},
      Γ.toAGraph.HasSplitter (t.map Subtype.val) (t'.map Subtype.val) ↔
        Υ.toAGraph.HasSplitter (liftEnd π t) (liftEnd π t')) :=
  ⟨exists_tilde_of_skeletonIso hd hc h, hasPath_iff_of_skeletonIso hc h,
    hasSplitter_iff_of_skeletonIso hc h⟩

/-- **Lemma 4.3.** If `(Γ, v)`, `(Υ, w)` belong to the same `S_M`-congruence class, they have the
same skeleton via a bijection `π` of live nodes, and:
* `π` extends to a bijection `Δ̃_Γ → Δ̃_Υ` compatible with the valuations;
* directed paths between live nodes, `i`-th edges of the domain (at the start) and `j`-th edges of
  the codomain (at the end) exist in `Γ` iff they exist in `Υ` between the corresponding ends;
* the same for splitter paths between two ends that are live nodes or edges of the codomain.

Ends are `PEnd {x // Γ.Live x}`: `.node x` for a live node, `.edge i` for the `i`-th edge of the
domain (start) or of the codomain (end); `liftEnd π` carries them to `Υ`. -/
theorem lemma_4_3 [Finite N] [Finite E] [Finite N'] [Finite E']
    (h : SRel G.markovTemplates (DClass.mk Γ) (DClass.mk Υ)) :
    Γ.domWord = Υ.domWord ∧ Γ.codWord = Υ.codWord ∧
      ∃ π : {x // Γ.Live x} ≃ {y // Υ.Live y}, SkeletonIso Γ Υ π ∧
        (∃ π' : {x // ¬ Γ.QuasiTerminal x} ≃ {y // ¬ Υ.QuasiTerminal y},
          (∀ x, Υ.val.v₁ (π' x).1 = Γ.val.v₁ x.1) ∧
            ∀ x : {x // Γ.Live x}, (π' ⟨x.1, x.2.not_quasiTerminal⟩).1 = (π x).1) ∧
        (∀ s t : PEnd {x // Γ.Live x}, Γ.toAGraph.HasPath (s.map Subtype.val) (t.map Subtype.val) ↔
          Υ.toAGraph.HasPath (liftEnd π s) (liftEnd π t)) ∧
        (∀ t t' : PEnd {x // Γ.Live x},
          Γ.toAGraph.HasSplitter (t.map Subtype.val) (t'.map Subtype.val) ↔
            Υ.toAGraph.HasSplitter (liftEnd π t) (liftEnd π t')) := by
  obtain ⟨hd, hc, π, hπ⟩ := lemma_4_3_sameSkeleton h
  exact ⟨hd, hc, π, hπ, skeletonIso_items hd hc hπ⟩

end Diagram

end FreeMarkov
