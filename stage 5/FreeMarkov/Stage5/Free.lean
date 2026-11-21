/-
Free Markov categories, Stage 5: tools in the free Markov category `F_s(G)/S_M` of Theorem 4.1.

* `JoyalStreet.lift J f hf`: the strict Markov functor `F_s(G)/S_M → D` that Theorem 4.1 gives for
  a graph monoid homomorphism `f : G → D` matching duplicates and discards, with its values on
  words and generators and its uniqueness.
* `ProdSig.toHom`: the graph monoid homomorphism `Q.G → D` given by objects for the letters and
  morphisms for the producers.
* `ProdSig.projM_eq_of_card`: two morphisms of `F_s(Q.G)` with the same domain (without repeated
  letters), satisfying the label conditions and with the same number of nodes of each producer,
  have the same image in `F_s(Q.G)/S_M` (label coherence and Lemma 4.4).
* `ProdSig.free X`: the free `DD`-graph monoid with letters `X` whose only arrows are the
  duplicates and the discards; `ProdSig.free_hom_eq`: in its free Markov category there is at
  most one morphism from a word without repeated letters to any word.

The cited result C1 enters through the free Markov category `J.FsM` (`J : JoyalStreet _`).
-/
module

public import FreeMarkov.Stage5.Counts

@[expose] public section

universe w v u' v'

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov

/-! ### The functor given by Theorem 4.1 -/

namespace JoyalStreet

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} (J : JoyalStreet G.toFreeGraphMonoid)
  {D : Type u'} [Monoid D] [Category.{v'} D] [StrictMarkov D]

/-- *Theorem 4.1.* The strict Markov functor `F : F_s(G)/S_M → D` with `f = F ∘ i_m`. -/
noncomputable def lift (f : G.toGraphMonoid.Hom (graphMonoid D)) (hf : G.MatchesDupDisc f) :
    StrictMarkovFunctor J.FsM D :=
  Classical.choose (J.theorem_4_1.existsUnique_lift D f hf)

variable {J}

theorem lift_spec (f : G.toGraphMonoid.Hom (graphMonoid D)) (hf : G.MatchesDupDisc f) :
    f = (J.lift f hf).toGraphMonoidHom.comp J.iM :=
  (Classical.choose_spec (J.theorem_4_1.existsUnique_lift D f hf)).1

/-- The uniqueness in Theorem 4.1. -/
theorem eq_lift (f : G.toGraphMonoid.Hom (graphMonoid D)) (hf : G.MatchesDupDisc f)
    (F : StrictMarkovFunctor J.FsM D) (hF : f = F.toGraphMonoidHom.comp J.iM) : F = J.lift f hf :=
  (Classical.choose_spec (J.theorem_4_1.existsUnique_lift D f hf)).2 F hF

theorem lift_obj (f : G.toGraphMonoid.Hom (graphMonoid D)) (hf : G.MatchesDupDisc f)
    (a : FreeMonoid S) : (J.lift f hf).obj (J.wordM a) = f.V a := by
  conv_rhs => rw [lift_spec (J := J) f hf]
  rfl

theorem lift_gen (f : G.toGraphMonoid.Hom (graphMonoid D)) (hf : G.MatchesDupDisc f) (x : G.A) :
    Arrow.mk ((J.lift f hf).map (J.projM.map (J.hom (DHom.gen x)))) = f.A x := by
  conv_rhs => rw [lift_spec (J := J) f hf]
  rfl

/-- Two strict Markov functors out of `F_s(G)/S_M` that agree on the generators are equal. -/
theorem functor_ext {F F' : StrictMarkovFunctor J.FsM D}
    (h : F.toGraphMonoidHom.comp J.iM = F'.toGraphMonoidHom.comp J.iM) : F = F' := by
  have hm : G.MatchesDupDisc (F.toGraphMonoidHom.comp J.iM) := by
    refine ⟨fun a => ?_, fun a => ?_⟩
    · change Arrow.mk (F.map (J.iM.A (G.dup a)).hom) = _
      rw [J.iM_matches.dup a]
      exact F.map_copy _
    · change Arrow.mk (F.map (J.iM.A (G.disc a)).hom) = _
      rw [J.iM_matches.disc a]
      exact F.map_discard _
  exact (eq_lift _ hm F rfl).trans (eq_lift _ hm F' h).symm

end JoyalStreet

/-! ### Graph monoid homomorphisms out of `Q.G` -/

namespace ProdSig

open JoyalStreet

variable (Q : ProdSig) {D : Type u'} [Monoid D] [Category.{v'} D] [StrictMarkov D]

/-- The graph monoid homomorphism `Q.G → D` sending the letter `x` to `obj x`, the duplicates and
discards to those of `D`, and the producer `p` to `κ p`. -/
def toHom (obj : Q.X → D) (κ : ∀ p, FreeMonoid.lift obj (Q.src p) ⟶ obj (Q.out p)) :
    Q.G.toGraphMonoid.Hom (graphMonoid D) where
  V := FreeMonoid.lift obj
  A
    | .dup x => Arrow.mk (δ_ (obj x))
    | .disc x => Arrow.mk (ε_ (obj x))
    | .mech p => Arrow.mk (κ p)
  s_A := by rintro (x | x | p) <;> simp
  t_A := by rintro (x | x | p) <;> simp

theorem toHom_matches (obj : Q.X → D) (κ : ∀ p, FreeMonoid.lift obj (Q.src p) ⟶ obj (Q.out p)) :
    Q.G.MatchesDupDisc (Q.toHom obj κ) where
  dup a := by
    change Arrow.mk (δ_ (obj a)) = Arrow.mk (δ_ (FreeMonoid.lift obj (FreeMonoid.of a)))
    rw [FreeMonoid.lift_eval_of]
  disc a := by
    change Arrow.mk (ε_ (obj a)) = Arrow.mk (ε_ (FreeMonoid.lift obj (FreeMonoid.of a)))
    rw [FreeMonoid.lift_eval_of]

/-! ### Uniqueness from label coherence -/

variable {Q} (J : JoyalStreet Q.G.toFreeGraphMonoid)

/-- The label conditions for a morphism of `F_s(Q.G)`, counted on its class: every producer occurs
at most once, and not at all if its output letter is in the domain. -/
def LabelOK {a b : FreeMonoid Q.X} (f : Fs.of J a ⟶ Fs.of J b) : Prop :=
  ∀ p, J.card (.mech p) f ≤ 1 ∧ (J.card (.mech p) f ≠ 0 → Q.out p ∉ Q.letters a)

variable {J}

theorem labelCond_of_labelOK {a b : FreeMonoid Q.X} {f : Fs.of J a ⟶ Fs.of J b} (hf : LabelOK J f)
    {n m : ℕ} {Γ : Diagram Q.G.toFreeGraphMonoid (Fin n) (Fin m)} (hΓ : J.cls f = DClass.mk Γ) :
    LabelCond Γ := by
  have hc : ∀ p, J.card (.mech p) f = Nat.card {x // Γ.val.v₁ x = .mech p} := fun p => by
    simp only [JoyalStreet.card, hΓ, DClass.card_mk, Diagram.card]
  have hdom : Γ.domWord = a := by rw [← DClass.dom_mk, ← hΓ]; exact J.cls_dom f
  refine ⟨fun p x y hx hy => ?_, fun p x hx => ?_⟩
  · have h := (hf p).1
    rw [hc] at h
    have := (Finite.card_le_one_iff_subsingleton.1 h).elim ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  · rw [hdom]
    refine (hf p).2 ?_
    rw [hc]
    exact Nat.card_ne_zero.2 ⟨⟨⟨x, hx⟩⟩, inferInstance⟩

/-- Two morphisms of `F_s(Q.G)` from a word without repeated letters, satisfying the label
conditions and with the same number of nodes of each producer, have the same image in
`F_s(Q.G)/S_M`. -/
theorem projM_eq_of_card {a b : FreeMonoid Q.X} (hnd : (Q.letters a).Nodup)
    {f g : Fs.of J a ⟶ Fs.of J b} (hf : LabelOK J f) (hg : LabelOK J g)
    (hc : ∀ p, J.card (.mech p) f = J.card (.mech p) g) :
    J.projM.map f = J.projM.map g := by
  obtain ⟨n, m, Γ, hΓ⟩ := DClass.exists_eq_mk (J.cls f)
  obtain ⟨n', m', Υ, hΥ⟩ := DClass.exists_eq_mk (J.cls g)
  rw [J.projM_map_eq_iff f g hΓ hΥ]
  have hdΓ : Γ.domWord = a := by rw [← DClass.dom_mk, ← hΓ]; exact J.cls_dom f
  have hdΥ : Υ.domWord = a := by rw [← DClass.dom_mk, ← hΥ]; exact J.cls_dom g
  have hcΓ : Γ.codWord = b := by rw [← DClass.cod_mk, ← hΓ]; exact J.cls_cod f
  have hcΥ : Υ.codWord = b := by rw [← DClass.cod_mk, ← hΥ]; exact J.cls_cod g
  refine sameSkeleton_of_labels (hdΓ.trans hdΥ.symm) (by rw [hdΓ]; exact hnd)
    (hcΓ.trans hcΥ.symm) (labelCond_of_labelOK hf hΓ) (labelCond_of_labelOK hg hΥ) fun p => ?_
  have h₁ : J.card (.mech p) f = Nat.card {x // Γ.val.v₁ x = .mech p} := by
    simp only [JoyalStreet.card, hΓ, DClass.card_mk, Diagram.card]
  have h₂ : J.card (.mech p) g = Nat.card {x // Υ.val.v₁ x = .mech p} := by
    simp only [JoyalStreet.card, hΥ, DClass.card_mk, Diagram.card]
  have h := hc p
  rw [h₁, h₂] at h
  constructor
  · rintro ⟨x, hx⟩
    have : Nat.card {x // Υ.val.v₁ x = .mech p} ≠ 0 := by
      rw [← h]; exact Nat.card_ne_zero.2 ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
    obtain ⟨⟨y, hy⟩⟩ := (Nat.card_ne_zero.1 this).1
    exact ⟨y, hy⟩
  · rintro ⟨x, hx⟩
    have : Nat.card {x // Γ.val.v₁ x = .mech p} ≠ 0 := by
      rw [h]; exact Nat.card_ne_zero.2 ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
    obtain ⟨⟨y, hy⟩⟩ := (Nat.card_ne_zero.1 this).1
    exact ⟨y, hy⟩

/-! ### No producers -/

variable (X : Type)

/-- The production signature with letters `X` and no producers: its free `DD`-graph monoid has the
letters `X` and only the duplicates and the discards as arrows. -/
abbrev free : ProdSig where
  X := X
  P := Empty
  out := Empty.elim
  out_injective := fun a => a.elim
  src := Empty.elim

variable {X}

/-- In the free Markov category over the letters `X` with only duplicates and discards, there is
at most one morphism from a word without repeated letters to any word: "a diagram from `a_1 … a_n`
has no live nodes, and the origin of an edge in its codomain is the edge in its domain with the
same value" (Remark 5.3; Remark 5.2 for one letter). -/
theorem free_hom_eq (J : JoyalStreet (free X).G.toFreeGraphMonoid) {a b : FreeMonoid X}
    (hnd : (FreeMonoid.toList a).Nodup)
    (f g : J.projM.obj (Fs.of J a) ⟶ J.projM.obj (Fs.of J b)) : f = g := by
  obtain ⟨f', rfl⟩ := J.projM_surj f
  obtain ⟨g', rfl⟩ := J.projM_surj g
  exact projM_eq_of_card hnd (fun p => p.elim) (fun p => p.elim) (fun p => p.elim)

end ProdSig

end FreeMarkov
