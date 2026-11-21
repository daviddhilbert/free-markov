/-
Free Markov categories, Stage 3: `F_s(G) / S_M` is a strict Markov category (Section 4,
before Theorem 4.1).

"We claim that the equalities (1.1), (1.2), and (1.3) hold in `F_s(G) / S_M` for all objects
and all morphisms, in other words, that `F_s(G) / S_M` is a Markov category; it is strict
since `F_s(G)` is."

* On a letter `a`, `δ_a` and `ε_a` are the images of the duplicate and the discard on `a`;
  the templates (4.1)–(4.3) give the comonoid laws on letters (`letterComon`).
* On words, `δ` and `ε` are the monoidal products of those on the letters (`Comonoid.lean`);
  so (1.2) holds and (1.1) holds for all words.
* (1.3), naturality of discards, holds for every morphism, by the template (4.4) on the
  generators (`discard_natural`).
-/
module

public import FreeMarkov.Stage3.Comonoid

@[expose] public section

universe w v

namespace FreeMarkov

open CategoryTheory MonoidalCategory StrictSMC StrictMarkov ComonObj

variable {S : Type w}

/-! ### Markov pairs are `S_M`-equivalent; the criterion for `S_M ⊆ K` -/

namespace FreeDDGraphMonoid

variable {G : FreeDDGraphMonoid.{w, v} S}

/-- The two diagrams of each Markov template are `S_M`-equivalent (a surgery on the whole
diagram). -/
theorem MarkovPair.sRel (J : JoyalStreet G.toFreeGraphMonoid) {c d : DClass G.toFreeGraphMonoid}
    (h : G.MarkovPair c d) : SRel G.markovTemplates c d := by
  have key : ∀ τ ∈ G.baseMarkovTemplates, ∀ {c d}, (∃ (dΩ : Enumeration τ.Ω.IsDom)
      (cΩ : Enumeration τ.Ω.IsCod), DClass.mk (τ.Ω.anchor dΩ cΩ) = c ∧
      DClass.mk (τ.Λ.anchor (dΩ.mapEquiv τ.α.symm) (cΩ.mapEquiv τ.β.symm)) = d) →
      SRel G.markovTemplates c d := by
    rintro τ hτ c d ⟨dΩ, cΩ, h₁, h₂⟩
    have := SRel.of_gen (T := G.markovTemplates) J (Or.inr (Or.inl hτ)) dΩ cΩ (dΩ.mapEquiv τ.α.symm)
      (cΩ.mapEquiv τ.β.symm)
      (by rw [Enumeration.mapEquiv_mapEquiv, Equiv.symm_trans_self, Enumeration.mapEquiv_refl])
      (by rw [Enumeration.mapEquiv_mapEquiv, Equiv.symm_trans_self, Enumeration.mapEquiv_refl])
    rw [h₁, h₂] at this
    exact this
  cases h with
  | coass a =>
    exact key _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩)))) (Template.ofDiagrams_pair _ _ _ _)
  | counit a =>
    exact key _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩)))) (Template.ofDiagrams_pair _ _ _ _)
  | counit' a =>
    exact key _ (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩))) (Template.ofDiagrams_pair _ _ _ _)
  | cocomm a => exact key _ (Or.inl (Or.inr ⟨a, rfl⟩)) (Template.ofDiagrams_pair _ _ _ _)
  | nat f => exact key _ (Or.inr ⟨f, rfl⟩) (Template.ofDiagrams_pair _ _ _ _)

/-- **Criterion for `S_M ⊆ K`.** A relation on classes that is reflexive, transitive,
compatible with `⊗` and `∘`, and relates the two diagrams of each Markov template (in both
directions) contains `S_M`. -/
theorem sRelClosed_markov {K : DClass G.toFreeGraphMonoid → DClass G.toFreeGraphMonoid → Prop}
    (refl : ∀ c, K c c) (trans : ∀ {c d e}, K c d → K d e → K c e)
    (tensor : ∀ {c c' d d'}, K c c' → K d d' → K (c.tensor d) (c'.tensor d'))
    (comp : ∀ {c c' d d'}, K c c' → K d d' → c.cod = d.dom → c'.cod = d'.dom →
      K (c.comp d) (c'.comp d'))
    (pair : ∀ {c d}, G.MarkovPair c d → K c d ∧ K d c) :
    SRelClosed G.markovTemplates K where
  refl := refl
  trans := trans
  tensor := tensor
  comp := comp
  gen τ hτ := by
    rcases hτ with rfl | hτ | ⟨σ, hσ, rfl⟩
    · refine ⟨Enumeration.ofFinite _, Enumeration.ofFinite _, ?_⟩
      change K _ (DClass.mk ((Template.empty G.toFreeGraphMonoid).Λ.anchor
        ((Enumeration.ofFinite _).mapEquiv (Equiv.refl _))
        ((Enumeration.ofFinite _).mapEquiv (Equiv.refl _))))
      rw [Enumeration.mapEquiv_refl, Enumeration.mapEquiv_refl]
      exact refl _
    · obtain ⟨c, d, h, dΩ, cΩ, h₁, h₂⟩ := G.baseMarkovTemplates_pair (by assumption)
      refine ⟨dΩ, cΩ, ?_⟩
      rw [h₁, h₂]
      exact (pair h).1
    · obtain ⟨c, d, h, hp⟩ := G.baseMarkovTemplates_pair (by assumption)
      obtain ⟨dΩ, cΩ, h₁, h₂⟩ := Template.symm_pair hp
      refine ⟨dΩ, cΩ, ?_⟩
      rw [h₁, h₂]
      exact (pair h).2

end FreeDDGraphMonoid

/-- `σ_{1,1} = 1_1` in a symmetric strict monoidal category. -/
theorem StrictSMC.braid_one_one {C : Type*} [Monoid C] [Category C]
    [StrictSMC C] : σ_ (1 : C) (1 : C) = eqToHom (by rw [one_mul]) := by
  have h := braiding_tensorUnit_left (C := C) 1
  simp only [braiding_hom_eq, tensorUnit_eq, leftUnitor_eq, rightUnitor_eq, eqToIso.hom,
    eqToIso.inv, eqToHom_trans] at h
  exact h

/-! ### The quotient `F_s(G) / S_M` -/

namespace JoyalStreet

variable {G : FreeDDGraphMonoid.{w, v} S} (J : JoyalStreet G.toFreeGraphMonoid)

/-- **The quotient category `F_s(G) / S_M`** (Section 4), `S_M` the monoidal congruence
of the Markov templates. -/
abbrev FsM : Type w := J.Quot G.markovTemplates G.markovTemplates_isSymmetric

/-- The projection `- / S_M : F_s(G) → F_s(G) / S_M`. -/
noncomputable abbrev projM : J.Fs ⥤ J.FsM := J.quotProj _ _

/-- A word, as an object of `F_s(G) / S_M`. -/
abbrev wordM (a : FreeMonoid S) : J.FsM := J.word _ _ a

theorem projM_eq_of_pair {a b : FreeMonoid S} (f g : DHom G.toFreeGraphMonoid a b)
    (h : G.MarkovPair f.1 g.1) : J.projM.map (J.hom f) = J.projM.map (J.hom g) :=
  (J.quotProj_map_eq_iff _ _ _ _).2 (h.sRel J)

/-- The duplicate on a letter in `F_s(G) / S_M`: the class of the one-node diagram. -/
noncomputable def dupM (x : S) :
    J.wordM (FreeMonoid.of x) ⟶ J.wordM (FreeMonoid.of x) * J.wordM (FreeMonoid.of x) :=
  J.projM.map (J.hom (G.dupH x))

/-- The discard on a letter in `F_s(G) / S_M`: the class of the one-node diagram. -/
noncomputable def discM (x : S) : J.wordM (FreeMonoid.of x) ⟶ 1 :=
  J.projM.map (J.hom (G.discH x))

/-- (4.1) in `F_s(G) / S_M`: `(δ_a ⊗ 1_a) ∘ δ_a = (1_a ⊗ δ_a) ∘ δ_a` on letters. -/
theorem dupM_assoc (x : S) :
    J.dupM x ≫ (J.dupM x ⊗ₛ 𝟙 _) = J.dupM x ≫ (𝟙 _ ⊗ₛ J.dupM x) :=
  J.projM_eq_of_pair (G.coassΩ x) ((G.coassΛ x).cast rfl (mul_assoc _ _ _).symm)
    (G.markovPair_coass x)

/-- (4.2) in `F_s(G) / S_M`: `(1_a ⊗ ε_a) ∘ δ_a = 1_a` on letters. -/
theorem dupM_discM (x : S) : J.dupM x ≫ (𝟙 _ ⊗ₛ J.discM x) = 𝟙 _ :=
  J.projM_eq_of_pair (G.counitΩ x) ((DHom.id _ (FreeMonoid.of x)).cast rfl (mul_one _).symm)
    (G.markovPair_counit x)

/-- (4.2), right counitality, in `F_s(G) / S_M`: `(ε_a ⊗ 1_a) ∘ δ_a = 1_a` on letters. -/
theorem discM_dupM (x : S) : J.dupM x ≫ (J.discM x ⊗ₛ 𝟙 _) = 𝟙 _ :=
  J.projM_eq_of_pair (G.counitΩ' x) ((DHom.id _ (FreeMonoid.of x)).cast rfl (one_mul _).symm)
    (G.markovPair_counit' x)

/-- (4.3) in `F_s(G) / S_M`: `σ_{aa} ∘ δ_a = δ_a` on letters. -/
theorem dupM_comm (x : S) : J.dupM x ≫ σ_ _ _ = J.dupM x :=
  J.projM_eq_of_pair (G.cocommΩ x) (G.dupH x) (G.markovPair_cocomm x)

/-- The comonoid `(a, δ_a, ε_a)` on a letter, as a Mathlib comonoid object. -/
@[reducible] noncomputable def letterComon (x : S) : ComonObj (J.wordM (FreeMonoid.of x)) where
  counit := J.discM x
  comul := J.dupM x
  counit_comul := by
    simp only [whiskerRight_eq, leftUnitor_eq, eqToIso.inv]
    exact (J.discM_dupM x).trans (eqToHom_refl _ _).symm
  comul_counit := by
    simp only [whiskerLeft_eq, rightUnitor_eq, eqToIso.inv]
    exact (J.dupM_discM x).trans (eqToHom_refl _ _).symm
  comul_assoc := by
    simp only [whiskerLeft_eq, whiskerRight_eq, associator_eq, eqToIso.hom]
    show _ = J.dupM x ≫ (J.dupM x ⊗ₛ 𝟙 _) ≫ 𝟙 _
    rw [Category.comp_id]
    exact (J.dupM_assoc x).symm

theorem letterComm (x : S) :
    @IsCommComonObj _ _ _ _ (J.wordM (FreeMonoid.of x)) (J.letterComon x) :=
  @IsCommComonObj.mk _ _ _ _ _ (J.letterComon x) (by
    simp only [braiding_hom_eq]
    exact J.dupM_comm x)

/-- The duplicate `δ_a` on a word `a` of `F_s(G) / S_M`. -/
noncomputable def copyM (a : J.FsM) : a ⟶ a * a := J.copyW _ _ J.letterComon a

/-- The discard `ε_a = ε_{a_1} ⊗ ⋯ ⊗ ε_{a_n}` on a word `a` of `F_s(G) / S_M`. -/
noncomputable def discardM (a : J.FsM) : a ⟶ 1 := J.discardW _ _ J.letterComon a

theorem discardM_tensor (a b : J.FsM) :
    J.discardM (a * b) = (J.discardM a ⊗ₛ J.discardM b : a * b ⟶ 1) :=
  Arrow.eq_of_mk_eq (J.discardW_tensor _ _ _ a b)

theorem copyM_of (x : S) : J.copyM (J.wordM (FreeMonoid.of x)) = J.dupM x :=
  J.copyW_of _ _ _ x

theorem discardM_of (x : S) : J.discardM (J.wordM (FreeMonoid.of x)) = J.discM x :=
  J.discardW_of _ _ _ x

/-- `ε_{a_1} ⊗ ⋯ ⊗ ε_{a_n}` of `F_s(G)` goes to `ε_a` in `F_s(G) / S_M`. -/
theorem projM_discList (l : List S) :
    J.projM.map (J.hom (G.discList l)) = J.discardM (J.wordM (FreeMonoid.ofList l)) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change J.projM.map (J.hom (G.discH x)) ⊗ₛ J.projM.map (J.hom (G.discList l)) =
      J.discardM (J.wordM (FreeMonoid.of x) * J.wordM (FreeMonoid.ofList l))
    rw [ih, J.discardM_tensor, J.discardM_of]
    rfl

theorem projM_discWord (a : FreeMonoid S) :
    J.projM.map (J.hom (G.discWord a)) = J.discardM (J.wordM a) :=
  J.projM_discList (FreeMonoid.toList a)

/-- **(1.3) in `F_s(G) / S_M`**: discards are natural, `ε_c ∘ f = ε_b` for every morphism
`f : b → c`.  On a generator this is the template (4.4); the other cases follow from (1.2)
and the axioms of symmetric strict monoidal categories, by the generation principle. -/
theorem discardM_natural {a b : J.FsM} (f : a ⟶ b) : f ≫ J.discardM b = J.discardM a := by
  induction f using Quotient.ind with
  | _ g =>
  change J.projM.map g ≫ J.discardM (J.projM.obj b) = J.discardM (J.projM.obj a)
  refine J.induction (P := fun {a b} g =>
    J.projM.map g ≫ J.discardM (J.projM.obj b) = J.discardM (J.projM.obj a)) ?_ ?_ ?_ ?_ ?_ g
  · intro x
    have h := J.projM_eq_of_pair (G.natΩ x) (G.natΛ x) (G.markovPair_nat x)
    change J.projM.map (J.hom (DHom.gen x)) ≫ J.projM.map (J.hom (G.discWord (G.t x))) =
      J.projM.map (J.hom (G.discWord (G.s x))) at h
    rw [J.projM_discWord, J.projM_discWord] at h
    exact h
  · intro a
    exact Category.id_comp _
  · intro a b
    change σ_ (J.projM.obj a) (J.projM.obj b) ≫ J.discardM (J.projM.obj b * J.projM.obj a) =
      J.discardM (J.projM.obj a * J.projM.obj b)
    rw [J.discardM_tensor, J.discardM_tensor]
    have h1 : σ_ (1 : J.FsM) (1 : J.FsM) = 𝟙 _ :=
      StrictSMC.braid_one_one.trans (eqToHom_refl _ _)
    refine (braid_natural _ _).symm.trans ?_
    exact (congrArg _ h1).trans (Category.comp_id _)
  · intro a b c f g hf hg
    rw [Functor.map_comp, Category.assoc, hg, hf]
  · intro a b c d f g hf hg
    change (J.projM.map f ⊗ₛ J.projM.map g) ≫ J.discardM (J.projM.obj b * J.projM.obj d) =
      J.discardM (J.projM.obj a * J.projM.obj c)
    rw [J.discardM_tensor, J.discardM_tensor]
    exact (tensorHom_comp _ _ _ _).symm.trans (congrArg₂ _ hf hg)

/-- **`F_s(G) / S_M` is a strict Markov category** (Section 4): duplicates and discards on
words as above; (1.1), (1.2) and (1.3) hold for all objects and morphisms. -/
noncomputable instance strictMarkovM : StrictMarkov J.FsM where
  toStrictSMC := J.quotStrictSMC _ _
  copy := J.copyM
  discard := J.discardM
  copy_assoc := J.copyW_assoc _ _ _
  discard_copy := J.discardW_copyW _ _ _
  copy_discard := J.copyW_discardW _ _ _
  copy_comm := J.copyW_comm _ _ _ J.letterComm
  copy_tensor := J.copyW_tensor _ _ _
  discard_tensor := J.discardW_tensor _ _ _
  discard_natural := J.discardM_natural

/-! ### Independence of the order of the prongs -/

/-- The duplicate on a letter with a chosen order of its prongs: `δ_a` (`false`), or the
one-node diagram of (4.3) whose outputs are taken in the other order, which represents
`σ_{aa} ∘ δ_a` (`true`). -/
noncomputable def dupPronged (x : S) (b : Bool) :
    J.wordM (FreeMonoid.of x) ⟶ J.wordM (FreeMonoid.of x) * J.wordM (FreeMonoid.of x) :=
  if b then J.projM.map (J.hom (G.cocommΩ x)) else J.dupM x

/-- The diagram `Γ` that defines `δ_a` for `a = a_1 ⋯ a_n`: the duplicates on the letters,
the two outputs of the `i`th one joined to the `i`th and `(n+i)`th edges of the codomain
in the order chosen by `c i`, read as a morphism of `F_s(G) / S_M` through (1.2). -/
noncomputable def prongCopy : (l : List S) → (Fin l.length → Bool) →
    ((J.wordM (FreeMonoid.ofList l) : J.FsM) ⟶ J.wordM (FreeMonoid.ofList l) *
      J.wordM (FreeMonoid.ofList l))
  | [], _ => 𝟙 (1 : J.FsM)
  | x :: l, c =>
    ((J.dupPronged x (c 0) ⊗ₛ prongCopy l (fun i => c i.succ)) ≫
      eqToHom (by simp only [mul_assoc]) ≫
      ((𝟙 (J.wordM (FreeMonoid.of x)) ⊗ₛ σ_ (J.wordM (FreeMonoid.of x))
        (J.wordM (FreeMonoid.ofList l))) ⊗ₛ 𝟙 (J.wordM (FreeMonoid.ofList l)))) ≫
      eqToHom (by simp only [mul_assoc]; rfl)

theorem dupPronged_eq (x : S) (b : Bool) : J.dupPronged x b = J.dupM x := by
  cases b
  · rfl
  · exact J.dupM_comm x

/-- **Independence of the order of the prongs** (Section 4): "the two outputs of each
`δ_{a_i}` may be connected in either order. On the other hand, in light of (4.3), all such
`Γ` represent the same morphism in the quotient category `F_s(G) / S_M`, which is denoted by
`δ_a` (it is the identity if `a` is the empty word)." -/
theorem prongCopy_eq (l : List S) (c : Fin l.length → Bool) :
    Arrow.mk (J.prongCopy l c) = Arrow.mk (δ_ (J.wordM (FreeMonoid.ofList l))) := by
  induction l with
  | nil => exact copy_one.symm
  | cons x l ih =>
    change Arrow.mk ((((J.dupPronged x (c 0) ⊗ₛ J.prongCopy l (fun i => c i.succ)) ≫ _) ≫
      eqToHom _)) = _
    rw [Arrow.arrow_mk_comp_eqToHom, J.dupPronged_eq, ← J.copyM_of,
      Arrow.eq_of_mk_eq ((ih (fun i => c i.succ)).trans rfl)]
    exact (copy_tensor (J.wordM (FreeMonoid.of x)) (J.wordM (FreeMonoid.ofList l))).symm

/-- `F_s(G) / S_M` is a Markov category in the sense of Mathlib (through the bridge of
Stage 0). -/
noncomputable instance markovCategoryM : MarkovCategory J.FsM := StrictMarkov.markovCategory _

end JoyalStreet

end FreeMarkov
