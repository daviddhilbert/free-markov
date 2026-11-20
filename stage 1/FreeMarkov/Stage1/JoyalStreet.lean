/-
Free Markov categories, Stage 1: the cited result C1 (Joyal–Street, Theorem 2.3) in
comparison form, the category `F_s(G)`, and Theorem 2.3 of the paper under it
(design decision D4 of `formalization/PLAN.md`).

`JoyalStreet G` is a hypothesis, never an axiom.  It states, for a free graph
monoid `G`, a bijection between the morphisms `a → b` of the syntactic free
symmetric strict monoidal category `Syn_s(G)` (built and shown free in Stage 0) and
the isomorphism classes of anchored diagrams in `G` from `a` to `b`, sending a
generator to its one-node diagram, composition to gluing, monoidal product to
disjoint union, identities and symmetries to the node-free diagrams.  Given that
`Syn_s(G)` is free, this is equivalent to Joyal–Street's Theorem 2.3 with the
construction of `F_s(G)` in Chapter 2, §2 (two free objects are isomorphic by a
unique strict isomorphism, and that isomorphism is the identity on words and on
generators); it says nothing more.  The category laws of `F_s(G)`, its freeness and
its generation by the generators are then theorems.
-/
module

public import FreeMarkov.Stage1.Classes

@[expose] public section

universe w v u' v'

namespace FreeMarkov

open CategoryTheory StrictSMC FreeGraphMonoid

/-- **Cited result C1** (Joyal–Street, *The geometry of tensor calculus I*, Chapter 2,
§2, Theorem 2.3, and the remark after the proof of Theorem 1.2), in comparison form
(PLAN.md, D4): for all words `a, b`, a bijection between the morphisms `a → b` of the
syntactic free symmetric strict monoidal category `Syn_s(G)` and the isomorphism
classes of anchored diagrams in `G` from `a` to `b`, compatible with the operations
of Section 2. -/
structure JoyalStreet {S : Type w} (G : FreeGraphMonoid.{w, v} S) where
  /-- The bijection `Syn_s(G)(a, b) ≅ {[Γ, v] : dom = a, cod = b}`. -/
  equiv (a b : FreeMonoid S) : (Syn.of G a ⟶ Syn.of G b) ≃ DHom G a b
  /-- A generator goes to the class of its one-node diagram. -/
  map_gen (x : G.A) : equiv (G.s x) (G.t x) (Syn.gen x) = DHom.gen x
  /-- Identities go to node-free diagrams. -/
  map_id (a : FreeMonoid S) : equiv a a (𝟙 (Syn.of G a)) = DHom.id G a
  /-- Symmetries go to node-free diagrams. -/
  map_braid (a b : FreeMonoid S) :
    equiv (a * b) (b * a) (σ_ (Syn.of G a) (Syn.of G b)) = DHom.braid G a b
  /-- Composition goes to gluing. -/
  map_comp {a b c : FreeMonoid S} (f : Syn.of G a ⟶ Syn.of G b) (g : Syn.of G b ⟶ Syn.of G c) :
    equiv a c (f ≫ g) = (equiv a b f).comp (equiv b c g)
  /-- Monoidal product goes to disjoint union. -/
  map_tensor {a b c d : FreeMonoid S} (f : Syn.of G a ⟶ Syn.of G b)
    (g : Syn.of G c ⟶ Syn.of G d) :
    equiv (a * c) (b * d) (f ⊗ₛ g) = (equiv a b f).tensor (equiv c d g)

/-- A symmetric strict monoidal category `C` is **free** over a free graph monoid `G`
via `i : G → C` (Section 2, after Theorem 2.3): "every graph monoid homomorphism from
`G` into a symmetric strict monoidal category factors through the obvious graph monoid
homomorphism `G → F_s(G)` by exactly one strict symmetric monoidal functor".  As for
`IsFreeMarkov`, the target universes `u'`, `v'` are free parameters. -/
structure IsFreeSymmetric (C : Type*) [Monoid C] [Category C] [StrictSMC C]
    {S : Type w} (G : FreeGraphMonoid.{w, v} S) (i : G.toGraphMonoid.Hom (graphMonoid C)) :
    Prop where
  existsUnique_lift :
    ∀ (D : Type u') [Monoid D] [Category.{v'} D] [StrictSMC D]
      (f : G.toGraphMonoid.Hom (graphMonoid D)),
      ∃! F : StrictFunctor C D, f = F.toGraphMonoidHom.comp i

namespace JoyalStreet

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} (J : JoyalStreet G)

/-! The laws of `F_s(G)`, transported from `Syn_s(G)` along C1. -/

section Laws

include J

theorem dhom_id_comp {a b : FreeMonoid S} (f : DHom G a b) : (DHom.id G a).comp f = f := by
  obtain ⟨f, rfl⟩ := (J.equiv a b).surjective f
  rw [← J.map_id, ← J.map_comp, Category.id_comp]

theorem dhom_comp_id {a b : FreeMonoid S} (f : DHom G a b) : f.comp (DHom.id G b) = f := by
  obtain ⟨f, rfl⟩ := (J.equiv a b).surjective f
  rw [← J.map_id, ← J.map_comp, Category.comp_id]

theorem dhom_assoc {a b c d : FreeMonoid S} (f : DHom G a b) (g : DHom G b c) (h : DHom G c d) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  obtain ⟨f, rfl⟩ := (J.equiv a b).surjective f
  obtain ⟨g, rfl⟩ := (J.equiv b c).surjective g
  obtain ⟨h, rfl⟩ := (J.equiv c d).surjective h
  rw [← J.map_comp, ← J.map_comp, ← J.map_comp, ← J.map_comp, Category.assoc]

theorem dhom_tensor_id (a c : FreeMonoid S) :
    (DHom.id G a).tensor (DHom.id G c) = DHom.id G (a * c) :=
  calc (DHom.id G a).tensor (DHom.id G c)
      = (J.equiv a a (𝟙 _)).tensor (J.equiv c c (𝟙 _)) := by rw [J.map_id, J.map_id]
    _ = J.equiv (a * c) (a * c) (𝟙 (Syn.of G a) ⊗ₛ 𝟙 (Syn.of G c)) := (J.map_tensor _ _).symm
    _ = J.equiv (a * c) (a * c) (𝟙 (Syn.of G (a * c))) :=
        congrArg (J.equiv _ _) (StrictSMC.tensorHom_id _ _)
    _ = DHom.id G (a * c) := J.map_id _

theorem dhom_tensor_comp {a₁ a₂ a₃ c₁ c₂ c₃ : FreeMonoid S} (f : DHom G a₁ a₂)
    (f' : DHom G a₂ a₃) (g : DHom G c₁ c₂) (g' : DHom G c₂ c₃) :
    (f.comp f').tensor (g.comp g') = (f.tensor g).comp (f'.tensor g') := by
  obtain ⟨f, rfl⟩ := (J.equiv _ _).surjective f
  obtain ⟨f', rfl⟩ := (J.equiv _ _).surjective f'
  obtain ⟨g, rfl⟩ := (J.equiv _ _).surjective g
  obtain ⟨g', rfl⟩ := (J.equiv _ _).surjective g'
  exact (congrArg₂ DHom.tensor (J.map_comp f f').symm (J.map_comp g g').symm).trans
    ((J.map_tensor _ _).symm.trans ((congrArg (J.equiv _ _)
      (StrictSMC.tensorHom_comp f f' g g')).trans ((J.map_comp _ _).trans
        (congrArg₂ DHom.comp (J.map_tensor f g) (J.map_tensor f' g')))))

theorem dhom_braid_natural {a b c d : FreeMonoid S} (f : DHom G a b) (g : DHom G c d) :
    (f.tensor g).comp (DHom.braid G b d) = (DHom.braid G a c).comp (g.tensor f) := by
  obtain ⟨f, rfl⟩ := (J.equiv _ _).surjective f
  obtain ⟨g, rfl⟩ := (J.equiv _ _).surjective g
  exact (congrArg₂ DHom.comp (J.map_tensor f g).symm (J.map_braid b d).symm).trans
    ((J.map_comp _ _).symm.trans ((congrArg (J.equiv _ _) (StrictSMC.braid_natural f g)).trans
      ((J.map_comp _ _).trans (congrArg₂ DHom.comp (J.map_braid a c) (J.map_tensor g f)))))

theorem dhom_braid_braid (a b : FreeMonoid S) :
    (DHom.braid G a b).comp (DHom.braid G b a) = DHom.id G (a * b) :=
  (congrArg₂ DHom.comp (J.map_braid a b).symm (J.map_braid b a).symm).trans
    ((J.map_comp _ _).symm.trans ((congrArg (J.equiv _ _)
      (StrictSMC.braid_braid (Syn.of G a) (Syn.of G b))).trans (J.map_id _)))

/-- Morphisms of `Syn_s(G)` that are equal as arrows have the same class. -/
theorem val_eq_of_arrow_eq {a b a' b' : FreeMonoid S} {f : Syn.of G a ⟶ Syn.of G b}
    {f' : Syn.of G a' ⟶ Syn.of G b'} (h : Arrow.mk f = Arrow.mk f') :
    (J.equiv a b f).1 = (J.equiv a' b' f').1 := by
  have ha : Syn.of G a = Syn.of G a' := Arrow.left_eq_of_mk_eq h
  have hb : Syn.of G b = Syn.of G b' := Arrow.right_eq_of_mk_eq h
  have ha' : a = a' := ha
  have hb' : b = b' := hb
  subst ha' hb'
  rw [Arrow.eq_of_mk_eq h]

theorem val_comp_eqToHom_comp {a b b' c : FreeMonoid S} (f : Syn.of G a ⟶ Syn.of G b)
    (h : b = b') (g : Syn.of G b' ⟶ Syn.of G c) :
    (J.equiv a c (f ≫ eqToHom (congrArg (Syn.of G) h) ≫ g)).1 =
      (J.equiv a b f).1.comp (J.equiv b' c g).1 := by
  subst h
  rw [eqToHom_refl, Category.id_comp, J.map_comp]
  rfl

theorem val_tensor_assoc {a b c d e f : FreeMonoid S} (x : DHom G a b) (y : DHom G c d)
    (z : DHom G e f) : ((x.tensor y).tensor z).1 = (x.tensor (y.tensor z)).1 := by
  obtain ⟨x, rfl⟩ := (J.equiv _ _).surjective x
  obtain ⟨y, rfl⟩ := (J.equiv _ _).surjective y
  obtain ⟨z, rfl⟩ := (J.equiv _ _).surjective z
  have e₁ := (congrArg (fun t => DHom.tensor t (J.equiv _ _ z)) (J.map_tensor x y).symm).trans
    (J.map_tensor (x ⊗ₛ y) z).symm
  have e₂ := (congrArg (fun t => DHom.tensor (J.equiv _ _ x) t) (J.map_tensor y z).symm).trans
    (J.map_tensor x (y ⊗ₛ z)).symm
  exact (congrArg Subtype.val e₁).trans ((J.val_eq_of_arrow_eq
    (StrictSMC.tensorHom_assoc x y z)).trans (congrArg Subtype.val e₂).symm)

theorem val_id_one_tensor {a b : FreeMonoid S} (f : DHom G a b) :
    ((DHom.id G 1).tensor f).1 = f.1 := by
  obtain ⟨f, rfl⟩ := (J.equiv _ _).surjective f
  have e := (congrArg (fun t => DHom.tensor t (J.equiv _ _ f)) (J.map_id 1).symm).trans
    (J.map_tensor (𝟙 (Syn.of G 1)) f).symm
  exact (congrArg Subtype.val e).trans (J.val_eq_of_arrow_eq (StrictSMC.id_one_tensorHom f))

theorem val_tensor_id_one {a b : FreeMonoid S} (f : DHom G a b) :
    (f.tensor (DHom.id G 1)).1 = f.1 := by
  obtain ⟨f, rfl⟩ := (J.equiv _ _).surjective f
  have e := (congrArg (fun t => DHom.tensor (J.equiv _ _ f) t) (J.map_id 1).symm).trans
    (J.map_tensor f (𝟙 (Syn.of G 1))).symm
  exact (congrArg Subtype.val e).trans (J.val_eq_of_arrow_eq (StrictSMC.tensorHom_id_one f))

theorem val_hexagon (a b c : FreeMonoid S) :
    (DHom.braid G a (b * c)).1 =
      ((DHom.braid G a b).tensor (DHom.id G c)).1.comp
        ((DHom.id G b).tensor (DHom.braid G a c)).1 := by
  have e₁ : (DHom.braid G a b).tensor (DHom.id G c) =
      J.equiv _ _ (σ_ (Syn.of G a) (Syn.of G b) ⊗ₛ 𝟙 (Syn.of G c)) :=
    (congrArg₂ DHom.tensor (J.map_braid a b).symm (J.map_id c).symm).trans (J.map_tensor _ _).symm
  have e₂ : (DHom.id G b).tensor (DHom.braid G a c) =
      J.equiv _ _ (𝟙 (Syn.of G b) ⊗ₛ σ_ (Syn.of G a) (Syn.of G c)) :=
    (congrArg₂ DHom.tensor (J.map_id b).symm (J.map_braid a c).symm).trans (J.map_tensor _ _).symm
  refine (congrArg Subtype.val (J.map_braid a (b * c)).symm).trans
    ((J.val_eq_of_arrow_eq (StrictSMC.hexagon (Syn.of G a) (Syn.of G b) (Syn.of G c))).trans
      ((J.val_comp_eqToHom_comp _ (mul_assoc b a c) _).trans ?_))
  exact congrArg₂ (fun (s : DHom G _ _) (t : DHom G _ _) => s.1.comp t.1) e₁.symm e₂.symm

end Laws

/-- *Section 2.* The symmetric strict monoidal category `F_s(G)`: objects the words
over `S`, morphisms `a → b` the isomorphism classes `[Γ, v]` of anchored diagrams in
`G` from `a` to `b` (`DHom G a b`), composition by gluing, monoidal product by disjoint
union, identities and symmetries by node-free diagrams.  The operations are defined
in Stage 1 without C1; C1 is used only for the laws. -/
def Fs (_J : JoyalStreet G) : Type w := FreeMonoid S

instance : Monoid J.Fs := inferInstanceAs (Monoid (FreeMonoid S))

/-- A word, regarded as an object of `F_s(G)`. -/
def Fs.of (a : FreeMonoid S) : J.Fs := a

noncomputable instance category : Category.{max w v} J.Fs where
  Hom a b := DHom G a b
  id a := DHom.id G a
  comp f g := DHom.comp f g
  id_comp f := J.dhom_id_comp f
  comp_id f := J.dhom_comp_id f
  assoc f g h := J.dhom_assoc f g h

/-- A class from `a` to `b`, as a morphism of `F_s(G)`. -/
def hom {a b : FreeMonoid S} (f : DHom G a b) : Fs.of J a ⟶ Fs.of J b := f

/-- The class `[Γ, v]` underlying a morphism of `F_s(G)`. -/
def cls {a b : J.Fs} (f : a ⟶ b) : DClass G :=
  Subtype.val (p := fun c : DClass G => c.dom = a ∧ c.cod = b) f

@[simp] theorem cls_hom {a b : FreeMonoid S} (f : DHom G a b) : J.cls (J.hom f) = f.1 := rfl

theorem cls_dom {a b : J.Fs} (f : a ⟶ b) : (J.cls f).dom = a :=
  (Subtype.property (p := fun c : DClass G => c.dom = a ∧ c.cod = b) f).1

theorem cls_cod {a b : J.Fs} (f : a ⟶ b) : (J.cls f).cod = b :=
  (Subtype.property (p := fun c : DClass G => c.dom = a ∧ c.cod = b) f).2

theorem cls_comp {a b c : J.Fs} (f : a ⟶ b) (g : b ⟶ c) :
    J.cls (f ≫ g) = (J.cls f).comp (J.cls g) := rfl

theorem cls_id (a : J.Fs) : J.cls (𝟙 a) = DClass.mk (Diagram.idD G a) := rfl

theorem cls_comp_eqToHom_comp {a b b' c : J.Fs} (f : a ⟶ b) (h : b = b') (g : b' ⟶ c) :
    J.cls (f ≫ eqToHom h ≫ g) = (J.cls f).comp (J.cls g) := by
  subst h
  rw [eqToHom_refl, Category.id_comp]
  rfl

/-- Morphisms of `F_s(G)` with the same class are equal as arrows. -/
theorem arrow_eq_of_cls_eq {a b a' b' : J.Fs} {f : a ⟶ b} {g : a' ⟶ b'}
    (h : J.cls f = J.cls g) : Arrow.mk f = Arrow.mk g := by
  have ha : a = a' := (J.cls_dom f).symm.trans (h ▸ J.cls_dom g)
  have hb : b = b' := (J.cls_cod f).symm.trans (h ▸ J.cls_cod g)
  subst ha hb
  exact congrArg Arrow.mk (Subtype.ext h)

/-- The identification of `Syn_s(G)` with `F_s(G)` given by C1, as a functor. -/
noncomputable def toFs : G.Syn ⥤ J.Fs where
  obj a := a
  map {a b} f := J.equiv a b f
  map_id a := J.map_id a
  map_comp f g := J.map_comp f g

theorem toFs_map {a b : G.Syn} (f : a ⟶ b) : J.toFs.map f = J.equiv a b f := rfl

noncomputable instance strictSMC : StrictSMC J.Fs where
  tensorHom f g := DHom.tensor f g
  braid a b := DHom.braid G a b
  tensorHom_id a c := J.dhom_tensor_id a c
  tensorHom_comp f f' g g' := J.dhom_tensor_comp f f' g g'
  tensorHom_assoc x y z := J.arrow_eq_of_cls_eq (J.val_tensor_assoc x y z)
  id_one_tensorHom f := J.arrow_eq_of_cls_eq (J.val_id_one_tensor f)
  tensorHom_id_one f := J.arrow_eq_of_cls_eq (J.val_tensor_id_one f)
  braid_natural f g := J.dhom_braid_natural f g
  braid_braid a b := J.dhom_braid_braid a b
  hexagon a b c := J.arrow_eq_of_cls_eq
    ((J.val_hexagon a b c).trans (J.cls_comp_eqToHom_comp _ _ _).symm)

theorem cls_tensor {a b c d : J.Fs} (f : a ⟶ b) (g : c ⟶ d) :
    J.cls (f ⊗ₛ g) = (J.cls f).tensor (J.cls g) := rfl

theorem cls_braid (a b : J.Fs) : J.cls (σ_ a b) = DClass.mk (Diagram.braidD G a b) := rfl

/-- The identification `Syn_s(G) → F_s(G)` is a strict symmetric monoidal functor. -/
noncomputable def toFsStrict : StrictFunctor G.Syn J.Fs where
  toFunctor := J.toFs
  obj_one := rfl
  obj_mul _ _ := rfl
  map_tensorHom f g := congrArg Arrow.mk (J.map_tensor f g)
  map_braid a b := congrArg Arrow.mk (J.map_braid a b)

/-- The inverse identification `F_s(G) → Syn_s(G)`, a strict symmetric monoidal
functor. -/
noncomputable def ofFsStrict : StrictFunctor J.Fs G.Syn where
  obj a := a
  map {a b} f := (J.equiv a b).symm f
  map_id a := (Equiv.symm_apply_eq _).2 (J.map_id a).symm
  map_comp {a b c} f g := (Equiv.symm_apply_eq _).2 <| by
    refine Eq.trans ?_ (J.map_comp _ _).symm
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  obj_one := rfl
  obj_mul _ _ := rfl
  map_tensorHom {a b c d} f g := congrArg Arrow.mk <| (Equiv.symm_apply_eq _).2 <| by
    refine Eq.trans ?_ (J.map_tensor _ _).symm
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  map_braid a b := congrArg Arrow.mk <| (Equiv.symm_apply_eq _).2 (J.map_braid a b).symm

theorem ofFs_comp_toFs : J.ofFsStrict.comp J.toFsStrict = StrictFunctor.id G.Syn :=
  StrictFunctor.ext fun {a b} f => by
    exact congrArg Arrow.mk ((J.equiv a b).symm_apply_apply f)

theorem toFs_comp_ofFs : J.toFsStrict.comp J.ofFsStrict = StrictFunctor.id J.Fs :=
  StrictFunctor.ext fun {a b} f => by
    exact congrArg Arrow.mk ((J.equiv a b).apply_symm_apply f)

/-- *Section 2.* The "obvious graph monoid homomorphism `G → F_s(G)`": the identity on
words, and each arrow to the class of its one-node diagram. -/
noncomputable def ι : G.toGraphMonoid.Hom (graphMonoid J.Fs) where
  V := MonoidHom.id (FreeMonoid S)
  A x := Arrow.mk (J.hom (DHom.gen x))
  s_A _ := rfl
  t_A _ := rfl

theorem toFsStrict_comp_ι : J.toFsStrict.toGraphMonoidHom.comp (Syn.ι G) = J.ι := by
  ext x
  · rfl
  · exact congrArg Arrow.mk (J.map_gen x)

theorem ofFsStrict_comp_ι : J.ofFsStrict.toGraphMonoidHom.comp J.ι = Syn.ι G := by
  ext x
  · rfl
  · change Arrow.mk ((J.equiv _ _).symm (DHom.gen x)) = Arrow.mk (Syn.gen x)
    rw [← J.map_gen, Equiv.symm_apply_apply]

theorem StrictFunctor.comp_assoc {A B C D : Type*} [Monoid A] [Category A] [StrictSMC A]
    [Monoid B] [Category B] [StrictSMC B] [Monoid C] [Category C] [StrictSMC C]
    [Monoid D] [Category D] [StrictSMC D] (H : StrictFunctor C D) (K : StrictFunctor B C)
    (F : StrictFunctor A B) : (H.comp K).comp F = H.comp (K.comp F) :=
  StrictFunctor.ext fun _ => rfl

theorem StrictFunctor.comp_id {A B : Type*} [Monoid A] [Category A] [StrictSMC A]
    [Monoid B] [Category B] [StrictSMC B] (F : StrictFunctor A B) :
    F.comp (StrictFunctor.id A) = F :=
  StrictFunctor.ext fun _ => rfl

/-- **Theorem 2.3** (Joyal–Street, Theorem 2.3, under the cited result C1). "The
isomorphism classes of anchored diagrams `(Γ, v)` in the free graph monoid `G`,
denoted by `[Γ, v]`, form the free symmetric monoidal category `F_s(G)` over `G`."
Freeness is understood as after the theorem: every graph monoid homomorphism from `G`
into a symmetric strict monoidal category factors through `ι : G → F_s(G)` by exactly
one strict symmetric monoidal functor. -/
theorem isFreeSymmetric : IsFreeSymmetric.{w, v, u', v'} J.Fs G J.ι where
  existsUnique_lift D _ _ _ f := by
    refine ⟨(Syn.lift f).comp J.ofFsStrict, ?_, fun F hF => ?_⟩
    · change f = (Syn.lift f).toGraphMonoidHom.comp (J.ofFsStrict.toGraphMonoidHom.comp J.ι)
      rw [ofFsStrict_comp_ι, Syn.lift_comp_ι]
    · have h₁ : (F.comp J.toFsStrict).toGraphMonoidHom.comp (Syn.ι G) = f := by
        change F.toGraphMonoidHom.comp (J.toFsStrict.toGraphMonoidHom.comp (Syn.ι G)) = f
        rw [toFsStrict_comp_ι, hF]
      have h₂ := Syn.eq_lift f h₁
      calc F = (F.comp J.toFsStrict).comp J.ofFsStrict := by
            rw [StrictFunctor.comp_assoc, toFs_comp_ofFs, StrictFunctor.comp_id]
        _ = (Syn.lift f).comp J.ofFsStrict := by rw [h₂]

/-- **Generation principle** for `F_s(G)` (PLAN.md, Section 2): every morphism of
`F_s(G)` is built from the generators, identities and symmetries by composition and
monoidal product. -/
theorem induction {P : ∀ {a b : J.Fs}, (a ⟶ b) → Prop}
    (h_gen : ∀ x : G.A, P (J.hom (DHom.gen x)))
    (h_id : ∀ a : J.Fs, P (𝟙 a))
    (h_braid : ∀ a b : J.Fs, P (σ_ a b))
    (h_comp : ∀ {a b c : J.Fs} (f : a ⟶ b) (g : b ⟶ c), P f → P g → P (f ≫ g))
    (h_tensor : ∀ {a b c d : J.Fs} (f : a ⟶ b) (g : c ⟶ d), P f → P g → P (f ⊗ₛ g))
    {a b : J.Fs} (f : a ⟶ b) : P f := by
  obtain ⟨f, rfl⟩ := (J.equiv a b).surjective f
  refine Syn.induction (P := fun {a b} f => P (J.toFs.map f)) ?_ ?_ ?_ ?_ ?_ f
  · intro x
    exact (congrArg (fun t => P (J.hom t)) (J.map_gen x)).mpr (h_gen x)
  · intro a
    exact (congrArg (fun t => P t) (J.toFs.map_id a)).mpr (h_id a)
  · intro a b
    exact (congrArg (fun t => P (J.hom t)) (J.map_braid a b)).mpr (h_braid a b)
  · intro a b c f g hf hg
    exact (congrArg (fun t => P t) (J.toFs.map_comp f g)).mpr (h_comp _ _ hf hg)
  · intro a b c d f g hf hg
    exact (congrArg (fun t => P (J.hom t)) (J.map_tensor f g)).mpr (h_tensor _ _ hf hg)

end JoyalStreet

end FreeMarkov
