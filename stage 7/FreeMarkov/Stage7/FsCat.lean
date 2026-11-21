/-
Free Markov categories, Stage 7: the symmetric strict monoidal category `F_s(G)` of classes of
diagrams, built without the cited result C1, and the strict functor `Syn_s(G) → F_s(G)`.

The laws on classes (`Laws.lean`, `Laws2.lean`) make the operations of Stage 1 (gluing,
disjoint union, node-free and one-node diagrams) a `StrictSMC` on the words, `FsC G`.  Its
morphisms `a ⟶ b` are Stage 1's `DHom G a b`, exactly the morphisms of `J.Fs` for an instance
`J` of C1.  The universal property of `Syn_s(G)` (Stage 0) then gives the strict functor
`FsC.fromSyn G : Syn_s(G) → F_s(G)` sending generators to one-node diagrams; it is the map that
`JoyalStreet G` asks to be bijective.
-/
module

public import FreeMarkov.Stage7.Laws2

@[expose] public section

universe w v

namespace FreeMarkov

open CategoryTheory StrictSMC FreeGraphMonoid Diagram

/-! ### The laws on classes -/

namespace DClass

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

theorem idD_comp (c : DClass G) : (mk (idD G c.dom)).comp c = c := by
  induction c using ind with
  | h n m Γ =>
    have h : (idD G Γ.domWord).codWord = Γ.domWord := by simp
    rw [dom_mk, mk_comp _ _ h, mk_idD_glue]

theorem comp_idD (c : DClass G) : c.comp (mk (idD G c.cod)) = c := by
  induction c using ind with
  | h n m Γ =>
    have h : Γ.codWord = (idD G Γ.codWord).domWord := by simp
    rw [cod_mk, mk_comp _ _ h, mk_glue_idD]

theorem comp_assoc {c d e : DClass G} (h₁ : c.cod = d.dom) (h₂ : d.cod = e.dom) :
    (c.comp d).comp e = c.comp (d.comp e) := by
  induction c using ind with
  | h _ _ Γ => induction d using ind with
    | h _ _ Δ => induction e using ind with
      | h _ _ Ε =>
        simp only [cod_mk, dom_mk] at h₁ h₂
        rw [mk_comp _ _ h₁, mk_comp _ _ h₂, mk_comp _ _ (by rw [glue_codWord]; exact h₂),
          mk_comp _ _ (by rw [glue_domWord]; exact h₁), mk_glue_assoc]

theorem tensor_assoc (c d e : DClass G) : (c.tensor d).tensor e = c.tensor (d.tensor e) := by
  induction c using ind with
  | h _ _ Γ => induction d using ind with
    | h _ _ Δ => induction e using ind with
      | h _ _ Ε => rw [mk_tensor, mk_tensor, mk_tensor, mk_tensor, mk_tensor_assoc]

theorem idD_one_tensor (c : DClass G) : (mk (idD G 1)).tensor c = c := by
  induction c using ind with
  | h _ _ Γ => rw [mk_tensor, mk_idD_one_tensor]

theorem tensor_idD_one (c : DClass G) : c.tensor (mk (idD G 1)) = c := by
  induction c using ind with
  | h _ _ Γ => rw [mk_tensor, mk_tensor_idD_one]

theorem idD_tensor_idD (a c : FreeMonoid S) :
    (mk (idD G a)).tensor (mk (idD G c)) = mk (idD G (a * c)) := by
  rw [mk_tensor, mk_idD_tensor_idD]

theorem interchange {c c' d d' : DClass G} (h₁ : c.cod = c'.dom) (h₂ : d.cod = d'.dom) :
    (c.comp c').tensor (d.comp d') = (c.tensor d).comp (c'.tensor d') := by
  induction c using ind with
  | h _ _ Γ => induction c' using ind with
    | h _ _ Γ' => induction d using ind with
      | h _ _ Δ => induction d' using ind with
        | h _ _ Δ' =>
          simp only [cod_mk, dom_mk] at h₁ h₂
          have h : (Γ.tensor Δ).codWord = (Γ'.tensor Δ').domWord := by simp [h₁, h₂]
          rw [mk_comp _ _ h₁, mk_comp _ _ h₂, mk_tensor, mk_tensor, mk_tensor, mk_comp _ _ h,
            mk_interchange]

theorem braid_natural (c d : DClass G) :
    (c.tensor d).comp (mk (braidD G c.cod d.cod)) = (mk (braidD G c.dom d.dom)).comp (d.tensor c) := by
  induction c using ind with
  | h _ _ Γ => induction d using ind with
    | h _ _ Δ =>
      have h : (Γ.tensor Δ).codWord = (braidD G Γ.codWord Δ.codWord).domWord := by simp
      have h' : (braidD G Γ.domWord Δ.domWord).codWord = (Δ.tensor Γ).domWord := by simp
      rw [cod_mk, cod_mk, dom_mk, dom_mk, mk_tensor, mk_tensor, mk_comp _ _ h, mk_comp _ _ h',
        mk_braid_natural]

theorem braid_braid (a b : FreeMonoid S) :
    (mk (braidD G a b)).comp (mk (braidD G b a)) = mk (idD G (a * b)) := by
  have h : (braidD G a b).codWord = (braidD G b a).domWord := by simp
  rw [mk_comp _ _ h, mk_braid_braid]

theorem hexagon (a b c : FreeMonoid S) :
    ((mk (braidD G a b)).tensor (mk (idD G c))).comp ((mk (idD G b)).tensor (mk (braidD G a c))) =
      mk (braidD G a (b * c)) := by
  have h : ((braidD G a b).tensor (idD G c)).codWord =
      ((idD G b).tensor (braidD G a c)).domWord := by simp [mul_assoc]
  rw [mk_tensor, mk_tensor, mk_comp _ _ h, mk_hexagon]

end DClass

/-! ### The category -/

namespace DHom

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

theorem id_comp' {a b : FreeMonoid S} (f : DHom G a b) : (DHom.id G a).comp f = f := by
  ext1
  have := DClass.idD_comp f.1
  rw [f.2.1] at this
  exact this

theorem comp_id' {a b : FreeMonoid S} (f : DHom G a b) : f.comp (DHom.id G b) = f := by
  ext1
  have := DClass.comp_idD f.1
  rw [f.2.2] at this
  exact this

theorem assoc' {a b c d : FreeMonoid S} (f : DHom G a b) (g : DHom G b c) (h : DHom G c d) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext1
  exact DClass.comp_assoc (f.2.2.trans g.2.1.symm) (g.2.2.trans h.2.1.symm)

theorem tensor_id' (a c : FreeMonoid S) :
    (DHom.id G a).tensor (DHom.id G c) = DHom.id G (a * c) := by
  ext1
  exact DClass.idD_tensor_idD a c

theorem tensor_comp' {a₁ a₂ a₃ c₁ c₂ c₃ : FreeMonoid S} (f : DHom G a₁ a₂) (f' : DHom G a₂ a₃)
    (g : DHom G c₁ c₂) (g' : DHom G c₂ c₃) :
    (f.comp f').tensor (g.comp g') = (f.tensor g).comp (f'.tensor g') := by
  ext1
  exact DClass.interchange (f.2.2.trans f'.2.1.symm) (g.2.2.trans g'.2.1.symm)

theorem braid_natural' {a b c d : FreeMonoid S} (f : DHom G a b) (g : DHom G c d) :
    (f.tensor g).comp (DHom.braid G b d) = (DHom.braid G a c).comp (g.tensor f) := by
  ext1
  have := DClass.braid_natural f.1 g.1
  rw [f.2.1, f.2.2, g.2.1, g.2.2] at this
  exact this

theorem braid_braid' (a b : FreeMonoid S) :
    (DHom.braid G a b).comp (DHom.braid G b a) = DHom.id G (a * b) := by
  ext1
  exact DClass.braid_braid a b

end DHom

variable {S : Type w}

/-- *Section 2.* The symmetric strict monoidal category `F_s(G)` of a free graph monoid `G`,
built from the combinatorial diagrams of Stage 1 without the cited result C1: objects the words
over `S`, morphisms `a → b` the isomorphism classes of anchored diagrams from `a` to `b`
(`DHom G a b`), composition by gluing, monoidal product by disjoint union, identities and
symmetries by node-free diagrams. -/
def FsC (_G : FreeGraphMonoid.{w, v} S) : Type w := FreeMonoid S

namespace FsC

variable (G : FreeGraphMonoid.{w, v} S)

instance : Monoid (FsC G) := inferInstanceAs (Monoid (FreeMonoid S))

/-- A word, regarded as an object of `F_s(G)`. -/
def of (a : FreeMonoid S) : FsC G := a

noncomputable instance category : Category.{max w v} (FsC G) where
  Hom a b := DHom G a b
  id a := DHom.id G a
  comp f g := DHom.comp f g
  id_comp f := DHom.id_comp' f
  comp_id f := DHom.comp_id' f
  assoc f g h := DHom.assoc' f g h

variable {G}

/-- A class from `a` to `b`, as a morphism of `F_s(G)`. -/
def hom {a b : FreeMonoid S} (f : DHom G a b) : FsC.of G a ⟶ FsC.of G b := f

/-- The class `[Γ, v]` underlying a morphism of `F_s(G)`. -/
def cls {a b : FsC G} (f : a ⟶ b) : DClass G :=
  Subtype.val (p := fun c : DClass G => c.dom = a ∧ c.cod = b) f

theorem cls_dom {a b : FsC G} (f : a ⟶ b) : (cls f).dom = a :=
  (Subtype.property (p := fun c : DClass G => c.dom = a ∧ c.cod = b) f).1

theorem cls_cod {a b : FsC G} (f : a ⟶ b) : (cls f).cod = b :=
  (Subtype.property (p := fun c : DClass G => c.dom = a ∧ c.cod = b) f).2

theorem cls_comp {a b c : FsC G} (f : a ⟶ b) (g : b ⟶ c) :
    cls (f ≫ g) = (cls f).comp (cls g) := rfl

theorem cls_id (a : FsC G) : cls (𝟙 a) = DClass.mk (Diagram.idD G a) := rfl

theorem cls_comp_eqToHom_comp {a b b' c : FsC G} (f : a ⟶ b) (h : b = b') (g : b' ⟶ c) :
    cls (f ≫ eqToHom h ≫ g) = (cls f).comp (cls g) := by
  subst h
  rw [eqToHom_refl, Category.id_comp]
  rfl

/-- Morphisms of `F_s(G)` with the same class are equal as arrows. -/
theorem arrow_eq_of_cls_eq {a b a' b' : FsC G} {f : a ⟶ b} {g : a' ⟶ b'}
    (h : cls f = cls g) : Arrow.mk f = Arrow.mk g := by
  have ha : a = a' := (cls_dom f).symm.trans (h ▸ cls_dom g)
  have hb : b = b' := (cls_cod f).symm.trans (h ▸ cls_cod g)
  subst ha hb
  exact congrArg Arrow.mk (Subtype.ext h)

variable (G)

noncomputable instance strictSMC : StrictSMC (FsC G) where
  tensorHom f g := DHom.tensor f g
  braid a b := DHom.braid G a b
  tensorHom_id a c := DHom.tensor_id' a c
  tensorHom_comp f f' g g' := DHom.tensor_comp' f f' g g'
  tensorHom_assoc x y z := arrow_eq_of_cls_eq (DClass.tensor_assoc (cls x) (cls y) (cls z))
  id_one_tensorHom f := arrow_eq_of_cls_eq (DClass.idD_one_tensor (cls f))
  tensorHom_id_one f := arrow_eq_of_cls_eq (DClass.tensor_idD_one (cls f))
  braid_natural f g := DHom.braid_natural' f g
  braid_braid a b := DHom.braid_braid' a b
  hexagon a b c := arrow_eq_of_cls_eq ((DClass.hexagon a b c).symm.trans
    (cls_comp_eqToHom_comp (G := G) (a := a * b * c) (b := b * a * c) (b' := b * (a * c))
      (c := b * (c * a)) (DHom.tensor (DHom.braid G a b) (DHom.id G c)) (mul_assoc b a c)
      (DHom.tensor (DHom.id G b) (DHom.braid G a c))).symm)

variable {G}

theorem cls_tensor {a b c d : FsC G} (f : a ⟶ b) (g : c ⟶ d) :
    cls (f ⊗ₛ g) = (cls f).tensor (cls g) := rfl

theorem cls_braid (a b : FsC G) : cls (σ_ a b) = DClass.mk (Diagram.braidD G a b) := rfl

variable (G)

/-- *Section 2.* The "obvious graph monoid homomorphism `G → F_s(G)`": the identity on words,
and each arrow to the class of its one-node diagram. -/
noncomputable def ι : G.toGraphMonoid.Hom (graphMonoid (FsC G)) where
  V := MonoidHom.id (FreeMonoid S)
  A x := Arrow.mk (hom (DHom.gen x))
  s_A _ := rfl
  t_A _ := rfl

/-- The strict symmetric monoidal functor `Syn_s(G) → F_s(G)` given by the universal property of
`Syn_s(G)`: a formal composite of generators, identities and symmetries goes to the class of the
corresponding gluing of one-node and node-free diagrams. -/
noncomputable def fromSyn : StrictFunctor G.Syn (FsC G) := Syn.lift (ι G)

variable {G}

/-- The comparison map on hom-sets: `Syn_s(G)(a, b) → {[Γ, v] : dom = a, cod = b}`. -/
noncomputable def toDHom {a b : FreeMonoid S} (f : Syn.of G a ⟶ Syn.of G b) : DHom G a b :=
  (fromSyn G).map f

theorem toDHom_gen (x : G.A) : toDHom (Syn.gen x) = DHom.gen x :=
  Arrow.eq_of_mk_eq (congrArg (fun F => F.A x) (Syn.lift_comp_ι (ι G)))

theorem toDHom_id (a : FreeMonoid S) : toDHom (𝟙 (Syn.of G a)) = DHom.id G a :=
  (fromSyn G).map_id _

theorem toDHom_comp {a b c : FreeMonoid S} (f : Syn.of G a ⟶ Syn.of G b)
    (g : Syn.of G b ⟶ Syn.of G c) : toDHom (f ≫ g) = (toDHom f).comp (toDHom g) :=
  (fromSyn G).map_comp f g

theorem toDHom_tensor {a b c d : FreeMonoid S} (f : Syn.of G a ⟶ Syn.of G b)
    (g : Syn.of G c ⟶ Syn.of G d) : toDHom (f ⊗ₛ g) = (toDHom f).tensor (toDHom g) :=
  Arrow.eq_of_mk_eq ((fromSyn G).map_tensorHom f g)

theorem toDHom_braid (a b : FreeMonoid S) :
    toDHom (σ_ (Syn.of G a) (Syn.of G b)) = DHom.braid G a b :=
  Arrow.eq_of_mk_eq ((fromSyn G).map_braid a b)

end FsC

end FreeMarkov
