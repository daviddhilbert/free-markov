/-
Trial of design decision D2 (PLAN.md), second part: interpreting terms of
`Syn_s(G)` in a symmetric strict monoidal category `D` along a graph monoid
homomorphism `f`, where the casts come from `f.V.map_mul`, and checking the
hardest cases of soundness (associativity of `⊗`, the hexagon) in the `Arrow`
calculus.  Not part of the library; compiled by `scripts/verify.py`.
-/
import FreeMarkov.Stage0

universe w v u' v'

namespace D2Interp

open CategoryTheory FreeMarkov StrictSMC FreeGraphMonoid

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}
  {D : Type u'} [Monoid D] [Category.{v'} D] [StrictSMC D]
  (f : G.toGraphMonoid.Hom (graphMonoid D))

/-- The value of a term. -/
def interp : ∀ {a b : FreeMonoid S}, G.Term a b → (f.V a ⟶ f.V b)
  | _, _, .gen x => eqToHom (f.s_A x).symm ≫ (f.A x).hom ≫ eqToHom (f.t_A x)
  | _, _, .id a => 𝟙 (f.V a)
  | _, _, .comp t u => interp t ≫ interp u
  | _, _, .tensor t u => eqToHom (f.V.map_mul _ _) ≫ (interp t ⊗ₛ interp u) ≫
      eqToHom (f.V.map_mul _ _).symm
  | _, _, .braid a b => eqToHom (f.V.map_mul a b) ≫ σ_ (f.V a) (f.V b) ≫
      eqToHom (f.V.map_mul b a).symm

theorem arrow_interp_tensor {a b c d : FreeMonoid S} (t : G.Term a b) (u : G.Term c d) :
    Arrow.mk (interp f (t.tensor u)) = Arrow.mk (interp f t ⊗ₛ interp f u) := by
  simp only [interp, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]

theorem arrow_interp_braid (a b : FreeMonoid S) :
    Arrow.mk (interp f (Term.braid (G := G) a b)) = Arrow.mk (σ_ (f.V a) (f.V b)) := by
  simp only [interp, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]

theorem arrow_interp_cast {a b a' b' : FreeMonoid S} (ha : a = a') (hb : b = b')
    (t : G.Term a b) : Arrow.mk (interp f (t.cast ha hb)) = Arrow.mk (interp f t) := by
  subst ha hb
  rfl

/-- Soundness for the associativity of `⊗`. -/
theorem sound_tensor_assoc {a b c d e g : FreeMonoid S} (t : G.Term a b) (u : G.Term c d)
    (w : G.Term e g) :
    Arrow.mk (interp f ((t.tensor u).tensor w)) = Arrow.mk (interp f (t.tensor (u.tensor w))) := by
  rw [arrow_interp_tensor, arrow_interp_tensor]
  refine (mk_tensorHom_congr (arrow_interp_tensor f t u) rfl).trans ?_
  refine Eq.trans ?_ (mk_tensorHom_congr rfl (arrow_interp_tensor f u w)).symm
  exact tensorHom_assoc _ _ _

/-- Soundness for the hexagon. -/
theorem sound_hexagon (a b c : FreeMonoid S) :
    Arrow.mk (interp f (Term.braid (G := G) a (b * c))) =
      Arrow.mk (interp f (((Term.braid a b).tensor (Term.id c)).comp
          (((Term.id b).tensor (Term.braid a c)).cast (mul_assoc b a c).symm rfl))) := by
  rw [arrow_interp_braid]
  have e1 : f.V (b * c) = f.V b * f.V c := f.V.map_mul b c
  -- Left side: `σ_{fa, f(bc)}`, retyped to `σ_{fa, fb * fc}`.
  have hl : Arrow.mk (σ_ (f.V a) (f.V (b * c))) = Arrow.mk (σ_ (f.V a) (f.V b * f.V c)) := by
    rw [e1]
  rw [hl, hexagon]
  simp only [interp]
  refine Arrow.mk_comp_congr ?_ ?_
  · simp only [Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]
    exact mk_tensorHom_congr (by simp) rfl
  · rw [arrow_interp_cast]
    simp only [Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom, interp]
    exact mk_tensorHom_congr rfl (by simp)

end D2Interp
