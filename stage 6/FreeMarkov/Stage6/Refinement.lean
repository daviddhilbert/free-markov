/-
Free Markov categories, Stage 6: the graph monoid homomorphism `f_φ : W(G) → Cau(H)` of (6.1), the
note on `H_{φ⁻¹(pa v) → φ⁻¹(v)}`, and the `φ`-refinement `φ^* : Cau(G) → Cau(H)` (Definition 6.4).

For `φ : H → G` in `FinODAG`, `JG : G.JS`, `JH : H.JS` (the cited result C1 for `W(G)`, `W(H)`):

* `R_preimage_parents`: the vertices of `H_{φ⁻¹(pa v) → φ⁻¹(v)}` outside `φ⁻¹(pa v)` are exactly
  those of `φ⁻¹(v)`; `inD_preimage_parents`: it has no other vertex than those of `φ⁻¹(pa v)` and
  `φ⁻¹(v)`.
* `fPhi φ JH`: `f_φ(v) = φ⁻¹(v)`, `f_φ(ε_v) = ε_{φ⁻¹(v)}`, `f_φ(δ_v) = δ_{φ⁻¹(v)}`,
  `f_φ(κ_v) = [φ⁻¹(v) ‖ φ⁻¹(pa(v))]_{(V_H, K_H)}`; it matches duplicates and discards
  (`fPhi_matches`); the case of an empty fiber (`fPhi_dup_empty`, `fPhi_mech_empty`).
* `refine φ JG JH` (`φ^*`): the unique strict Markov functor `Cau(G) → Cau(H)` agreeing with `f_φ` on
  `W(G)` (`refine_spec`, `eq_refine`), with its values on words and generators.

The cited result C1 enters through `JG` and `JH`.
-/
module

public import FreeMarkov.Stage6.Variables

@[expose] public section

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov JoyalStreet Relation

namespace FinODAG

variable {H G : FinODAG} (φ : H ⟶ G)

/-! ### The note on `H_{φ⁻¹(pa v) → φ⁻¹(v)}` -/

/-- *Section 6.* "`H_{φ⁻¹(pa(v)) → φ⁻¹(v)}` does not contain any vertex that is not already in
`φ⁻¹(pa(v))` or `φ⁻¹(v)`, since `φ` sends a parent of a vertex in `φ⁻¹(v)` either to `v` or to a
parent of `v`": its vertices outside `φ⁻¹(pa v)` are those of `φ⁻¹(v)`. -/
theorem R_preimage_parents (y : Fin G.n) (k : Fin H.n) :
    H.K.R (preimS φ (G.pa y)) (fiber φ y) k ↔ φ.onV k = y := by
  constructor
  · rintro ⟨hk, t, ht, h⟩
    rw [mem_fiber] at ht
    suffices H' : ∀ a, ReflTransGen (H.K.Avoid (preimS φ (G.pa y))) a t →
        a ∉ preimS φ (G.pa y) → φ.onV a = y from H' k h hk
    intro a ha
    induction ha using ReflTransGen.head_induction_on with
    | refl => intro _; exact ht
    | @head a c hac _ ih =>
      intro haS
      have hc := ih hac.2
      rcases φ.map_pa hac.1 with h' | h'
      · exact h'.trans hc
      · rw [hc] at h'
        exact absurd (mem_preimS φ |>.2 h') haS
  · intro hk
    refine ⟨fun h => ?_, k, (mem_fiber φ).2 hk, ReflTransGen.refl⟩
    rw [mem_preimS, hk] at h
    exact G.K.not_mem_pa y h |>.elim

/-- *Section 6.* "But it may contain directed paths with more than one arrow; all the vertices of
such a path are in `φ⁻¹(v)`, except possibly the first one": every vertex of
`H_{φ⁻¹(pa(v)) → φ⁻¹(v)}` is in `φ⁻¹(pa(v))` or in `φ⁻¹(v)`. -/
theorem inD_preimage_parents (y : Fin G.n) {k : Fin H.n}
    (h : H.K.InD (preimS φ (G.pa y)) (fiber φ y) k) : k ∈ preimS φ (G.pa y) ∨ k ∈ fiber φ y := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ((mem_fiber φ).2 ((R_preimage_parents φ y k).1 h))

/-! ### `f_φ` -/

variable (JH : H.JS)

/-- The object `φ⁻¹(v)` of `Cau(H)`. -/
noncomputable abbrev objW (y : Fin G.n) : JH.FsM := JH.wordM (finWord (fiber φ y))

theorem lift_objW (v : FreeMonoid (Fin G.n)) :
    FreeMonoid.lift (objW φ JH) v = JH.wordM (preimW φ v) := by
  induction v using FreeMonoid.inductionOn' with
  | one => rfl
  | of_mul y v ih =>
    rw [map_mul, ih, preimW_mul, FreeMonoid.lift_eval_of, preimW_of]
    rfl

theorem eSrc (y : Fin G.n) :
    FreeMonoid.lift (objW φ JH) (G.K.sig.src y) = JH.projM.obj (Fs.of JH (finWord (preimS φ (G.pa y)))) := by
  rw [lift_objW, src_mech, preimW_finWord]
  rfl

theorem eTgt (y : Fin G.n) :
    JH.projM.obj (Fs.of JH (finWord (fiber φ y))) = objW φ JH (G.K.sig.out y) := rfl

/-- The morphism `[φ⁻¹(v) ‖ φ⁻¹(pa(v))]_{(V_H, K_H)}` of (6.1), with its domain written as
`f_φ(pa(v))`. -/
noncomputable def mechImage (y : Fin G.n) :
    FreeMonoid.lift (objW φ JH) (G.K.sig.src y) ⟶ objW φ JH (G.K.sig.out y) :=
  eqToHom (eSrc φ JH y) ≫ EffSig.freeEffect JH (preimS φ (G.pa y)) (fiber φ y) ≫ eqToHom (eTgt φ JH y)

theorem arrow_mechImage (y : Fin G.n) :
    Arrow.mk (mechImage φ JH y) = Arrow.mk (EffSig.freeEffect JH (preimS φ (G.pa y)) (fiber φ y)) := by
  simp [mechImage]

/-- *Section 6, (6.1).* The graph monoid homomorphism **`f_φ : W(G) → Cau(H)`**: `f_φ(v) = φ⁻¹(v)`,
`f_φ(ε_v) = ε_{φ⁻¹(v)}`, `f_φ(δ_v) = δ_{φ⁻¹(v)}`, `f_φ(κ_v) = [φ⁻¹(v) ‖ φ⁻¹(pa(v))]_{(V_H, K_H)}`. -/
noncomputable def fPhi : G.W.toGraphMonoid.Hom (graphMonoid JH.FsM) :=
  G.K.sig.toHom (objW φ JH) (mechImage φ JH)

/-- "So `f_φ` is a graph monoid homomorphism into the underlying graph monoid of `Cau(H)` that
matches duplicates and discards." -/
theorem fPhi_matches : G.W.MatchesDupDisc (fPhi φ JH) := G.K.sig.toHom_matches _ _

/-- (6.1): `f_φ(v) = φ⁻¹(v)`. -/
theorem fPhi_V (v : FreeMonoid (Fin G.n)) : (fPhi φ JH).V v = JH.wordM (preimW φ v) :=
  lift_objW φ JH v

/-- (6.1): `f_φ(δ_v) = δ_{φ⁻¹(v)}`. -/
theorem fPhi_dup (y : Fin G.n) :
    (fPhi φ JH).A (.dup y) = Arrow.mk (δ_ (JH.wordM (preimW φ (FreeMonoid.of y)))) := by
  rw [preimW_of]; rfl

/-- (6.1): `f_φ(ε_v) = ε_{φ⁻¹(v)}`. -/
theorem fPhi_disc (y : Fin G.n) :
    (fPhi φ JH).A (.disc y) = Arrow.mk (ε_ (JH.wordM (preimW φ (FreeMonoid.of y)))) := by
  rw [preimW_of]; rfl

/-- (6.1): `f_φ(κ_v) = [φ⁻¹(v) ‖ φ⁻¹(pa(v))]_{(V_H, K_H)}`, a morphism `φ⁻¹(pa(v)) → φ⁻¹(v)`. -/
theorem fPhi_mech (y : Fin G.n) :
    (fPhi φ JH).A (.mech y) = Arrow.mk (EffSig.freeEffect JH (preimS φ (G.pa y)) (fiber φ y)) :=
  arrow_mechImage φ JH y

/-- *Section 6.* "If `φ⁻¹(v) = ∅` then `f_φ(ε_v) = f_φ(δ_v) = 1_∅`." -/
theorem fPhi_dup_empty {y : Fin G.n} (hy : fiber φ y = ∅) :
    (fPhi φ JH).A (.dup y) = Arrow.mk (𝟙 (1 : JH.FsM)) := by
  change Arrow.mk (δ_ (JH.wordM (finWord (fiber φ y)))) = _
  rw [hy, finWord_empty]
  exact copy_one

theorem fPhi_disc_empty {y : Fin G.n} (hy : fiber φ y = ∅) :
    (fPhi φ JH).A (.disc y) = Arrow.mk (𝟙 (1 : JH.FsM)) := by
  change Arrow.mk (ε_ (JH.wordM (finWord (fiber φ y)))) = _
  rw [hy, finWord_empty]
  exact congrArg Arrow.mk discard_one

/-- *Section 6.* "... and `f_φ(κ_v)` is the discard on `φ⁻¹(pa(v))`." -/
theorem fPhi_mech_empty {y : Fin G.n} (hy : fiber φ y = ∅) :
    (fPhi φ JH).A (.mech y) =
      Arrow.mk (ε_ (JH.wordM (finWord (preimS φ (G.pa y))))) := by
  rw [fPhi_mech]
  have e : JH.projM.obj (Fs.of JH (finWord (fiber φ y))) = 1 := by
    rw [hy, finWord_empty]; rfl
  rw [← Arrow.arrow_mk_comp_eqToHom _ e, eq_discard (_ ≫ eqToHom e)]
  rfl

/-! ### The `φ`-refinement -/

variable (JG : G.JS)

/-- *Definition 6.4* (Refinement). "Since `Cau(G)` is free over `W(G)` and `f_φ` matches duplicates
and discards, there is exactly one strict Markov functor that agrees with `f_φ` on `W(G)`. It is
called the **`φ`-refinement** `φ^* : Cau(G) → Cau(H)`." -/
noncomputable def refine : StrictMarkovFunctor JG.FsM JH.FsM :=
  JG.lift (fPhi φ JH) (fPhi_matches φ JH)

/-- `φ^*` agrees with `f_φ` on `W(G)`. -/
theorem refine_spec : fPhi φ JH = (refine φ JH JG).toGraphMonoidHom.comp JG.iM :=
  lift_spec _ _

/-- *Definition 6.4.* "So `φ^*` is unique": every strict Markov functor `Cau(G) → Cau(H)` that agrees
with `f_φ` on `W(G)` is `φ^*`. -/
theorem eq_refine (F : StrictMarkovFunctor JG.FsM JH.FsM)
    (hF : fPhi φ JH = F.toGraphMonoidHom.comp JG.iM) : F = refine φ JH JG :=
  eq_lift _ _ F hF

theorem refine_obj (v : FreeMonoid (Fin G.n)) :
    (refine φ JH JG).obj (JG.wordM v) = JH.wordM (preimW φ v) :=
  (lift_obj _ _ v).trans (fPhi_V φ JH v)

theorem refine_gen (x : G.W.A) :
    Arrow.mk ((refine φ JH JG).map (JG.projM.map (JG.hom (DHom.gen x)))) = (fPhi φ JH).A x :=
  lift_gen _ _ x

/-- `φ^*(κ_v) = [φ⁻¹(v) ‖ φ⁻¹(pa(v))]_{(V_H, K_H)}`. -/
theorem refine_mechK (y : Fin G.n) :
    Arrow.mk ((refine φ JH JG).map (JG.projM.map (EffSig.mechK JG y))) =
      Arrow.mk (EffSig.freeEffect JH (preimS φ (G.pa y)) (fiber φ y)) := by
  rw [← fPhi_mech, ← refine_gen]
  exact (refine φ JH JG).toFunctor.mk_map_congr (JG.projM.mk_map_congr (EffSig.arrow_mechK y))

end FinODAG

end FreeMarkov
