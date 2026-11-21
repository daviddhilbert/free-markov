/-
Free Markov categories, Stage 5: the strictification of a Markov category (cited result C2) and
effects in an arbitrary Markov category (end of Section 5).

* `Strictification M Str`: **cited result C2** (Mac Lane coherence; Joyal–Street §1.1; Mac Lane–Paré
  §2; Fritz 2020, Proposition 10.16), stating exactly what the end of Section 5 takes from these
  sources: a strict Markov category `str(M) = Str` whose objects are the words over the objects of
  `M`, and the evaluation `eval : str(M) → M`, a Markov functor (strong symmetric monoidal, matching
  duplicates and discards) that is full and faithful, given on objects by
  `eval(∅) = 1`, `eval(a) = a`, `eval(a_1 … a_{n+1}) = eval(a_1 … a_n) ⊗ a_{n+1}`.
  `Strictification.EvalStrict`: the last clause, "`eval` is strict when `M` is strict".
* `straight_str`: "`str(M)` is straight, since its objects form a free monoid" (proved).
* `Strictification.MData`, `MData.effect`: effects in an arbitrary Markov category `M`: for objects
  `a_1, …, a_n` of `M` and morphisms `κ_i : eval(w_{S_i}) → a_i`, the morphism
  `eval([T ‖ S]_{(W,K)}) : eval(w_S) → eval(w_T)` with `w_i` the word `a_i` of length one.
* `MData.effect_strict`: if `M` is strict (and `eval` is strict), this is the effect formed in `M`
  from the `a_i` and the `κ_i` as in Definition 5.4 ("this follows from Proposition 5.6 if `M` is
  straight and from Remark 5.7 in general").

The cited results used: C2 (`Strictification`) for the effects in an arbitrary `M`, and C1 (`J`).
-/
module

public import FreeMarkov.Stage5.Effect

@[expose] public section

universe v u

namespace FreeMarkov

open CategoryTheory MonoidalCategory ComonObj StrictSMC StrictMarkov JoyalStreet

/-- **Cited result C2** (Section 5, after Remark 5.7; Mac Lane's coherence theorem, Joyal–Street
§1.1, Mac Lane–Paré §2, Fritz 2020, Proposition 10.16).  For a Markov category `M`: a strict Markov
category `str(M)` (here `Str`) whose objects are the words of the free monoid `W(M₀)`, and the
evaluation functor `eval : str(M) → M` such that

1. `eval` is a Markov functor: a strong symmetric monoidal functor that matches the duplicates and
   the discards;
2. `eval` is full and faithful ("the arrows `w → w'` in `str(M)` are the arrows
   `eval(w) → eval(w')` in `M`");
3. on objects, `eval(∅) = 1`, `eval(a) = a` (the identity on one-letter words) and
   `eval(a_1 … a_{n+1}) = eval(a_1 … a_n) ⊗ a_{n+1}`.

The clause "`eval` is strict when `M` is strict" is `Strictification.EvalStrict`.  Nothing else is
assumed: in particular not the essential surjectivity of `eval` nor its quasi-inverse, which the
paper mentions but does not use for effects. -/
structure Strictification (M : Type u) [Category.{v} M] [MonoidalCategory M] [MarkovCategory M] (Str : Type u) [Monoid Str] [Category.{v} Str] [StrictMarkov Str] where
  /-- The objects of `str(M)` are the words over the objects of `M`. -/
  words : Str ≃* FreeMonoid M
  /-- The evaluation functor. -/
  eval : Str ⥤ M
  /-- `eval` is strong symmetric monoidal. -/
  braided : eval.Braided
  /-- `eval` matches the duplicates. -/
  map_copy : letI := braided; ∀ w : Str,
    eval.map Δ[w] ≫ (Functor.Monoidal.μIso eval w w).inv = Δ[eval.obj w]
  /-- `eval` matches the discards. -/
  map_discard : letI := braided; ∀ w : Str,
    eval.map ε[w] ≫ (Functor.Monoidal.εIso eval).inv = ε[eval.obj w]
  /-- `eval` is full. -/
  full : eval.Full
  /-- `eval` is faithful. -/
  faithful : eval.Faithful
  /-- `eval(∅) = 1`. -/
  eval_one : eval.obj 1 = 𝟙_ M
  /-- `eval(a) = a` for a word `a` of length one. -/
  eval_of (a : M) : eval.obj (words.symm (FreeMonoid.of a)) = a
  /-- `eval(a_1 … a_{n+1}) = eval(a_1 … a_n) ⊗ a_{n+1}` for `n ≥ 1`. -/
  eval_snoc (w : FreeMonoid M) (a : M) (hw : w ≠ 1) :
    eval.obj (words.symm (w * FreeMonoid.of a)) = eval.obj (words.symm w) ⊗ a

namespace Strictification

variable {M : Type u} [Category.{v} M] [MonoidalCategory M] [MarkovCategory M]
  {Str : Type u} [Monoid Str] [Category.{v} Str] [StrictMarkov Str] (T : Strictification M Str)

/-- **C2, last clause.** "If `M` is itself strict then `eval` is a strict Markov functor": for a
strict Markov category `C` (with its Markov structure in Mathlib's sense from the bridge), `eval` is
the underlying functor of a strict Markov functor `str(C) → C`, and its structure isomorphisms are
identities. -/
structure EvalStrict {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C]
    (T : Strictification C Str) : Prop where
  strict : ∃ F : StrictMarkovFunctor Str C, F.toFunctor = T.eval ∧
    (∀ v w : Str, Arrow.mk (@Functor.Monoidal.μIso _ _ _ _ _ _ T.eval T.braided.toMonoidal v w).hom =
      Arrow.mk (𝟙 (T.eval.obj (v * w)))) ∧
    Arrow.mk (@Functor.Monoidal.εIso _ _ _ _ _ _ T.eval T.braided.toMonoidal).hom =
      Arrow.mk (𝟙 (T.eval.obj 1))

/-- The one-letter word `a`. -/
def letter (a : M) : Str := T.words.symm (FreeMonoid.of a)

theorem eval_letter (a : M) : T.eval.obj (T.letter a) = a := T.eval_of a

end Strictification

/-- "Note that `str(M)` is straight, since its objects form a free monoid." -/
theorem straight_of_mulEquiv {Str : Type*} [Monoid Str] {X : Type*} (e : Str ≃* FreeMonoid X) :
    Straight Str := by
  have hlen : ∀ w : Str, (FreeMonoid.toList (e w)).length = 0 → w = 1 := fun w h => by
    have : e w = 1 := FreeMonoid.toList.injective (List.eq_nil_of_length_eq_zero h)
    simpa using congrArg e.symm this
  refine ⟨fun w hw => hlen w ?_, fun w n hn hw => hlen w ?_⟩
  · have := congrArg (fun x => (FreeMonoid.toList (e x)).length) hw
    simp only [map_mul, FreeMonoid.toList_mul, List.length_append] at this
    omega
  · have := congrArg (fun x => (FreeMonoid.toList (e x)).length) hw
    simp only [map_pow, map_one, FreeMonoid.toList_one, List.length_nil] at this
    have hp : ∀ m, (FreeMonoid.toList (e w ^ m)).length = m * (FreeMonoid.toList (e w)).length := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, FreeMonoid.toList_mul, List.length_append, ih, Nat.succ_mul]
    rw [hp] at this
    rcases Nat.mul_eq_zero.1 this with h | h
    · omega
    · exact h

theorem Strictification.straight_str {M : Type u} [Category.{v} M] [MonoidalCategory M]
    [MarkovCategory M] {Str : Type u} [Monoid Str] [Category.{v} Str]
    [StrictMarkov Str] (T : Strictification M Str) : Straight Str :=
  straight_of_mulEquiv T.words

/-! ### Effects in an arbitrary Markov category -/

namespace Strictification

variable {M : Type u} [Category.{v} M] [MonoidalCategory M] [MarkovCategory M]
  {Str : Type u} [Monoid Str] [Category.{v} Str] [StrictMarkov Str] (T : Strictification M Str)
  {n : ℕ}

/-- `w_S` in `str(M)`: the product of the one-letter words `a_i`, `i ∈ S`, in increasing order. -/
abbrev wS (a : Fin n → M) (S : Finset (Fin n)) : Str := FreeMonoid.lift (fun i => T.letter (a i)) (finWord S)

/-- *End of Section 5.* The data of an effect in an arbitrary Markov category `M`: objects
`a_1, …, a_n` of `M`, sets `S_i` with acyclic associated graph, and morphisms
`κ_i : eval(w_{S_i}) → a_i` of `M`. -/
structure MData (n : ℕ) extends EffSig n where
  /-- The objects `a_i`. -/
  a : Fin n → M
  /-- The morphisms `κ_i : eval(w_{S_i}) → a_i`. -/
  κ (i : Fin n) : T.eval.obj (T.wS a (pa i)) ⟶ a i

variable {T}

namespace MData

variable (D : MData T n)

/-- "`κ_i : eval(w_{S_i}) → a_i` a morphism of `M`, that is, a morphism `w_{S_i} → w_i` of
`str(M)`": the preimage under the full functor `eval`. -/
noncomputable def κStr (i : Fin n) : T.wS D.a (D.pa i) ⟶ T.letter (D.a i) :=
  haveI := T.full
  T.eval.preimage (D.κ i ≫ eqToHom (T.eval_letter (D.a i)).symm)

theorem eval_map_κStr (i : Fin n) :
    Arrow.mk (T.eval.map (D.κStr i)) = Arrow.mk (D.κ i) := by
  have := T.full
  rw [κStr, Functor.map_preimage, Arrow.arrow_mk_comp_eqToHom]

/-- The `(W, K)` data in `str(M)`, with `w_i` the word `a_i` of length one. -/
noncomputable abbrev toEffData : EffData Str n where
  toEffSig := D.toEffSig
  w i := T.letter (D.a i)
  κ := D.κStr

variable (J : JoyalStreet D.sig.G.toFreeGraphMonoid)

/-- *End of Section 5.* The **effect in `M`** of `S` on `T` over the data `(a_i, S_i, κ_i)`:
`eval([T ‖ S]_{(W,K)}) : eval(w_S) → eval(w_T)`. -/
noncomputable def effect (S T' : Finset (Fin n)) : T.eval.obj (T.wS D.a S) ⟶ T.eval.obj (T.wS D.a T') :=
  T.eval.map (D.toEffData.effect J S T')

end MData

end Strictification

/-! ### Agreement with Definition 5.4 for strict `M` -/

namespace EffData

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C] {n : ℕ}

/-- Effects depend only on the objects and on the morphisms `κ_i` as arrows. -/
theorem effect_mk_congr (K : EffSig n) (J : JoyalStreet K.sig.G.toFreeGraphMonoid)
    (w₁ w₂ : Fin n → C) (κ₁ : ∀ i, FreeMonoid.lift w₁ (finWord (K.pa i)) ⟶ w₁ i)
    (κ₂ : ∀ i, FreeMonoid.lift w₂ (finWord (K.pa i)) ⟶ w₂ i) (hw : w₁ = w₂)
    (hκ : ∀ i, Arrow.mk (κ₁ i) = Arrow.mk (κ₂ i)) (S T : Finset (Fin n)) :
    Arrow.mk ((EffData.mk K w₁ κ₁).effect J S T) = Arrow.mk ((EffData.mk K w₂ κ₂).effect J S T) := by
  subst hw
  have : κ₁ = κ₂ := funext fun i => Arrow.eq_of_mk_eq (hκ i)
  subst this
  rfl

end EffData

namespace Strictification

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C]
  {Str : Type u} [Monoid Str] [Category.{v} Str] [StrictMarkov Str] {T : Strictification C Str}
  {n : ℕ}

omit [Monoid C] [StrictMarkov C] in
theorem mk_eqToHom_comp' {X Y Z : C} (h : X = Y) (f : Y ⟶ Z) :
    Arrow.mk (eqToHom h ≫ f) = Arrow.mk f := by subst h; simp

theorem obj_wS {F : StrictMarkovFunctor Str C} (hF : F.toFunctor = T.eval) (a : Fin n → C)
    (S : Finset (Fin n)) : F.obj (T.wS a S) = FreeMonoid.lift a (finWord S) := by
  rw [← StrictFunctor.lift_comp F.toStrictFunctor]
  have : (F.obj ∘ fun i => T.letter (a i)) = a := funext fun i => by
    change F.toFunctor.obj (T.letter (a i)) = a i
    rw [hF]
    exact T.eval_letter (a i)
  rw [this]

/-- The data `(a_i, S_i, κ_i)` read directly in the strict Markov category `C`: the morphisms
`κ_i : a_{S_i} → a_i` (through `eval(w_{S_i}) = a_{S_i}`). -/
noncomputable def MData.direct (D : MData T n) {F : StrictMarkovFunctor Str C}
    (hF : F.toFunctor = T.eval) : EffData C n where
  toEffSig := D.toEffSig
  w := D.a
  κ i := eqToHom (by rw [← obj_wS hF D.a (D.pa i), hF]) ≫ D.κ i

/-- *End of Section 5.* "If `M` is itself strict then `eval` is a strict Markov functor, and hence
this is the morphism `[T ‖ S]` formed in `M` from the objects `a_i` and the morphisms `κ_i` as in
Definition 5.4; this follows from Proposition 5.6 if `M` is straight and from Remark 5.7 in
general." -/
theorem MData.effect_strict (D : MData T n) (hT : T.EvalStrict)
    (J : JoyalStreet D.sig.G.toFreeGraphMonoid) (S T' : Finset (Fin n)) :
    ∃ F : StrictMarkovFunctor Str C, ∃ hF : F.toFunctor = T.eval,
      Arrow.mk (D.effect J S T') = Arrow.mk ((D.direct hF).effect J S T') := by
  obtain ⟨F, hF, -⟩ := hT.strict
  refine ⟨F, hF, ?_⟩
  have h₁ : Arrow.mk (D.effect J S T') = Arrow.mk (F.map (D.toEffData.effect J S T')) := by
    unfold MData.effect
    rw [← hF]
  refine h₁.trans ((D.toEffData.prop_5_6 J F S T').trans ?_)
  refine EffData.effect_mk_congr D.toEffSig J _ _ _ _ ?_ (fun i => ?_) S T'
  · funext i
    change F.toFunctor.obj (T.letter (D.a i)) = D.a i
    rw [hF]; exact T.eval_letter _
  · change Arrow.mk (eqToHom _ ≫ F.map (D.κStr i)) = Arrow.mk (eqToHom _ ≫ D.κ i)
    rw [mk_eqToHom_comp', mk_eqToHom_comp']
    refine Eq.trans ?_ (D.eval_map_κStr i)
    rw [← hF]

end Strictification

end FreeMarkov
