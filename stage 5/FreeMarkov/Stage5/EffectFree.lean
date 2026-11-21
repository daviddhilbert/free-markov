/-
Free Markov categories, Stage 5: effects in the free Markov category of a family `K`
(Definition 5.4 and Lemma 5.5 in the free case).

For `K : EffSig n` let `K.sig` be the production signature with letters `1, …, n` and one producer
`κ_i : w_{S_i} → i` for each `i`; its free `DD`-graph monoid is the `W(G)` of Definition 6.2, and
`J.FsM` (for `J : JoyalStreet K.sig.G`) is its free Markov category.

* `finWord S`: the word `w_S` of the elements of `S` in increasing order.
* `IsEffectDiagram S T Γ`: "`Γ` is a diagram `Γ_{[w_T ‖ w_S]}`": its domain is `w_S`, its codomain
  `w_T`, it has exactly one node with the value `κ_i` for each `i ∈ V(G_{S → T}) ∖ S` and no other
  node with the value of a producer (the other nodes are duplicates and discards).  This is the
  description by which Definition 5.4 and the proofs of Lemma 5.5 and Proposition 6.6 recognise the
  fused diagram.  `IsEffect f` is the same condition for a morphism of `F_s(K.sig.G)`.
* `exists_effect`: there is such a morphism (built one vertex at a time).
* `effectDiagram_sameSkeleton`: any two effect diagrams for `(S, T)` have the same skeleton ("the
  morphism that it represents is unique"), `effectDiagram_live`: every node of a producer in an
  effect diagram is live, `effectDiagram_congruent`: two Markov minimal ones are Markov congruent.
* `freeEffect S T`: the effect `[w_T ‖ w_S]` in `J.FsM`; `projM_eq_freeEffect`: every effect diagram
  represents it (independence of the assignment and of the depiction of the multipliers).
* `lemma_5_5_free`: `[T ‖ S] = [T ‖ T_i] ∘ [T_i ‖ S]`, the composite of effect diagrams being an
  effect diagram (`isEffect_comp`).
* `freeEffect_parents`: `[i ‖ S_i] = κ_i`.

The cited result C1 enters through `J`.
-/
module

public import FreeMarkov.Stage5.Graph
public import Mathlib.Data.Finset.Sort

@[expose] public section

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov JoyalStreet Relation

variable {n : ℕ}

/-- `w_S`: the word of the elements of `S` in increasing order ("taken in the increasing order of
`i`"). -/
def finWord (S : Finset (Fin n)) : FreeMonoid (Fin n) := FreeMonoid.ofList (S.sort (· ≤ ·))

theorem finWord_nodup (S : Finset (Fin n)) : (FreeMonoid.toList (finWord S)).Nodup :=
  Finset.sort_nodup _ _

theorem mem_finWord {S : Finset (Fin n)} {i : Fin n} : i ∈ FreeMonoid.toList (finWord S) ↔ i ∈ S :=
  Finset.mem_sort _

namespace EffSig

variable (K : EffSig n)

/-- The production signature of `K`: letters `1, …, n` and one producer `κ_i : w_{S_i} → i`. -/
@[reducible] def sig : ProdSig where
  X := Fin n
  P := Fin n
  out := id
  out_injective := fun _ _ h => h
  src i := finWord (K.pa i)

variable {K}

/-! ### Effect diagrams -/

open Classical in
/-- *Definition 5.4.* `Γ` is an effect diagram `Γ_{[w_T ‖ w_S]}`: domain `w_S`, codomain `w_T`,
exactly one node with the value `κ_i` for each `i ∈ V(G_{S → T}) ∖ S`, and no other node with the
value of a producer. -/
structure IsEffectDiagram (S T : Finset (Fin n)) {N E : Type*} (Γ : Diagram K.sig.G.toFreeGraphMonoid N E) :
    Prop where
  dom : Γ.domWord = finWord S
  cod : Γ.codWord = finWord T
  card (k : Fin n) : Γ.card (.mech k) = if K.R S T k then 1 else 0

variable (J : JoyalStreet K.sig.G.toFreeGraphMonoid)

open Classical in
/-- A morphism of `F_s(K.sig.G)` whose diagrams are effect diagrams. -/
def IsEffect {S T : Finset (Fin n)} (f : Fs.of J (finWord S) ⟶ Fs.of J (finWord T)) : Prop :=
  ∀ k, J.card (.mech k) f = if K.R S T k then 1 else 0

variable {J}

theorem isEffectDiagram_iff {S T : Finset (Fin n)} {f : Fs.of J (finWord S) ⟶ Fs.of J (finWord T)}
    {N E : Type*} [Finite N] [Finite E] {Γ : Diagram K.sig.G.toFreeGraphMonoid N E}
    (hΓ : J.cls f = DClass.mk Γ) : IsEffect J f ↔ IsEffectDiagram S T Γ := by
  have hd : Γ.domWord = finWord S := by rw [← DClass.dom_mk, ← hΓ]; exact J.cls_dom f
  have hc : Γ.codWord = finWord T := by rw [← DClass.cod_mk, ← hΓ]; exact J.cls_cod f
  have hk : ∀ k, J.card (.mech k) f = Γ.card (.mech k) := fun k => by
    unfold JoyalStreet.card; rw [hΓ, DClass.card_mk]
  constructor
  · intro h; exact ⟨hd, hc, fun k => (hk k).symm.trans (h k)⟩
  · intro h k; exact (hk k).trans (h.card k)

/-! ### Building blocks in `F_s(Q.G)` -/

section Blocks

variable {Q : ProdSig} (J : JoyalStreet Q.G.toFreeGraphMonoid)

/-- The generator `δ_x`. -/
noncomputable def dupF (x : Q.X) : Fs.of J (FreeMonoid.of x) ⟶ Fs.of J (FreeMonoid.of x * FreeMonoid.of x) :=
  J.hom (DHom.gen (G := Q.G.toFreeGraphMonoid) (.dup x))

/-- The generator `ε_x`. -/
noncomputable def discF (x : Q.X) : Fs.of J (FreeMonoid.of x) ⟶ Fs.of J 1 :=
  J.hom (DHom.gen (G := Q.G.toFreeGraphMonoid) (.disc x))

/-- The generator `κ_p`. -/
noncomputable def mechF (p : Q.P) : Fs.of J (Q.src p) ⟶ Fs.of J (FreeMonoid.of (Q.out p)) :=
  J.hom (DHom.gen (G := Q.G.toFreeGraphMonoid) (.mech p))

/-- A cast between objects of `F_s(Q.G)`. -/
noncomputable def castF {a b : J.Fs} (h : a = b) : a ⟶ b := eqToHom h

/-! The identifications of objects used below, each with its statement fixed. -/

theorem eNil : Fs.of J (FreeMonoid.ofList ([] : List Q.X)) =
    Fs.of J (FreeMonoid.ofList []) * Fs.of J (FreeMonoid.ofList []) := (mul_one _).symm

theorem eCons (x : Q.X) (l : List Q.X) : Fs.of J (FreeMonoid.ofList (x :: l)) =
    Fs.of J (FreeMonoid.of x) * Fs.of J (FreeMonoid.ofList l) := rfl

theorem eAssoc₁ (x : Q.X) (l : List Q.X) :
    (Fs.of J (FreeMonoid.of x) * Fs.of J (FreeMonoid.of x)) *
        (Fs.of J (FreeMonoid.ofList l) * Fs.of J (FreeMonoid.ofList l)) =
      Fs.of J (FreeMonoid.of x) *
        ((Fs.of J (FreeMonoid.of x) * Fs.of J (FreeMonoid.ofList l)) * Fs.of J (FreeMonoid.ofList l)) := rfl

theorem eAssoc₂ (x : Q.X) (l : List Q.X) :
    Fs.of J (FreeMonoid.of x) * (Fs.of J (FreeMonoid.ofList l) * Fs.of J (FreeMonoid.of x) *
        Fs.of J (FreeMonoid.ofList l)) =
      Fs.of J (FreeMonoid.ofList (x :: l)) * Fs.of J (FreeMonoid.ofList (x :: l)) :=
  (by simp only [mul_assoc] : (FreeMonoid.of x * (FreeMonoid.ofList l * FreeMonoid.of x *
    FreeMonoid.ofList l) : FreeMonoid Q.X) =
    FreeMonoid.of x * FreeMonoid.ofList l * (FreeMonoid.of x * FreeMonoid.ofList l))

theorem eNilOne : Fs.of J (FreeMonoid.ofList ([] : List Q.X)) = Fs.of J 1 := rfl

theorem eOneNil : Fs.of J 1 = Fs.of J (FreeMonoid.ofList ([] : List Q.X)) := rfl

theorem eOneOne : Fs.of J 1 * Fs.of J 1 = Fs.of J (1 : FreeMonoid Q.X) := mul_one _

theorem eSel₁ {x y : Q.X} (hx : x = y) :
    Fs.of J (FreeMonoid.of x) * Fs.of J 1 = Fs.of J (FreeMonoid.of y) := by
  rw [hx]; exact mul_one (FreeMonoid.of y)

theorem eSel₂ (y : Q.X) : Fs.of J 1 * Fs.of J (FreeMonoid.of y) = Fs.of J (FreeMonoid.of y) :=
  one_mul _

theorem eConsR (y : Q.X) (Y : List Q.X) :
    Fs.of J (FreeMonoid.of y) * Fs.of J (FreeMonoid.ofList Y) = Fs.of J (FreeMonoid.ofList (y :: Y)) := rfl

/-- A copy of a word, built from the duplicates on its letters. -/
noncomputable def copyW : (l : List Q.X) →
    (Fs.of J (FreeMonoid.ofList l) ⟶ Fs.of J (FreeMonoid.ofList l) * Fs.of J (FreeMonoid.ofList l))
  | [] => castF J (eNil J)
  | x :: l =>
    castF J (eCons J x l) ≫ (dupF J x ⊗ₛ copyW l) ≫ castF J (eAssoc₁ J x l) ≫
    (𝟙 (Fs.of J (FreeMonoid.of x)) ⊗ₛ (σ_ (Fs.of J (FreeMonoid.of x)) (Fs.of J (FreeMonoid.ofList l)) ⊗ₛ
        𝟙 (Fs.of J (FreeMonoid.ofList l)))) ≫ castF J (eAssoc₂ J x l)

/-- A discard of a word, built from the discards on its letters. -/
noncomputable def discW : (l : List Q.X) → (Fs.of J (FreeMonoid.ofList l) ⟶ Fs.of J 1)
  | [] => castF J (eNilOne J)
  | x :: l => castF J (eCons J x l) ≫ (discF J x ⊗ₛ discW l) ≫ castF J (eOneOne J)

open Classical in
/-- Keep one letter `y` of a word and discard the others. -/
noncomputable def selOne : (l : List Q.X) → (y : Q.X) → y ∈ l →
    (Fs.of J (FreeMonoid.ofList l) ⟶ Fs.of J (FreeMonoid.of y))
  | [], _, h => absurd h List.not_mem_nil
  | x :: l, y, h =>
    castF J (eCons J x l) ≫
    if hx : x = y then (𝟙 (Fs.of J (FreeMonoid.of x)) ⊗ₛ discW J l) ≫ castF J (eSel₁ J hx)
    else (discF J x ⊗ₛ selOne l y ((List.mem_cons.1 h).resolve_left (Ne.symm hx))) ≫
      castF J (eSel₂ J y)

/-- A morphism `w_X → w_Y` copying and discarding letters (a multiplier by indices). -/
noncomputable def selMany (X : List Q.X) : (Y : List Q.X) → (∀ y ∈ Y, y ∈ X) →
    (Fs.of J (FreeMonoid.ofList X) ⟶ Fs.of J (FreeMonoid.ofList Y))
  | [], _ => discW J X ≫ castF J (eOneNil J)
  | y :: Y, h => copyW J X ≫ (selOne J X y (h y (by simp)) ⊗ₛ selMany X Y fun z hz => h z (by simp [hz])) ≫
      castF J (eConsR J y Y)

variable {J}

@[simp] theorem card_castF (k : Q.P) {a b : J.Fs} (h : a = b) : J.card (.mech k) (castF J h) = 0 := by
  unfold castF; exact card_eqToHom _ h

@[simp] theorem card_dupF (k : Q.P) (x : Q.X) : J.card (.mech k) (dupF J x) = 0 := by
  unfold dupF; rw [card_gen]; simp

@[simp] theorem card_discF (k : Q.P) (x : Q.X) : J.card (.mech k) (discF J x) = 0 := by
  unfold discF; rw [card_gen]; simp

open Classical in
@[simp] theorem card_mechF (k i : Q.P) : J.card (.mech k) (mechF J i) = if i = k then 1 else 0 := by
  unfold mechF; rw [card_gen]; simp

@[simp] theorem card_copyW (k : Q.P) : ∀ l, J.card (.mech k) (copyW J l) = 0
  | [] => by rw [copyW, card_castF]
  | x :: l => by
    rw [copyW]
    simp only [card_comp, card_tensor, card_id, card_braid, card_dupF]
    repeat erw [card_castF]
    rw [card_copyW k l]

@[simp] theorem card_discW (k : Q.P) : ∀ l, J.card (.mech k) (discW J l) = 0
  | [] => by rw [discW, card_castF]
  | x :: l => by
    rw [discW]
    simp only [card_comp, card_tensor, card_discF]
    repeat erw [card_castF]
    rw [card_discW k l]

@[simp] theorem card_selOne (k : Q.P) : ∀ l y h, J.card (.mech k) (selOne J l y h) = 0
  | [], _, h => absurd h List.not_mem_nil
  | x :: l, y, h => by
    unfold selOne
    split_ifs
    · simp only [card_comp, card_tensor, card_id]
      repeat erw [card_castF]
      rw [card_discW]
    · simp only [card_comp, card_tensor, card_discF]
      repeat erw [card_castF]
      rw [card_selOne k l]

@[simp] theorem card_selMany (k : Q.P) (X : List Q.X) :
    ∀ Y h, J.card (.mech k) (selMany J X Y h) = 0
  | [], _ => by rw [selMany, card_comp, card_castF, card_discW]
  | y :: Y, h => by
    rw [selMany]
    simp only [card_comp, card_tensor]
    repeat erw [card_castF]
    rw [card_copyW, card_selOne, card_selMany k X Y]

end Blocks

/-! ### Existence of effect morphisms -/

section Exists

variable {S T : Finset (Fin n)}

/-- If the parents of `v` are in `S`, adding `v` to `S` removes exactly `v` from
`V(G_{S → T}) ∖ S`. -/
theorem R_insert {v : Fin n} (hv : K.pa v ⊆ S) (k : Fin n) :
    K.R (insert v S) T k ↔ K.R S T k ∧ k ≠ v := by
  constructor
  · rintro ⟨hk, t, ht, h⟩
    refine ⟨⟨fun h' => hk (Finset.mem_insert_of_mem h'), t, ht, ?_⟩,
      fun h' => hk (h' ▸ Finset.mem_insert_self _ _)⟩
    exact ReflTransGen.mono (fun a b hab => ⟨hab.1, fun h' => hab.2 (Finset.mem_insert_of_mem h')⟩)
      _ _ h
  · rintro ⟨⟨hkS, t, ht, h⟩, hkv⟩
    refine ⟨fun h' => (Finset.mem_insert.1 h').elim hkv hkS, t, ht, ?_⟩
    clear ht
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ReflTransGen.refl
    | @head a c hac _ ih =>
      have hcv : c ≠ v := fun h' => hkS (hv (h' ▸ hac.1))
      refine ReflTransGen.head ⟨hac.1, fun h' => (Finset.mem_insert.1 h').elim hcv hac.2⟩ ?_
      exact ih hcv hac.2

/-- A vertex of `V(G_{S → T}) ∖ S` that is minimal for the arrows has all its parents in `S`. -/
theorem exists_minimal (h : ∃ k, K.R S T k) : ∃ v, K.R S T v ∧ K.pa v ⊆ S := by
  obtain ⟨v, hv, hmin⟩ := K.wellFounded.has_min {k | K.R S T k} h
  refine ⟨v, hv, fun j hj => ?_⟩
  rcases inD_of_mem_pa hv hj with hS | hR
  · exact hS
  · exact absurd hj (hmin j hR)

variable (J) in
theorem eFin (S : Finset (Fin n)) : Fs.of J (finWord S) = Fs.of J (FreeMonoid.ofList (S.sort (· ≤ ·))) := rfl

variable (J) in
theorem eApp (S S' : Finset (Fin n)) :
    Fs.of J (FreeMonoid.ofList (S.sort (· ≤ ·) ++ S'.sort (· ≤ ·))) =
      Fs.of J (finWord S) * Fs.of J (finWord S') := rfl

variable (J) in
theorem ePa (v : Fin n) : Fs.of J (finWord (K.pa v)) = Fs.of J (K.sig.src v) := rfl

variable (J) in
theorem eOut (v : Fin n) : Fs.of J (FreeMonoid.of (K.sig.out v)) = Fs.of J (FreeMonoid.of v) := rfl

variable (J) in
theorem eSnoc (S : Finset (Fin n)) (v : Fin n) :
    Fs.of J (finWord S) * Fs.of J (FreeMonoid.of v) = Fs.of J (FreeMonoid.ofList (S.sort (· ≤ ·) ++ [v])) :=
  rfl

variable (J) in
/-- There is a morphism of `F_s(K.sig.G)` whose diagrams are effect diagrams for `(S, T)`. -/
theorem exists_effect (S T : Finset (Fin n)) :
    ∃ f : Fs.of J (finWord S) ⟶ Fs.of J (finWord T), IsEffect J f := by
  classical
  suffices H : ∀ m (S : Finset (Fin n)), (Finset.univ.filter fun k => K.R S T k).card = m →
      ∃ f : Fs.of J (finWord S) ⟶ Fs.of J (finWord T), IsEffect J f from H _ S rfl
  intro m
  induction m with
  | zero =>
    intro S hS
    have hR : ∀ k, ¬ K.R S T k := fun k hk => by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hS
      exact hS (Finset.mem_univ k) hk
    have hTS : ∀ y ∈ T.sort (· ≤ ·), y ∈ S.sort (· ≤ ·) := fun y hy => by
      rw [Finset.mem_sort] at hy ⊢
      by_contra h'
      exact hR y ⟨h', y, hy, ReflTransGen.refl⟩
    exact ⟨castF J (eFin J S) ≫ selMany J _ _ hTS ≫ castF J (eFin J T).symm, fun k => by
      simp only [card_comp]; repeat erw [card_castF]
      rw [card_selMany]; simp [hR k]⟩
  | succ m ih =>
    intro S hS
    obtain ⟨v, hvR, hvS⟩ := exists_minimal (S := S) (T := T) (by
      obtain ⟨k, hk⟩ := Finset.card_pos.1 (by omega : 0 < (Finset.univ.filter fun k => K.R S T k).card)
      exact ⟨k, (Finset.mem_filter.1 hk).2⟩)
    have hcard : (Finset.univ.filter fun k => K.R (insert v S) T k).card = m := by
      have : (Finset.univ.filter fun k => K.R (insert v S) T k) =
          (Finset.univ.filter fun k => K.R S T k).erase v := by
        ext k; simp [R_insert hvS k, and_comm]
      rw [this, Finset.card_erase_of_mem (by simpa using hvR), hS]; rfl
    obtain ⟨f', hf'⟩ := ih (insert v S) hcard
    have h₁ : ∀ y ∈ S.sort (· ≤ ·) ++ (K.pa v).sort (· ≤ ·), y ∈ S.sort (· ≤ ·) := fun y hy => by
      rcases List.mem_append.1 hy with hy | hy
      · exact hy
      · rw [Finset.mem_sort] at hy ⊢; exact hvS hy
    have h₂ : ∀ y ∈ (insert v S).sort (· ≤ ·), y ∈ S.sort (· ≤ ·) ++ [v] := fun y hy => by
      rw [Finset.mem_sort, Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · simp
      · exact List.mem_append_left _ ((Finset.mem_sort _).2 hy)
    let step : Fs.of J (finWord S) ⟶ Fs.of J (finWord (insert v S)) :=
      castF J (eFin J S) ≫ selMany J _ _ h₁ ≫ castF J (eApp J S (K.pa v)) ≫
      (𝟙 (Fs.of J (finWord S)) ⊗ₛ (castF J (ePa J v) ≫ mechF J v ≫ castF J (eOut J v))) ≫
      castF J (eSnoc J S v) ≫ selMany J _ _ h₂ ≫ castF J (eFin J (insert v S)).symm
    have hstep : ∀ k, J.card (.mech k) step = if v = k then 1 else 0 := fun k => by
      simp only [step, card_comp, card_tensor, card_id]
      repeat erw [card_castF]
      rw [card_selMany, card_selMany, card_mechF]
      simp
    refine ⟨step ≫ f', fun k => ?_⟩
    rw [card_comp, hstep k, hf' k]
    by_cases hkv : k = v
    · subst hkv
      have : ¬ K.R (insert k S) T k := fun h => (R_insert hvS k).1 h |>.2 rfl
      simp [hvR, this]
    · have e := R_insert (T := T) hvS k
      by_cases hk : K.R S T k
      · simp [Ne.symm hkv, hk, e.2 ⟨hk, hkv⟩]
      · have : ¬ K.R (insert v S) T k := fun h => hk (e.1 h).1
        simp [Ne.symm hkv, hk, this]

end Exists

/-! ### The effect in the free Markov category -/

section Free

variable {S T : Finset (Fin n)}

theorem labelOK_of_isEffect {f : Fs.of J (finWord S) ⟶ Fs.of J (finWord T)} (hf : IsEffect J f) :
    ProdSig.LabelOK J f := by
  classical
  intro k
  rw [hf k]
  refine ⟨by split_ifs <;> simp, fun h => ?_⟩
  split_ifs at h with hk
  · change k ∉ FreeMonoid.toList (finWord S)
    rw [mem_finWord]; exact hk.1
  · exact absurd rfl h

variable (J) in
/-- *Definition 5.4.* The **`(W, K)`-effect** `[w_T ‖ w_S]` in the free Markov category `J.FsM` of
`K`: the morphism represented by an effect diagram. -/
noncomputable def freeEffect (S T : Finset (Fin n)) :
    J.projM.obj (Fs.of J (finWord S)) ⟶ J.projM.obj (Fs.of J (finWord T)) :=
  J.projM.map (Classical.choose (exists_effect J S T))

/-- *Definition 5.4.* "The diagram thus obtained is not unique up to isomorphisms ... But the
morphism that it represents is unique": every effect diagram represents `[w_T ‖ w_S]`. -/
theorem projM_eq_freeEffect {f : Fs.of J (finWord S) ⟶ Fs.of J (finWord T)} (hf : IsEffect J f) :
    J.projM.map f = freeEffect J S T := by
  have hg := Classical.choose_spec (exists_effect J S T)
  exact ProdSig.projM_eq_of_card (finWord_nodup S) (labelOK_of_isEffect hf) (labelOK_of_isEffect hg)
    fun k => (hf k).trans (hg k).symm

theorem isEffect_comp {S' : Finset (Fin n)} {f : Fs.of J (finWord S) ⟶ Fs.of J (finWord S')}
    {g : Fs.of J (finWord S') ⟶ Fs.of J (finWord T)} (hf : IsEffect J f) (hg : IsEffect J g)
    (h : ∀ k, (K.R S T k ↔ K.R S S' k ∨ K.R S' T k)) (h' : ∀ k, ¬ (K.R S S' k ∧ K.R S' T k)) :
    IsEffect J (f ≫ g) := by
  classical
  intro k
  rw [card_comp, hf k, hg k]
  by_cases h₁ : K.R S S' k
  · have h₂ : ¬ K.R S' T k := fun h₂ => h' k ⟨h₁, h₂⟩
    simp [h₁, h₂, (h k).2 (Or.inl h₁)]
  · by_cases h₂ : K.R S' T k
    · simp [h₁, h₂, (h k).2 (Or.inr h₂)]
    · have : ¬ K.R S T k := fun h₃ => ((h k).1 h₃).elim h₁ h₂
      simp [h₁, h₂, this]

/-- **Lemma 5.5** (in the free Markov category of `K`): for `i ∈ V(G_{S → T}) ∖ S`,
`[T ‖ S] = [T ‖ T_i] ∘ [T_i ‖ S]`.  More precisely, an effect diagram for `(S, T_i)` glued to an
effect diagram for `(T_i, T)` is an effect diagram for `(S, T)` (`isEffect_comp`). -/
theorem lemma_5_5_free {i : Fin n} (hi : K.R S T i) :
    freeEffect J S T = freeEffect J S (K.Ti S T i) ≫ freeEffect J (K.Ti S T i) T := by
  obtain ⟨f, hf⟩ := exists_effect J S (K.Ti S T i)
  obtain ⟨g, hg⟩ := exists_effect J (K.Ti S T i) T
  rw [← projM_eq_freeEffect hf, ← projM_eq_freeEffect hg, ← Functor.map_comp]
  exact (projM_eq_freeEffect (isEffect_comp hf hg (R_iff_R_Ti_or hi) (not_R_Ti_and hi))).symm

variable (J) in
theorem eOutSingle (v : Fin n) : Fs.of J (FreeMonoid.of (K.sig.out v)) = Fs.of J (finWord {v}) := by
  change FreeMonoid.of v = FreeMonoid.ofList (({v} : Finset (Fin n)).sort (· ≤ ·))
  rw [Finset.sort_singleton]; rfl

theorem R_pa_iff (v k : Fin n) : K.R (K.pa v) {v} k ↔ k = v := by
  constructor
  · rintro ⟨hk, t, ht, h⟩
    rw [Finset.mem_singleton] at ht
    subst ht
    rcases h.cases_tail with rfl | ⟨c, _, hc⟩
    · rfl
    · exact absurd hc.1 (fun h' => by
        rcases (show ReflTransGen _ k c from by assumption).cases_tail with rfl | ⟨d, _, hd⟩
        · exact hk h'
        · exact hd.2 h')
  · rintro rfl
    exact ⟨K.not_mem_pa k, k, Finset.mem_singleton_self k, ReflTransGen.refl⟩

variable (J) in
/-- The generator `κ_v` as a morphism `w_{S_v} → w_{{v}}`. -/
noncomputable def mechK (v : Fin n) : Fs.of J (finWord (K.pa v)) ⟶ Fs.of J (finWord {v}) :=
  castF J (ePa J v) ≫ mechF J v ≫ castF J (eOutSingle J v)

theorem arrow_mechK (v : Fin n) : Arrow.mk (mechK J v) = Arrow.mk (mechF J v) := by
  simp [mechK, castF]

/-- `[i ‖ S_i] = κ_i`: the one-node diagram of `κ_i` is an effect diagram for `(S_i, {i})` (used for
the identity in Theorem 6.7). -/
theorem freeEffect_parents (v : Fin n) : freeEffect J (K.pa v) {v} = J.projM.map (mechK J v) := by
  classical
  refine (projM_eq_freeEffect (f := mechK J v) fun k => ?_).symm
  simp only [mechK, card_comp]
  repeat erw [card_castF]
  rw [card_mechF]
  by_cases h : k = v
  · subst h; simp [(R_pa_iff k k).2 rfl]
  · have h' : ¬ K.R (K.pa v) {v} k := fun h' => h ((R_pa_iff v k).1 h')
    simp [Ne.symm h, h']

end Free

/-! ### Effect diagrams: skeleton, live nodes, Markov congruence -/

section Diagrams

variable {S T : Finset (Fin n)} {N E N' E' : Type*}

theorem IsEffectDiagram.labelCond {Γ : Diagram K.sig.G.toFreeGraphMonoid N E} [Finite N]
    (h : IsEffectDiagram S T Γ) : ProdSig.LabelCond Γ := by
  classical
  have hc : ∀ k, Nat.card {x // Γ.val.v₁ x = .mech k} ≤ 1 := fun k => by
    have := h.card k; unfold Diagram.card at this; rw [this]; split_ifs <;> simp
  refine ⟨fun p x y hx hy => ?_, fun p x hx => ?_⟩
  · exact congrArg Subtype.val ((Finite.card_le_one_iff_subsingleton.1 (hc p)).elim ⟨x, hx⟩ ⟨y, hy⟩)
  · have h₁ := h.card p
    unfold Diagram.card at h₁
    split_ifs at h₁ with hp
    · rw [h.dom]; change p ∉ FreeMonoid.toList (finWord S); rw [mem_finWord]; exact hp.1
    · exact absurd h₁ (Nat.card_ne_zero.2 ⟨⟨⟨x, hx⟩⟩, inferInstance⟩)

/-- *Definition 5.4.* "Any two such diagrams have the same skeleton." -/
theorem effectDiagram_sameSkeleton {Γ : Diagram K.sig.G.toFreeGraphMonoid N E}
    {Υ : Diagram K.sig.G.toFreeGraphMonoid N' E'} [Finite N] [Finite E] [Finite N'] [Finite E']
    (hΓ : IsEffectDiagram S T Γ) (hΥ : IsEffectDiagram S T Υ) : Γ.SameSkeleton Υ := by
  refine ProdSig.sameSkeleton_of_labels (hΓ.dom.trans hΥ.dom.symm) (by rw [hΓ.dom]; exact finWord_nodup S)
    (hΓ.cod.trans hΥ.cod.symm) hΓ.labelCond hΥ.labelCond fun p => ?_
  have h₁ := hΓ.card p
  have h₂ := hΥ.card p
  unfold Diagram.card at h₁ h₂
  constructor
  · rintro ⟨x, hx⟩
    have : Nat.card {x // Υ.val.v₁ x = .mech p} ≠ 0 := by
      rw [h₂, ← h₁]; exact Nat.card_ne_zero.2 ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
    obtain ⟨⟨y, hy⟩⟩ := (Nat.card_ne_zero.1 this).1
    exact ⟨y, hy⟩
  · rintro ⟨x, hx⟩
    have : Nat.card {x // Γ.val.v₁ x = .mech p} ≠ 0 := by
      rw [h₁, ← h₂]; exact Nat.card_ne_zero.2 ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
    obtain ⟨⟨y, hy⟩⟩ := (Nat.card_ne_zero.1 this).1
    exact ⟨y, hy⟩

/-- *Definition 5.4.* "Each node with the value `κ_i`, `i ∈ V(G_{S → T}) ∖ S`, occurs once and is
live, since a directed path leads from it to the codomain." -/
theorem effectDiagram_live {Γ : Diagram K.sig.G.toFreeGraphMonoid N E} [Finite N] [Finite E]
    (hΓ : IsEffectDiagram S T Γ) {x : N} {k : Fin n} (hx : Γ.val.v₁ x = .mech k) : Γ.Live x := by
  classical
  have hocc : ∀ j, K.R S T j → ProdSig.Occurs Γ j := fun j hj => by
    have h₁ := hΓ.card j
    unfold Diagram.card at h₁
    simp only [hj, ↓reduceIte] at h₁
    obtain ⟨⟨y, hy⟩⟩ := (Nat.card_ne_zero.1 (by rw [h₁]; exact one_ne_zero)).1
    exact ⟨y, hy⟩
  have hkR : K.R S T k := by
    by_contra hk
    have h₁ := hΓ.card k
    unfold Diagram.card at h₁
    simp only [hk, ↓reduceIte] at h₁
    exact (Nat.card_ne_zero.2 ⟨⟨⟨x, hx⟩⟩, inferInstance⟩) h₁
  rw [ProdSig.live_iff_liveLab hΓ.labelCond hx]
  obtain ⟨hkS, t, ht, h⟩ := hkR
  -- follow the path to `T`
  have hT : t ∈ K.sig.letters Γ.codWord := by
    rw [hΓ.cod]; exact mem_finWord.2 ht
  clear hx
  induction h using ReflTransGen.head_induction_on with
  | refl => exact .cod hT
  | @head a c hac hct ih =>
    have hcR : K.R S T c := ⟨hac.2, t, ht, hct⟩
    exact .step (hocc c hcR) (ih hac.2) (mem_finWord.2 hac.1)

/-- *Definition 5.4.* Two Markov minimal effect diagrams for `(S, T)` are Markov congruent
("any two such diagrams have the same skeleton, and hence are Markov congruent by Lemma 4.4"). -/
theorem effectDiagram_congruent {Γ : Diagram K.sig.G.toFreeGraphMonoid N E}
    {Υ : Diagram K.sig.G.toFreeGraphMonoid N' E'} [Finite N] [Finite E] [Finite N'] [Finite E']
    (hΓ : IsEffectDiagram S T Γ) (hΥ : IsEffectDiagram S T Υ) (hmΓ : Γ.MarkovMinimal)
    (hmΥ : Υ.MarkovMinimal) : Diagram.MarkovCongruent Γ Υ :=
  Diagram.lemma_4_4_congruent hmΓ hmΥ (effectDiagram_sameSkeleton hΓ hΥ)

end Diagrams

end EffSig

end FreeMarkov
