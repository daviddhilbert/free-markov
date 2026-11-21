/-
Free Markov categories, Stage 5: Remarks 5.2 and 5.3 (uniqueness of multipliers) and the first
claim of Remark 5.7 (the `m`-fold copy is the image of the unique morphism `a → a^m`).

* `copyFunctor J w`: the strict Markov functor `F : F_s(G_a)/S_M → C` with `F(a) = w`, where `G_a`
  is the free `DD`-graph monoid with one letter `a` and only the duplicate and the discard on `a`
  (Theorem 4.1).
* `remark_5_7_copy`: every morphism `a → a^m` of `F_s(G_a)/S_M` is sent to the `m`-fold copy on `w`
  (in every strict Markov category, straight or not); `remark_5_7_unique`: there is only one such
  morphism.
* `remark_5_2`: in a straight Markov category the `m`-fold copy is the only multiplier on
  `(w, w^m)`.
* `exists_multiplier`: in every strict Markov category, if `v` is a monoidal product of members of `W`
  then there is a multiplier on `(W, v)`.
* `remark_5_3`, `remark_5_3_none`: if the objects form a free monoid, the `w_i` are pairwise
  distinct letters and `v` is a word in them, there is exactly one multiplier on `(W, v)`; if
  another letter occurs in `v`, there is none.

The cited result C1 is used for the free Markov categories `F_s(G_a)/S_M` and
`F_s(G_{a_1 … a_n})/S_M` (through `J : JoyalStreet _`).
-/
module

public import FreeMarkov.Stage5.Free

@[expose] public section

universe v u

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov JoyalStreet

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C]

theorem copyN_congr {w w' : C} (h : w = w') (m : ℕ) :
    Arrow.mk (copyN w m) = Arrow.mk (copyN w' m) := by
  subst h; rfl

theorem IsProdOf.eq_pow {M : Type*} [Monoid M] {a x : M} (h : IsProdOf [a] x) :
    ∃ k, x = a ^ k := by
  obtain ⟨l, hl, rfl⟩ := h
  have : l = List.replicate l.length a :=
    List.eq_replicate_iff.2 ⟨rfl, fun b hb => List.mem_singleton.1 (hl b hb)⟩
  exact ⟨l.length, by rw [this, List.prod_replicate, List.length_replicate]⟩

/-! ### The free Markov category on one letter -/

/-- The letter `a` of `G_a`. -/
abbrev oneLetter : FreeMonoid (ProdSig.free Unit).X := FreeMonoid.of ()

variable (J : JoyalStreet (ProdSig.free Unit).G.toFreeGraphMonoid)

/-- *Remark 5.2.* The strict Markov functor `F : F_s(G_a)/S_M → C` with `F(a) = w`. -/
noncomputable def copyFunctor (w : C) : StrictMarkovFunctor J.FsM C :=
  J.lift ((ProdSig.free Unit).toHom (fun _ => w) fun p => p.elim)
    ((ProdSig.free Unit).toHom_matches _ _)

theorem copyFunctor_obj_pow (w : C) (m : ℕ) :
    (copyFunctor J w).obj (J.wordM (oneLetter ^ m)) = w ^ m := by
  rw [copyFunctor, lift_obj]
  change (FreeMonoid.lift fun _ => w) (FreeMonoid.of () ^ m) = _
  rw [map_pow, FreeMonoid.lift_eval_of]

theorem copyFunctor_obj (w : C) : (copyFunctor J w).obj (J.wordM oneLetter) = w := by
  simpa using copyFunctor_obj_pow J w 1

/-- *Remark 5.2.* There is exactly one morphism `a → a^m` in `F_s(G_a)/S_M`: "a diagram in `G_a`
from `a` to `a^m` has no live nodes, and the origin of every edge in its codomain is the edge in
its domain.  So any two such diagrams have the same skeleton, and hence there is only one morphism
`a → a^m` by Lemma 4.4." -/
theorem remark_5_7_unique (m : ℕ) (h h' : J.wordM oneLetter ⟶ J.wordM (oneLetter ^ m)) :
    h = h' :=
  ProdSig.free_hom_eq J (List.nodup_singleton _) h h'

/-- *Remark 5.7.* "For every object `w` and every `m ≥ 0`, the recursion in Remark 5.2 still defines
a multiplier `w → w^m`, which we call the `m`-fold copy on `w`.  It is the image of the unique
morphism `a → a^m` under the strict Markov functor `F` with `F(a) = w` of that remark, which exists
for every strict `M`." -/
theorem remark_5_7_copy (w : C) (m : ℕ) (h : J.wordM oneLetter ⟶ J.wordM (oneLetter ^ m)) :
    Arrow.mk ((copyFunctor J w).map h) = Arrow.mk (copyN w m) := by
  have hpow : (J.wordM oneLetter) ^ m = J.wordM (oneLetter ^ m) := rfl
  rw [remark_5_7_unique J m h (copyN (J.wordM oneLetter) m ≫ eqToHom hpow), Functor.map_comp,
    eqToHom_map, Arrow.arrow_mk_comp_eqToHom, StrictMarkovFunctor.map_copyN]
  exact copyN_congr (copyFunctor_obj J w) m

/-- *Remark 5.7.* "This holds however the edges in its codomain are ordered": composing the
`m`-fold copy with the image of any endomorphism of `a^m` (for instance a permutation of the
factors) gives the `m`-fold copy again. -/
theorem copyN_comp_map (w : C) (m : ℕ) (σ : J.wordM (oneLetter ^ m) ⟶ J.wordM (oneLetter ^ m)) :
    Arrow.mk (copyN w m ≫ eqToHom (copyFunctor_obj_pow J w m).symm ≫ (copyFunctor J w).map σ) =
      Arrow.mk (copyN w m) := by
  have hpow : (J.wordM oneLetter) ^ m = J.wordM (oneLetter ^ m) := rfl
  have e := remark_5_7_copy J w m (copyN (J.wordM oneLetter) m ≫ eqToHom hpow ≫ σ)
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map] at e
  refine Eq.trans ?_ e
  refine Arrow.mk_comp_congr ?_ ?_
  · rw [StrictMarkovFunctor.map_copyN]
    exact copyN_congr (copyFunctor_obj J w).symm m
  · simp

/-! ### Remark 5.2: straight categories -/

include J in
/-- *Remark 5.2.* "If `n = 1` then there is exactly one multiplier on `(w, w^m)`, which is denoted
by `ι_{w → w^m}`": in a straight Markov category every morphism `w → w^m` generated from the
duplicate, the discard, the symmetry and the identity on `w` is the `m`-fold copy. -/
theorem remark_5_2 (hS : Straight C) (w : C) (m : ℕ) (f : w ⟶ w ^ m)
    (hf : IsMult [w] (Arrow.mk f)) : f = copyN w m := by
  by_cases hw : w = 1
  · -- "This is clear if `w = 1`, since `1` is terminal."
    subst hw
    have h1 : (1 : C) ^ m = 1 := one_pow m
    refine (cancel_mono (eqToHom h1)).1 ?_
    rw [eq_discard (f ≫ eqToHom h1), eq_discard (copyN 1 m ≫ eqToHom h1)]
  · have hinj : ∀ x y, IsProdOf [J.wordM oneLetter] x → IsProdOf [J.wordM oneLetter] y →
        (copyFunctor J w).obj x = (copyFunctor J w).obj y → x = y := by
      intro x y hx hy hxy
      obtain ⟨k, rfl⟩ := hx.eq_pow
      obtain ⟨l, rfl⟩ := hy.eq_pow
      change (copyFunctor J w).obj (J.wordM (oneLetter ^ k)) =
        (copyFunctor J w).obj (J.wordM (oneLetter ^ l)) at hxy
      rw [copyFunctor_obj_pow, copyFunctor_obj_pow] at hxy
      by_contra hkl
      exact (straight_iff.1 hS) w hw k l (fun h => hkl (by rw [h])) hxy
    have hf' : IsMult ([J.wordM oneLetter].map (copyFunctor J w).obj) (Arrow.mk f) := by
      rw [List.map_singleton, copyFunctor_obj]; exact hf
    obtain ⟨g, hg, e⟩ := IsMult.exists_preimage (copyFunctor J w) _ hinj hf'
    obtain ⟨k, hk⟩ := hg.mem_closure.1.eq_pow
    obtain ⟨l, hl⟩ := hg.mem_closure.2.eq_pow
    have hk1 : k = 1 := by
      have h₁ := Arrow.left_eq_of_mk_eq e
      rw [hk] at h₁
      change (copyFunctor J w).obj (J.wordM (oneLetter ^ k)) = w at h₁
      rw [copyFunctor_obj_pow] at h₁
      by_contra hne
      exact (straight_iff.1 hS) w hw k 1 hne (by rw [h₁, pow_one])
    have hlm : l = m := by
      have h₁ := Arrow.right_eq_of_mk_eq e
      rw [hl] at h₁
      change (copyFunctor J w).obj (J.wordM (oneLetter ^ l)) = w ^ m at h₁
      rw [copyFunctor_obj_pow] at h₁
      by_contra hne
      exact (straight_iff.1 hS) w hw l m hne h₁
    subst hk1 hlm
    have hk' : J.wordM oneLetter = g.left := by rw [hk, pow_one]
    have hl' : g.right = J.wordM (oneLetter ^ l) := hl
    have e₃ : Arrow.mk (eqToHom hk' ≫ g.hom ≫ eqToHom hl') = Arrow.mk g.hom := arrow_mk_cast _ _ _
    have e₂ := remark_5_7_copy J w l (eqToHom hk' ≫ g.hom ≫ eqToHom hl')
    rw [(copyFunctor J w).toFunctor.mk_map_congr e₃] at e₂
    exact Arrow.eq_of_mk_eq (e.symm.trans e₂)

/-! ### Existence of multipliers -/

theorem braid_one_right (a : C) : σ_ a (1 : C) = eqToHom (by rw [mul_one, one_mul]) := by
  have h := CategoryTheory.braiding_tensorUnit_right (C := C) a
  simp only [braiding_hom_eq, tensorUnit_eq, leftUnitor_eq, rightUnitor_eq, eqToIso.hom,
    eqToIso.inv, eqToHom_trans] at h
  exact h

theorem braid_one_left (a : C) : σ_ (1 : C) a = eqToHom (by rw [mul_one, one_mul]) := by
  have h := CategoryTheory.braiding_tensorUnit_left (C := C) a
  simp only [braiding_hom_eq, tensorUnit_eq, leftUnitor_eq, rightUnitor_eq, eqToIso.hom,
    eqToIso.inv, eqToHom_trans] at h
  exact h

section Exists

variable {W : List C}

theorem isMult_id_prod : ∀ {l : List C}, (∀ y ∈ l, y ∈ W) → IsMult W (Arrow.mk (𝟙 l.prod))
  | [], _ => .idOne
  | y :: l, hl => by
    rw [List.prod_cons, ← tensorHom_id]
    exact .tensor _ _ (.id (hl y (by simp))) (isMult_id_prod fun z hz => hl z (by simp [hz]))

theorem isMult_braid_mem_prod {x : C} (hx : x ∈ W) : ∀ {l : List C}, (∀ y ∈ l, y ∈ W) →
    IsMult W (Arrow.mk (σ_ x l.prod))
  | [], _ => by
    rw [List.prod_nil, braid_one_right, Arrow.mk_eqToHom, Arrow.mk_id_congr (mul_one x)]
    exact .id hx
  | y :: l, hl => by
    rw [List.prod_cons, hexagon]
    exact IsMult.comp' _ _ _ (.tensor _ _ (.braid hx (hl y (by simp)))
      (isMult_id_prod fun z hz => hl z (by simp [hz])))
      (.tensor _ _ (.id (hl y (by simp))) (isMult_braid_mem_prod hx fun z hz => hl z (by simp [hz])))

theorem isMult_braid_prod {c : C} (hc : IsProdOf W c) : ∀ {l : List C}, (∀ y ∈ l, y ∈ W) →
    IsMult W (Arrow.mk (σ_ l.prod c))
  | [], _ => by
    obtain ⟨l', hl', rfl⟩ := hc
    rw [List.prod_nil, braid_one_left, Arrow.mk_eqToHom, Arrow.mk_id_congr (one_mul _)]
    exact isMult_id_prod hl'
  | y :: l, hl => by
    obtain ⟨l', hl', rfl⟩ := hc
    rw [List.prod_cons, hexagon_reverse]
    exact IsMult.comp' _ _ _ (.tensor _ _ (.id (hl y (by simp)))
      (isMult_braid_prod ⟨l', hl', rfl⟩ fun z hz => hl z (by simp [hz])))
      (.tensor _ _ (isMult_braid_mem_prod (hl y (by simp)) hl')
        (isMult_id_prod fun z hz => hl z (by simp [hz])))

theorem isMult_copy_prod : ∀ {l : List C}, (∀ y ∈ l, y ∈ W) → IsMult W (Arrow.mk (δ_ l.prod))
  | [], _ => by rw [List.prod_nil, copy_one]; exact .idOne
  | y :: l, hl => by
    have hy : y ∈ W := hl y (by simp)
    have hl' : ∀ z ∈ l, z ∈ W := fun z hz => hl z (by simp [hz])
    rw [List.prod_cons, copy_tensor]
    exact IsMult.comp' _ _ _ (.tensor _ _ (.copy hy) (isMult_copy_prod hl'))
      (.tensor _ _ (.tensor _ _ (.id hy) (isMult_braid_mem_prod hy hl')) (isMult_id_prod hl'))

theorem isMult_discard_prod : ∀ {l : List C}, (∀ y ∈ l, y ∈ W) → IsMult W (Arrow.mk (ε_ l.prod))
  | [], _ => by rw [List.prod_nil, discard_one]; exact .idOne
  | y :: l, hl => by
    rw [List.prod_cons, discard_tensor]
    exact .tensor _ _ (.discard (hl y (by simp))) (isMult_discard_prod fun z hz => hl z (by simp [hz]))

open Classical in
/-- Keep one factor `y` of `⊗ l` and discard the others. -/
noncomputable def selectOne : (l : List C) → (y : C) → y ∈ l → (l.prod ⟶ y)
  | [], _, h => absurd h (List.not_mem_nil)
  | w :: l, y, h =>
    if hw : w = y then (𝟙 w ⊗ₛ ε_ l.prod) ≫ eqToHom (by rw [mul_one, hw])
    else (ε_ w ⊗ₛ selectOne l y ((List.mem_cons.1 h).resolve_left (Ne.symm hw))) ≫
      eqToHom (one_mul y)

theorem isMult_selectOne : ∀ (l : List C), (∀ z ∈ l, z ∈ W) → ∀ (y : C) (h : y ∈ l),
    IsMult W (Arrow.mk (selectOne l y h))
  | [], _, _, h => absurd h (List.not_mem_nil)
  | w :: l, hl, y, h => by
    have hw : w ∈ W := hl w (by simp)
    have hl' : ∀ z ∈ l, z ∈ W := fun z hz => hl z (by simp [hz])
    unfold selectOne
    split_ifs with hwy
    · exact IsMult.comp_eqToHom _ _ (.tensor _ _ (.id hw) (isMult_discard_prod hl'))
    · exact IsMult.comp_eqToHom _ _ (.tensor _ _ (.discard hw) (isMult_selectOne l hl' y _))

/-- A morphism `⊗ W → ⊗ ys` that copies and discards the factors of `⊗ W` as `ys` requires. -/
noncomputable def selectMany (W : List C) : (ys : List C) → (∀ y ∈ ys, y ∈ W) → (W.prod ⟶ ys.prod)
  | [], _ => ε_ W.prod ≫ eqToHom List.prod_nil.symm
  | y :: ys, h => δ_ W.prod ≫ (selectOne W y (h y (by simp)) ⊗ₛ
      selectMany W ys fun z hz => h z (by simp [hz])) ≫ eqToHom List.prod_cons.symm

theorem isMult_selectMany (W : List C) : ∀ (ys : List C) (h : ∀ y ∈ ys, y ∈ W),
    IsMult W (Arrow.mk (selectMany W ys h))
  | [], _ => IsMult.comp_eqToHom _ _ (isMult_discard_prod fun _ h => h)
  | y :: ys, h => by
    unfold selectMany
    rw [Arrow.mk_comp_comp_eqToHom]
    exact .comp _ _ (isMult_copy_prod fun _ h => h)
      (.tensor _ _ (isMult_selectOne W (fun _ h => h) y _) (isMult_selectMany W ys _))

end Exists

/-- In every strict Markov category, if `v` is a monoidal product of members of `W` then there is
a multiplier on `(W, v)` (the existence part of Remarks 5.2 and 5.3). -/
theorem exists_multiplier (W : List C) {v : C} (hv : IsProdOf W v) :
    ∃ f : W.prod ⟶ v, IsMultiplier W v f := by
  obtain ⟨ys, hys, rfl⟩ := hv
  exact ⟨selectMany W ys hys, isMult_selectMany W ys hys⟩

/-! ### Remark 5.3: free monoids of objects -/

section Free

variable {X : Type} [Category.{v} (FreeMonoid X)] [StrictMarkov (FreeMonoid X)]

omit [Category.{v} (FreeMonoid X)] [StrictMarkov (FreeMonoid X)] in
theorem FreeMonoid.lift_of_apply' (a : FreeMonoid X) : FreeMonoid.lift FreeMonoid.of a = a := by
  have : FreeMonoid.lift (FreeMonoid.of : X → FreeMonoid X) = MonoidHom.id _ :=
    FreeMonoid.hom_eq fun x => by simp
  rw [this]; rfl

omit [Category.{v} (FreeMonoid X)] [StrictMarkov (FreeMonoid X)] in
theorem FreeMonoid.prod_map_of' : ∀ l : List X, (l.map FreeMonoid.of).prod = FreeMonoid.ofList l
  | [] => rfl
  | x :: l => by rw [List.map_cons, List.prod_cons, FreeMonoid.prod_map_of' l]; rfl

/-- *Remark 5.3.* "Suppose that `(M₀, ⊗, 1)` is indeed a free monoid. Then the underlying graph
monoid of `M` is a free `DD`-graph monoid, with the duplicates and the discards on the letters." -/
def underlyingDD (X : Type) [Category.{v} (FreeMonoid X)] [StrictMarkov (FreeMonoid X)] :
    FreeDDGraphMonoid X where
  A := Arrow (FreeMonoid X)
  s f := f.left
  t f := f.right
  dup x := Arrow.mk (δ_ (FreeMonoid.of x))
  disc x := Arrow.mk (ε_ (FreeMonoid.of x))
  s_dup _ := rfl
  t_dup _ := rfl
  s_disc _ := rfl
  t_disc _ := rfl

variable (JX : JoyalStreet (ProdSig.free X).G.toFreeGraphMonoid)

/-- The strict Markov functor `F : F_s(G_{a_1 … a_n})/S_M → M` with `F(a_i) = w_i`, for the letters
`w_i` themselves (so `F` is the identity on objects). -/
noncomputable def letterFunctor : StrictMarkovFunctor JX.FsM (FreeMonoid X) :=
  JX.lift ((ProdSig.free X).toHom (D := FreeMonoid X) (fun x => FreeMonoid.of x) fun p => p.elim)
    ((ProdSig.free X).toHom_matches _ _)

theorem letterFunctor_obj (a : JX.FsM) : (letterFunctor JX).obj a = JX.unword _ _ a := by
  change (letterFunctor JX).obj (JX.wordM (JX.unword _ _ a)) = _
  rw [letterFunctor, lift_obj]
  exact FreeMonoid.lift_of_apply' _

theorem letterFunctor_map_words : ∀ l : List X,
    (l.map fun x => JX.wordM (FreeMonoid.of x)).map (letterFunctor JX).obj = l.map FreeMonoid.of
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.map_cons, List.map_cons, letterFunctor_map_words l,
      letterFunctor_obj]
    rfl

include JX in
/-- *Remark 5.3.* "If every `w_i` is in the alphabet, `w_i ≠ w_j` for all `i ≠ j`, and `v` is a
word in the letters `w_1, …, w_n` then there is again exactly one multiplier on `(W, v)`." -/
theorem remark_5_3 (W : List X) (hW : W.Nodup) (v : FreeMonoid X)
    (hv : ∀ x ∈ FreeMonoid.toList v, x ∈ W) :
    ∃! f : (W.map FreeMonoid.of).prod ⟶ v, IsMultiplier (W.map FreeMonoid.of) v f := by
  obtain ⟨f, hf⟩ := exists_multiplier (W.map FreeMonoid.of) (v := v)
    ⟨(FreeMonoid.toList v).map FreeMonoid.of,
      fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
        exact List.mem_map_of_mem (hv x hx),
      by
        conv_rhs => rw [← FreeMonoid.ofList_toList v]
        rw [← FreeMonoid.prod_map_of']⟩
  refine ⟨f, hf, fun f' hf' => ?_⟩
  -- both are images of morphisms of the free Markov category on the letters
  let F := letterFunctor JX
  let W' : List JX.FsM := W.map fun x => JX.wordM (FreeMonoid.of x)
  have hFW : W'.map F.obj = W.map FreeMonoid.of := by
    exact letterFunctor_map_words JX W
  have hinj : ∀ x y, IsProdOf W' x → IsProdOf W' y → F.obj x = F.obj y → x = y :=
    fun x y _ _ h => by
      rw [letterFunctor_obj, letterFunctor_obj] at h
      exact h
  obtain ⟨g, hg, e⟩ := IsMult.exists_preimage F W' hinj (by rw [hFW]; exact hf)
  obtain ⟨g', hg', e'⟩ := IsMult.exists_preimage F W' hinj (by rw [hFW]; exact hf')
  have hl : g.left = g'.left := by
    have h₁ := (Arrow.left_eq_of_mk_eq e).trans (Arrow.left_eq_of_mk_eq e').symm
    rwa [letterFunctor_obj, letterFunctor_obj] at h₁
  have hr : g.right = g'.right := by
    have h₁ := (Arrow.right_eq_of_mk_eq e).trans (Arrow.right_eq_of_mk_eq e').symm
    rwa [letterFunctor_obj, letterFunctor_obj] at h₁
  have hnd : (FreeMonoid.toList (JX.unword _ _ g.left)).Nodup := by
    have h₁ := Arrow.left_eq_of_mk_eq e
    rw [letterFunctor_obj] at h₁
    change (FreeMonoid.toList (JX.unword _ _ g.left)).Nodup
    rw [h₁, FreeMonoid.prod_map_of']
    exact hW
  have hgg : g = g' := by
    obtain ⟨a, b, g⟩ := g
    obtain ⟨a', b', g'⟩ := g'
    change a = a' at hl
    change b = b' at hr
    subst hl hr
    congr 1
    exact ProdSig.free_hom_eq JX (a := JX.unword _ _ a) (b := JX.unword _ _ b) hnd g g'
  subst hgg
  exact Arrow.eq_of_mk_eq (e'.symm.trans e)

/-- *Remark 5.3.* "If another letter occurs in `v` then there is no multiplier on `(W, v)` at
all." -/
theorem remark_5_3_none (W : List X) (v : FreeMonoid X) (hv : ∃ x ∈ FreeMonoid.toList v, x ∉ W)
    (f : (W.map FreeMonoid.of).prod ⟶ v) : ¬ IsMultiplier (W.map FreeMonoid.of) v f := by
  intro hf
  obtain ⟨l, hl, hlv⟩ := (IsMult.mem_closure hf).2
  obtain ⟨x, hx, hxW⟩ := hv
  change l.prod = v at hlv
  rw [← hlv] at hx
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ l, x ∈ FreeMonoid.toList y := by
    rw [FreeMonoid.toList_prod, List.mem_flatten] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ht
    exact ⟨y, hy, hxt⟩
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 (hl y hy)
  rw [FreeMonoid.toList_of, List.mem_singleton] at hxy
  subst hxy
  exact hxW hz

end Free

end FreeMarkov
