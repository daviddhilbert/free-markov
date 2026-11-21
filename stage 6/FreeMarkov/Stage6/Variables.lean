/-
Free Markov categories, Stage 6: variables (Terminology 6.1) and the variables `φ⁻¹(v)`.

* `Singular v`: no atomic variable occurs more than once in `v`; `finWord S` (`v_S`) is singular.
* `subVar`: `v_{S'}` is a sub-variable of `v_S` iff `S' ⊆ S`; `v_S ∩ v_{S'} = v_{S ∩ S'}`, …
  are `finWord` of the corresponding set operations (no separate declaration is needed).
* `preimW φ v` (`φ⁻¹(v)`): for `φ : H → G` in `FinODAG` and a variable `v` of `G`, the word
  `⊗_{w ∈ v} ⊗_{u ∈ φ⁻¹(w)} u`, the occurrences of `v` in their order and each fiber in the order of
  `V_H`; it is a monoid homomorphism (`φ⁻¹(v w) = φ⁻¹(v) φ⁻¹(w)`).
* `singular_preimW`: if `v` is singular then so is `φ⁻¹(v)`; `not_singular_of_preimW`: the converse
  fails (`φ⁻¹(y y) = ∅` for a vertex with empty fiber).
* `preimW_finWord`: `φ⁻¹(v_S) = u_{φ⁻¹(S)}`, "because the fibers are ordered as their images".
* `preimW_id`, `preimW_comp`: `1⁻¹(v) = v` and `ψ⁻¹(φ⁻¹(v)) = (φ ∘ ψ)⁻¹(v)` (Theorem 6.7, proof).

No cited result is used in this file.
-/
module

public import FreeMarkov.Stage6.ODAG

@[expose] public section

namespace FreeMarkov

open CategoryTheory

/-- *Terminology 6.1.* A variable is **singular** if no atomic variable occurs more than once in it;
in particular `∅` is singular. -/
def Singular {n : ℕ} (v : FreeMonoid (Fin n)) : Prop := (FreeMonoid.toList v).Nodup

theorem singular_one {n : ℕ} : Singular (1 : FreeMonoid (Fin n)) := List.nodup_nil

theorem singular_finWord {n : ℕ} (S : Finset (Fin n)) : Singular (finWord S) := finWord_nodup S

/-- *Terminology 6.1.* `v_{S'}` is a **sub-variable** of `v_S` (written `v_{S'} ⊆ v_S`) if `S' ⊆ S`. -/
def SubVar {n : ℕ} (S' S : Finset (Fin n)) : Prop := S' ⊆ S

theorem finWord_injective {n : ℕ} : Function.Injective (finWord (n := n)) := by
  intro S S' h
  ext i
  rw [← mem_finWord, ← mem_finWord, h]

/-- `finWord S` is the only strictly increasing word with the letters of `S`. -/
theorem finWord_eq_of_sorted {n : ℕ} {S : Finset (Fin n)} {l : List (Fin n)}
    (hl : l.Pairwise (· < ·)) (hm : ∀ x, x ∈ l ↔ x ∈ S) : finWord S = FreeMonoid.ofList l := by
  unfold finWord
  congr 1
  refine List.SortedLT.eq_of_mem_iff (Finset.sortedLT_sort S) hl.sortedLT fun x => ?_
  rw [Finset.mem_sort, hm]

theorem finWord_pairwise {n : ℕ} (S : Finset (Fin n)) :
    (FreeMonoid.toList (finWord S)).Pairwise (· < ·) :=
  (Finset.sortedLT_sort S).pairwise

theorem finWord_empty {n : ℕ} : finWord (∅ : Finset (Fin n)) = 1 := by
  unfold finWord; rw [Finset.sort_empty]; rfl

namespace FinODAG

variable {L H G : FinODAG}

/-- *Section 6.* `φ⁻¹(v) = ⊗_{w ∈ v} ⊗_{u ∈ φ⁻¹(w)} u`, where `w ∈ v` enumerates the occurrences of
atomic variables in `v` in their order and `u ∈ φ⁻¹(w)` the elements of the fiber in the order of
`V_H`. -/
noncomputable def preimW (φ : H ⟶ G) : FreeMonoid (Fin G.n) →* FreeMonoid (Fin H.n) :=
  FreeMonoid.lift fun y => finWord (fiber φ y)

variable (φ : H ⟶ G)

@[simp] theorem preimW_of (y : Fin G.n) : preimW φ (FreeMonoid.of y) = finWord (fiber φ y) :=
  FreeMonoid.lift_eval_of _ _

/-- "So `φ⁻¹(v w) = φ⁻¹(v) φ⁻¹(w)` for all variables `v`, `w`." -/
theorem preimW_mul (v w : FreeMonoid (Fin G.n)) : preimW φ (v * w) = preimW φ v * preimW φ w :=
  map_mul _ v w

theorem toList_preimW (v : FreeMonoid (Fin G.n)) :
    FreeMonoid.toList (preimW φ v) =
      (FreeMonoid.toList v).flatMap fun y => FreeMonoid.toList (finWord (fiber φ y)) := by
  induction v using FreeMonoid.inductionOn' with
  | one => rfl
  | of_mul y v ih =>
    rw [preimW_mul, FreeMonoid.toList_mul, ih, preimW_of, FreeMonoid.toList_mul,
      FreeMonoid.toList_of]
    rfl

theorem mem_preimW {v : FreeMonoid (Fin G.n)} {x : Fin H.n} :
    x ∈ FreeMonoid.toList (preimW φ v) ↔ φ.onV x ∈ FreeMonoid.toList v := by
  rw [toList_preimW, List.mem_flatMap]
  constructor
  · rintro ⟨y, hy, hx⟩
    rw [mem_finWord, mem_fiber] at hx
    rwa [hx]
  · intro h
    exact ⟨_, h, by rw [mem_finWord, mem_fiber]⟩

/-- *Section 6.* "If `v` is singular then so is `φ⁻¹(v)`, since distinct vertices have disjoint
fibers." -/
theorem singular_preimW {v : FreeMonoid (Fin G.n)} (hv : Singular v) : Singular (preimW φ v) := by
  unfold Singular at *
  rw [toList_preimW, List.nodup_flatMap]
  refine ⟨fun y _ => finWord_nodup _, ?_⟩
  refine hv.pairwise_of_forall_ne fun y _ y' _ hne => ?_
  rw [Function.onFun, List.disjoint_iff_ne]
  intro x hx x' hx' hxx
  rw [mem_finWord, mem_fiber] at hx hx'
  exact hne (hx.symm.trans (hxx ▸ hx'))

/-- *Section 6.* "The converse may fail, since a vertex `y` with an empty fiber may occur twice in
`v`, for instance `φ⁻¹(yy) = ∅`." -/
theorem preimW_of_of_empty {y : Fin G.n} (hy : fiber φ y = ∅) :
    preimW φ (FreeMonoid.of y * FreeMonoid.of y) = 1 := by
  rw [preimW_mul, preimW_of, hy, finWord_empty, mul_one]

theorem not_singular_of_of {n : ℕ} (y : Fin n) : ¬ Singular (FreeMonoid.of y * FreeMonoid.of y) := by
  unfold Singular
  simp

/-- *Section 6.* "If `v = v_S` for some `S` then the atomic variables in `φ⁻¹(v)` are in the order
of `V_H`, that is, `φ⁻¹(v)` is of the form `u_{S'}` ... because the fibers are ordered as their
images": `φ⁻¹(v_S) = u_{φ⁻¹(S)}`. -/
theorem preimW_finWord (S : Finset (Fin G.n)) : preimW φ (finWord S) = finWord (preimS φ S) := by
  have h₁ : (FreeMonoid.toList (preimW φ (finWord S))).Pairwise (· < ·) := by
    rw [toList_preimW, List.pairwise_flatMap]
    refine ⟨fun y _ => finWord_pairwise _, ?_⟩
    refine (finWord_pairwise S).imp fun {y y'} hyy x hx x' hx' => ?_
    rw [mem_finWord, mem_fiber] at hx hx'
    exact lt_of_fiber_lt φ (by rw [hx, hx']; exact hyy)
  rw [finWord_eq_of_sorted h₁ fun x => ?_, FreeMonoid.ofList_toList]
  rw [mem_preimW, mem_finWord, mem_preimS]

theorem fiber_id (y : Fin G.n) : fiber (𝟙 G) y = {y} := by
  ext x; simp

theorem finWord_singleton {n : ℕ} (y : Fin n) : finWord {y} = FreeMonoid.of y := by
  unfold finWord; rw [Finset.sort_singleton]; rfl

/-- *Theorem 6.7, proof.* "Let `φ` be the identity on `G`. Then `φ⁻¹(v) = v` for every variable
`v`." -/
theorem preimW_id (v : FreeMonoid (Fin G.n)) : preimW (𝟙 G) v = v := by
  have : preimW (𝟙 G) = MonoidHom.id _ := by
    refine FreeMonoid.hom_eq fun y => ?_
    rw [preimW_of, fiber_id, finWord_singleton]; rfl
  rw [this]; rfl

theorem preimS_fiber (ψ : L ⟶ H) (y : Fin G.n) : preimS ψ (fiber φ y) = fiber (ψ ≫ φ) y := by
  ext x; simp

theorem preimS_comp (ψ : L ⟶ H) (S : Finset (Fin G.n)) :
    preimS ψ (preimS φ S) = preimS (ψ ≫ φ) S := by
  ext x; simp

/-- *Theorem 6.7, proof.* "Hence `ψ⁻¹(φ⁻¹(v)) = (φ ∘ ψ)⁻¹(v)` for all variables `v`": the first
word lists the atomic variables block by block, a block being a fiber of `ψ` over a vertex in
`φ⁻¹(v)`, and since the fibers of `ψ` are ordered as their images this is the order of `V_{G''}`. -/
theorem preimW_comp (ψ : L ⟶ H) (v : FreeMonoid (Fin G.n)) :
    preimW ψ (preimW φ v) = preimW (ψ ≫ φ) v := by
  have : (preimW ψ).comp (preimW φ) = preimW (ψ ≫ φ) := by
    refine FreeMonoid.hom_eq fun y => ?_
    rw [MonoidHom.comp_apply, preimW_of, preimW_finWord, preimW_of, preimS_fiber]
  rw [← this]; rfl

end FinODAG

end FreeMarkov
