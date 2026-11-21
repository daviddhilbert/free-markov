/-
Free Markov categories, Stage 4: normalising the trees of duplicates, second phase: sorting the
leaves of each comb by a fixed rank of the edges.

"... so both trees may be transformed so that a given leaf is at the root, and we conclude by
induction on the number of leaves."  Here: in a comb `d₁(ℓ₁, d₂(ℓ₂, R))` with `ℓ₂` of smaller rank,
a swap at `d₁`, a rotation and a swap at `d₂` exchange `ℓ₁` and `ℓ₂`; in a last duplicate
`d(ℓ, ℓ')` with `ℓ'` of smaller rank, a swap.  The measure: the sum over the consumers `c` of
`rank(c)` times the position of `c` in its comb, which increases at each step and is bounded.
-/
module

public import FreeMarkov.Stage4.Normalize1
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

@[expose] public section

universe w v u₁ u₂

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

/-- `y` is the duplicate whose output is the input of the duplicate `x`. -/
def Parent (X : Diagram G.toFreeGraphMonoid N E) (y x : N) : Prop :=
  X.val.IsDup y ∧ X.val.IsDup x ∧ ∃ f ∈ X.ins x, X.src f = some y

theorem Parent.lt {X : Diagram G.toFreeGraphMonoid N E} {y x : N} (h : X.Parent y x) : X.Lt y x := by
  obtain ⟨-, -, f, hf, hfy⟩ := h
  exact X.lt_of_edge hfy ((X.mem_ins x f).1 hf)

theorem Parent.transGen_lt {X : Diagram G.toFreeGraphMonoid N E} {y x : N}
    (h : TransGen X.Parent y x) : X.Lt y x := by
  induction h with
  | single h => exact h.lt
  | tail _ h ih => exact ih.trans h.lt

/-- The leaves of a comb are sorted by `rk`. -/
def Sorted (rk : E → ℕ) (X : Diagram G.toFreeGraphMonoid N E) : Prop :=
  ∀ d a, X.val.v₁ d = G.dup a → ∀ ℓ o, X.outs d = [ℓ, o] →
    (X.Consumer o → rk ℓ < rk o) ∧
      ∀ d' a' ℓ' o', X.tgt o = some d' → X.val.v₁ d' = G.dup a' → X.outs d' = [ℓ', o'] → rk ℓ < rk ℓ'

section Measure

variable [Fintype N] [Fintype E]

open scoped Classical in
/-- The number of duplicates above a duplicate. -/
noncomputable def depth (X : Diagram G.toFreeGraphMonoid N E) (x : N) : ℕ :=
  (Finset.univ.filter fun y => TransGen X.Parent y x).card

open scoped Classical in
/-- The position of an edge in its comb. -/
noncomputable def pos (X : Diagram G.toFreeGraphMonoid N E) (c : E) : ℕ :=
  match X.src c with
  | some y => if X.val.IsDup y then X.depth y + (X.outs y).idxOf c else 0
  | none => 0

open scoped Classical in
/-- The measure of the second phase. -/
noncomputable def psi (rk : E → ℕ) (X : Diagram G.toFreeGraphMonoid N E) : ℕ :=
  ∑ c ∈ Finset.univ.filter X.Consumer, rk c * X.pos c

omit [Fintype E] in
open scoped Classical in
theorem pos_of_src {X : Diagram G.toFreeGraphMonoid N E} {c : E} {y : N} (hc : X.src c = some y)
    (hy : X.val.IsDup y) : X.pos c = X.depth y + (X.outs y).idxOf c := by
  classical
  simp [pos, hc, hy]

omit [Fintype E] in
theorem depth_le (X : Diagram G.toFreeGraphMonoid N E) (x : N) : X.depth x ≤ Fintype.card N := by
  classical
  exact Finset.card_le_univ _

omit [Fintype E] in
open scoped Classical in
theorem pos_le (X : Diagram G.toFreeGraphMonoid N E) (c : E) : X.pos c ≤ Fintype.card N + 1 := by
  classical
  unfold pos
  rcases hc : X.src c with _ | y
  · simp
  · simp only
    split_ifs with hy
    · obtain ⟨a, ha⟩ := hy
      obtain ⟨e₀, e₁, h, -⟩ := X.val.outs_eq_of_t_dup ha
      have hcm : c ∈ X.outs y := (X.mem_outs y c).2 hc
      rw [h] at hcm ⊢
      have := X.depth_le y
      rcases List.mem_pair.1 hcm with rfl | rfl
      · simp; omega
      · by_cases h' : c = e₀
        · subst h'; simp; omega
        · simp [List.idxOf_cons_ne _ (Ne.symm h')]; omega
    · omega

theorem psi_le (rk : E → ℕ) (X : Diagram G.toFreeGraphMonoid N E) :
    psi rk X ≤ ∑ c, rk c * (Fintype.card N + 1) := by
  classical
  unfold psi
  calc ∑ c ∈ Finset.univ.filter X.Consumer, rk c * X.pos c
      ≤ ∑ c ∈ Finset.univ.filter X.Consumer, rk c * (Fintype.card N + 1) :=
        Finset.sum_le_sum fun c _ => Nat.mul_le_mul_left _ (X.pos_le c)
    _ ≤ ∑ c, rk c * (Fintype.card N + 1) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end Measure


theorem sum_split_two {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) (hab : a ≠ b) : ∑ c ∈ s, f c = f a + f b + ∑ c ∈ (s.erase a).erase b, f c := by
  rw [← Finset.add_sum_erase _ _ ha, ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hab.symm, hb⟩),
    add_assoc]

theorem consumer_of_comb {X : Diagram G.toFreeGraphMonoid N E} (hc : X.IsComb) {x : N} {a : S}
    (hx : X.val.v₁ x = G.dup a) {o₀ o₁ : E} (h : X.outs x = [o₀, o₁]) : X.Consumer o₀ :=
  hc x a hx o₀ o₁ h

theorem not_consumer_of_tgt_dup {X : Diagram G.toFreeGraphMonoid N E} {e : E} {x : N}
    (he : X.tgt e = some x) (hx : X.val.IsDup x) : ¬ X.Consumer e := by
  rintro (h | ⟨y, hy, hy'⟩)
  · rw [he] at h; cases h
  · rw [he, Option.some.injEq] at hy
    exact hy'.1 (hy ▸ hx)

/-! ### The exchange of two leaves -/

/-- Two consecutive duplicates of a comb: `outs d₁ = [ℓ₁, m]`, `ins d₂ = [m]`, `outs d₂ = [ℓ₂, R]`. -/
structure ExchData (X : Diagram G.toFreeGraphMonoid N E) (d₁ d₂ : N) where
  a : S
  ℓ₁ : E
  m : E
  ℓ₂ : E
  R : E
  hd₁ : X.val.v₁ d₁ = G.dup a
  hd₂ : X.val.v₁ d₂ = G.dup a
  ho₁ : X.outs d₁ = [ℓ₁, m]
  hi₂ : X.ins d₂ = [m]
  ho₂ : X.outs d₂ = [ℓ₂, R]

namespace ExchData

variable {X : Diagram G.toFreeGraphMonoid N E} {d₁ d₂ : N} (D : ExchData X d₁ d₂)
include D

theorem src_m : X.src D.m = some d₁ := (X.mem_outs d₁ _).1 (by rw [D.ho₁]; simp)
theorem tgt_m : X.tgt D.m = some d₂ := (X.mem_ins d₂ _).1 (by rw [D.hi₂]; simp)
theorem src_ℓ₁ : X.src D.ℓ₁ = some d₁ := (X.mem_outs d₁ _).1 (by rw [D.ho₁]; simp)
theorem src_ℓ₂ : X.src D.ℓ₂ = some d₂ := (X.mem_outs d₂ _).1 (by rw [D.ho₂]; simp)
theorem src_R : X.src D.R = some d₂ := (X.mem_outs d₂ _).1 (by rw [D.ho₂]; simp)

theorem d₁_ne_d₂ : d₁ ≠ d₂ := by
  intro h
  apply X.acyclic d₂
  exact TransGen.single ⟨D.m, by rw [D.src_m, h], D.tgt_m⟩

theorem ℓ₁_ne_ℓ₂ : D.ℓ₁ ≠ D.ℓ₂ := RotData.ne_of_src D.src_ℓ₁ D.src_ℓ₂ D.d₁_ne_d₂
theorem ℓ₁_ne_R : D.ℓ₁ ≠ D.R := RotData.ne_of_src D.src_ℓ₁ D.src_R D.d₁_ne_d₂
theorem ℓ₂_ne_R : D.ℓ₂ ≠ D.R := by
  have := X.outs_nodup d₂
  rw [D.ho₂] at this
  simpa using this

/-- The swap at `d₁`. -/
def D₁ : SwapData X d₁ := ⟨D.a, D.ℓ₁, D.m, D.hd₁, D.ho₁⟩

/-- The rotation after the swap at `d₁`. -/
def R₁ : RotData (X.swap D.D₁) d₁ d₂ :=
  ⟨D.a, D.m, D.ℓ₁, D.ℓ₂, D.R, D.hd₁, D.hd₂, swap.outs_self D.D₁, D.hi₂,
    (swap.outs_of_ne D.D₁ D.d₁_ne_d₂.symm).trans D.ho₂⟩

/-- The swap at `d₂` after the rotation. -/
def D₂ : SwapData ((X.swap D.D₁).rotate D.R₁) d₂ :=
  ⟨D.a, D.R, D.ℓ₁, D.hd₂, rotOuts_d D.R₁⟩

/-- **The exchange** of the leaves `ℓ₁`, `ℓ₂`. -/
noncomputable def result : Diagram G.toFreeGraphMonoid N E := ((X.swap D.D₁).rotate D.R₁).swap D.D₂

theorem moveRel_chain [Finite N] [Finite E] : ReflTransGen MoveRel X D.result :=
  ((ReflTransGen.single (moveRel_swap D.D₁)).tail (moveRel_rotate D.R₁)).tail (moveRel_swap D.D₂)

theorem result_src_of_ne {e : E} (h₁ : e ≠ D.ℓ₁) (h₂ : e ≠ D.ℓ₂) : D.result.src e = X.src e :=
  rotSrc_of_ne D.R₁ h₂ h₁

theorem result_src_ℓ₁ : D.result.src D.ℓ₁ = some d₂ := rotSrc_A D.R₁

theorem result_src_ℓ₂ : D.result.src D.ℓ₂ = some d₁ := rotSrc_H D.R₁

theorem result_outs_d₁ : D.result.outs d₁ = [D.ℓ₂, D.m] := by
  rw [show D.result.outs d₁ = ((X.swap D.D₁).rotate D.R₁).outs d₁ from
    swap.outs_of_ne D.D₂ D.d₁_ne_d₂]
  exact rotOuts_p D.R₁

theorem result_outs_d₂ : D.result.outs d₂ = [D.ℓ₁, D.R] := swap.outs_self D.D₂

theorem result_outs_of_ne {x : N} (h₁ : x ≠ d₁) (h₂ : x ≠ d₂) : D.result.outs x = X.outs x := by
  rw [show D.result.outs x = ((X.swap D.D₁).rotate D.R₁).outs x from swap.outs_of_ne D.D₂ h₂]
  exact (rotOuts_of_ne D.R₁ h₁ h₂).trans (swap.outs_of_ne D.D₁ h₁)

theorem result_ins : D.result.ins = X.ins := rfl
theorem result_tgt : D.result.tgt = X.tgt := rfl
theorem result_v₁ : D.result.val.v₁ = X.val.v₁ := rfl

end ExchData


theorem MoveRel.chain_consumer {X Y : Diagram G.toFreeGraphMonoid N E} (h : ReflTransGen MoveRel X Y)
    (c : E) : X.Consumer c ↔ Y.Consumer c := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ h ih => exact ih.trans (h.consumer_iff c)

theorem MoveRel.chain_minimal [Finite N] [Finite E] {X Y : Diagram G.toFreeGraphMonoid N E}
    (h : ReflTransGen MoveRel X Y) (hX : X.MarkovMinimal) : Y.MarkovMinimal := by
  induction h with
  | refl => exact hX
  | tail _ h ih => exact h.minimal ih

namespace ExchData

variable {X : Diagram G.toFreeGraphMonoid N E} {d₁ d₂ : N} (D : ExchData X d₁ d₂)
include D

theorem not_consumer_m : ¬ X.Consumer D.m := not_consumer_of_tgt_dup D.tgt_m ⟨D.a, D.hd₂⟩

theorem parent_iff (hc : X.IsComb) (y x : N) : D.result.Parent y x ↔ X.Parent y x := by
  have hℓ₁ : X.Consumer D.ℓ₁ := hc d₁ D.a D.hd₁ _ _ D.ho₁
  have hℓ₂ : X.Consumer D.ℓ₂ := hc d₂ D.a D.hd₂ _ _ D.ho₂
  unfold Parent
  refine and_congr Iff.rfl (and_congr_right fun hx => exists_congr fun f => and_congr_right fun hf => ?_)
  have hfx : X.tgt f = some x := (X.mem_ins x f).1 hf
  have h₁ : f ≠ D.ℓ₁ := by rintro rfl; exact not_consumer_of_tgt_dup hfx hx hℓ₁
  have h₂ : f ≠ D.ℓ₂ := by rintro rfl; exact not_consumer_of_tgt_dup hfx hx hℓ₂
  rw [D.result_src_of_ne h₁ h₂]

section Measure

variable [Fintype N] [Fintype E]

omit [Fintype E] in
theorem depth_result (hc : X.IsComb) : D.result.depth = X.depth := by
  classical
  funext x
  unfold depth
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have : D.result.Parent = X.Parent := funext fun y => funext fun x => propext (D.parent_iff hc y x)
  rw [this]

omit [Fintype E] in
theorem depth_d₂ : X.depth d₂ = X.depth d₁ + 1 := by
  classical
  unfold depth
  have hpar : X.Parent d₁ d₂ := ⟨⟨D.a, D.hd₁⟩, ⟨D.a, D.hd₂⟩, D.m, by rw [D.hi₂]; simp, D.src_m⟩
  rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter fun y => TransGen X.Parent y d₁)
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun h => X.lt_irrefl _ (Parent.transGen_lt h))]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    obtain ⟨z, hyz, hz⟩ := TransGen.tail'_iff.1 h
    obtain ⟨-, -, f, hf, hfz⟩ := hz
    rw [D.hi₂, List.mem_singleton] at hf
    subst hf
    rw [D.src_m, Option.some.injEq] at hfz
    subst hfz
    rcases hyz.cases_tail with rfl | ⟨w, hyw, hw⟩
    · exact Or.inl rfl
    · exact Or.inr (TransGen.tail' hyw hw)
  · rintro (rfl | h)
    · exact TransGen.single hpar
    · exact h.tail hpar

/-- **The exchange raises the measure of the second phase.** -/
theorem psi_result (hc : X.IsComb) (rk : E → ℕ) :
    psi rk D.result + rk D.ℓ₂ = psi rk X + rk D.ℓ₁ := by
  classical
  have hℓ₁ : X.Consumer D.ℓ₁ := hc d₁ D.a D.hd₁ _ _ D.ho₁
  have hℓ₂ : X.Consumer D.ℓ₂ := hc d₂ D.a D.hd₂ _ _ D.ho₂
  have hcons := MoveRel.chain_consumer D.moveRel_chain
  have hfilt : Finset.univ.filter D.result.Consumer = Finset.univ.filter X.Consumer := by
    ext c; simp [hcons c]
  have hdep := D.depth_result hc
  have hD₁ : X.val.IsDup d₁ := ⟨D.a, D.hd₁⟩
  have hD₂ : X.val.IsDup d₂ := ⟨D.a, D.hd₂⟩
  -- positions of the two leaves
  have hp₁ : X.pos D.ℓ₁ = X.depth d₁ := by
    rw [pos_of_src D.src_ℓ₁ hD₁, D.ho₁]; simp
  have hp₂ : X.pos D.ℓ₂ = X.depth d₁ + 1 := by
    rw [pos_of_src D.src_ℓ₂ hD₂, D.ho₂, D.depth_d₂]; simp
  have hq₁ : D.result.pos D.ℓ₁ = X.depth d₁ + 1 := by
    rw [pos_of_src D.result_src_ℓ₁ hD₂, D.result_outs_d₂, hdep, D.depth_d₂]; simp
  have hq₂ : D.result.pos D.ℓ₂ = X.depth d₁ := by
    rw [pos_of_src D.result_src_ℓ₂ hD₁, D.result_outs_d₁, hdep]; simp
  -- the other consumers keep their positions
  have hrest : ∀ c, X.Consumer c → c ≠ D.ℓ₁ → c ≠ D.ℓ₂ → D.result.pos c = X.pos c := by
    intro c hcc h₁ h₂
    unfold pos
    rw [D.result_src_of_ne h₁ h₂]
    rcases hsc : X.src c with _ | y
    · rfl
    · simp only
      rw [show D.result.val.IsDup y ↔ X.val.IsDup y from Iff.rfl, hdep]
      split_ifs with hy
      · congr 1
        by_cases hy₁ : y = d₁
        · subst hy₁
          have : c ∈ X.outs y := (X.mem_outs y c).2 hsc
          rw [D.ho₁] at this
          rcases List.mem_pair.1 this with rfl | rfl
          · exact (h₁ rfl).elim
          · exact (D.not_consumer_m hcc).elim
        · by_cases hy₂ : y = d₂
          · subst hy₂
            have : c ∈ X.outs y := (X.mem_outs y c).2 hsc
            rw [D.ho₂] at this
            rcases List.mem_pair.1 this with rfl | rfl
            · exact (h₂ rfl).elim
            · rw [D.result_outs_d₂, D.ho₂]
              rw [List.idxOf_cons_ne _ D.ℓ₁_ne_R, List.idxOf_cons_ne _ D.ℓ₂_ne_R]
          · rw [D.result_outs_of_ne hy₁ hy₂]
      · rfl
  unfold psi
  rw [hfilt]
  have hm₁ : D.ℓ₁ ∈ Finset.univ.filter X.Consumer := by simp [hℓ₁]
  have hm₂ : D.ℓ₂ ∈ Finset.univ.filter X.Consumer := by simp [hℓ₂]
  rw [sum_split_two _ _ hm₁ hm₂ D.ℓ₁_ne_ℓ₂, sum_split_two _ (fun c => rk c * X.pos c) hm₁ hm₂ D.ℓ₁_ne_ℓ₂,
    Finset.sum_congr rfl fun c hc' => by
      have h₂ := Finset.ne_of_mem_erase hc'
      have h₁ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc')
      have hcc := (Finset.mem_filter.1 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc'))).2
      rw [hrest c hcc h₁ h₂],
    hp₁, hp₂, hq₁, hq₂]
  ring

end Measure

end ExchData

/-! ### The last pair of a comb -/

section LastSwap

variable [Fintype N] [Fintype E] {X : Diagram G.toFreeGraphMonoid N E} {d : N} (D : SwapData X d)

omit [Fintype N] [Fintype E] in
theorem parent_swap (y x : N) : (X.swap D).Parent y x ↔ X.Parent y x := Iff.rfl

omit [Fintype E] in
theorem depth_swap : (X.swap D).depth = X.depth := rfl

/-- **The last swap raises the measure of the second phase.** -/
theorem psi_swap (hc₀ : X.Consumer D.o₀) (hc₁ : X.Consumer D.o₁) (rk : E → ℕ) :
    psi rk (X.swap D) + rk D.o₁ = psi rk X + rk D.o₀ := by
  classical
  have hcons := MoveRel.consumer_iff (moveRel_swap D)
  have hfilt : Finset.univ.filter (X.swap D).Consumer = Finset.univ.filter X.Consumer := by
    ext c; simp [hcons c]
  have hD : X.val.IsDup d := ⟨D.a, D.hd⟩
  have hs₀ : X.src D.o₀ = some d := (X.mem_outs d _).1 (by rw [D.houts]; simp)
  have hs₁ : X.src D.o₁ = some d := (X.mem_outs d _).1 (by rw [D.houts]; simp)
  have hp₀ : X.pos D.o₀ = X.depth d := by rw [pos_of_src hs₀ hD, D.houts]; simp
  have hp₁ : X.pos D.o₁ = X.depth d + 1 := by
    rw [pos_of_src hs₁ hD, D.houts]; simp [List.idxOf_cons_ne _ D.ne]
  have hq₀ : (X.swap D).pos D.o₀ = X.depth d + 1 := by
    rw [pos_of_src (X := X.swap D) hs₀ hD, swap.outs_self, depth_swap]
    simp [List.idxOf_cons_ne _ D.ne.symm]
  have hq₁ : (X.swap D).pos D.o₁ = X.depth d := by
    rw [pos_of_src (X := X.swap D) hs₁ hD, swap.outs_self, depth_swap]; simp
  have hrest : ∀ c, c ≠ D.o₀ → c ≠ D.o₁ → (X.swap D).pos c = X.pos c := by
    intro c h₀ h₁
    unfold pos
    rw [show (X.swap D).src = X.src from rfl, depth_swap]
    rcases hsc : X.src c with _ | y
    · rfl
    · simp only
      rw [show (X.swap D).val.IsDup y ↔ X.val.IsDup y from Iff.rfl]
      split_ifs with hy
      · congr 1
        by_cases hyd : y = d
        · subst hyd
          have : c ∈ X.outs y := (X.mem_outs y c).2 hsc
          rw [D.houts] at this
          rcases List.mem_pair.1 this with rfl | rfl
          · exact (h₀ rfl).elim
          · exact (h₁ rfl).elim
        · rw [swap.outs_of_ne D hyd]
      · rfl
  unfold psi
  rw [hfilt]
  have hm₀ : D.o₀ ∈ Finset.univ.filter X.Consumer := by simp [hc₀]
  have hm₁ : D.o₁ ∈ Finset.univ.filter X.Consumer := by simp [hc₁]
  rw [sum_split_two _ _ hm₀ hm₁ D.ne, sum_split_two _ (fun c => rk c * X.pos c) hm₀ hm₁ D.ne,
    Finset.sum_congr rfl fun c hc' => by
      rw [hrest c (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc')) (Finset.ne_of_mem_erase hc')],
    hp₀, hp₁, hq₀, hq₁]
  ring

end LastSwap

/-! ### The second phase -/

/-- **The second phase.** Exchanges and last swaps lead from a Markov minimal comb to a Markov
minimal comb whose leaves are sorted. -/
theorem phase₂ [Fintype N] [Fintype E] (rk : E → ℕ) (hrk : Function.Injective rk)
    (X : Diagram G.toFreeGraphMonoid N E) (hX : X.MarkovMinimal) (hc : X.IsComb) :
    ∃ Y, ReflTransGen MoveRel X Y ∧ Y.MarkovMinimal ∧ Y.IsComb ∧ Sorted rk Y := by
  classical
  obtain ⟨B, hB⟩ : ∃ B, ∀ Z : Diagram G.toFreeGraphMonoid N E, psi rk Z ≤ B := ⟨_, psi_le rk⟩
  induction h : B - psi rk X using Nat.strong_induction_on generalizing X with
  | _ k ih =>
    by_cases hs : Sorted rk X
    · exact ⟨X, ReflTransGen.refl, hX, hc, hs⟩
    obtain ⟨d, a, hd, ℓ, o, ho, hbad⟩ : ∃ d a, X.val.v₁ d = G.dup a ∧ ∃ ℓ o, X.outs d = [ℓ, o] ∧
        ((X.Consumer o ∧ ¬ rk ℓ < rk o) ∨ ∃ d' a' ℓ' o', X.tgt o = some d' ∧
          X.val.v₁ d' = G.dup a' ∧ X.outs d' = [ℓ', o'] ∧ ¬ rk ℓ < rk ℓ') := by
      by_contra hne
      refine hs fun d a hd ℓ o ho => ⟨fun hco => ?_, fun d' a' ℓ' o' h₁ h₂ h₃ => ?_⟩
      · by_contra hlt
        exact hne ⟨d, a, hd, ℓ, o, ho, Or.inl ⟨hco, hlt⟩⟩
      · by_contra hlt
        exact hne ⟨d, a, hd, ℓ, o, ho, Or.inr ⟨d', a', ℓ', o', h₁, h₂, h₃, hlt⟩⟩
    have hℓ : X.Consumer ℓ := hc d a hd ℓ o ho
    have hne : ℓ ≠ o := by
      have := X.outs_nodup d
      rw [ho] at this
      simpa using this
    rcases hbad with ⟨hco, hlt⟩ | ⟨d', a', ℓ', o', hto, hd', ho', hlt⟩
    · -- the last pair: a swap
      have hlt' : rk o < rk ℓ := lt_of_le_of_ne (not_lt.1 hlt) fun h => hne (hrk h).symm
      let D : SwapData X d := ⟨a, ℓ, o, hd, ho⟩
      have hm := moveRel_swap D
      have hps : psi rk (X.swap D) + rk o = psi rk X + rk ℓ := psi_swap D hℓ hco rk
      have hle := hB (X.swap D)
      have hc' : (X.swap D).IsComb := by
        intro x b hx o₀ o₁ hxo
        by_cases hxd : x = d
        · subst hxd
          rw [swap.outs_self, List.cons.injEq] at hxo
          rw [← hxo.1]
          exact (hm.consumer_iff o).1 hco
        · rw [swap.outs_of_ne D hxd] at hxo
          exact (hm.consumer_iff o₀).1 (hc x b hx o₀ o₁ hxo)
      obtain ⟨Y, hY, hYm, hYc, hYs⟩ := ih (B - psi rk (X.swap D)) (by
        have := hB X
        omega) (X.swap D) (hm.minimal hX) hc' rfl
      exact ⟨Y, ReflTransGen.head hm hY, hYm, hYc, hYs⟩
    · -- an exchange
      obtain ⟨g, hg, hga⟩ := X.val.ins_eq_of_dup hd'
      have hgo : g = o := by
        have : o ∈ X.ins d' := (X.mem_ins d' o).2 hto
        rw [hg, List.mem_singleton] at this
        exact this.symm
      subst hgo
      obtain ⟨f₀, f₁, hf, -, hf₁⟩ := X.val.outs_eq_of_t_dup hd
      rw [ho, List.cons.injEq, List.cons.injEq] at hf
      have haa : a' = a := by rw [← hga, hf.2.1, hf₁]
      subst haa
      let D : ExchData X d d' := ⟨a', ℓ, g, ℓ', o', hd, hd', ho, hg, ho'⟩
      have hℓ' : X.Consumer ℓ' := hc d' a' hd' ℓ' o' ho'
      have hlt' : rk ℓ' < rk ℓ := lt_of_le_of_ne (not_lt.1 hlt) fun h => D.ℓ₁_ne_ℓ₂ (hrk h).symm
      have hps : psi rk D.result + rk ℓ' = psi rk X + rk ℓ := D.psi_result hc rk
      have hcons := MoveRel.chain_consumer D.moveRel_chain
      have hc' : D.result.IsComb := by
        intro x b hx o₀ o₁ hxo
        by_cases hx₁ : x = d
        · subst hx₁
          rw [D.result_outs_d₁, List.cons.injEq] at hxo
          rw [← hxo.1]
          exact (hcons ℓ').1 hℓ'
        · by_cases hx₂ : x = d'
          · subst hx₂
            rw [D.result_outs_d₂, List.cons.injEq] at hxo
            rw [← hxo.1]
            exact (hcons ℓ).1 hℓ
          · rw [D.result_outs_of_ne hx₁ hx₂] at hxo
            exact (hcons o₀).1 (hc x b hx o₀ o₁ hxo)
      have hle := hB D.result
      obtain ⟨Y, hY, hYm, hYc, hYs⟩ := ih (B - psi rk D.result) (by
        have := hB X
        omega) D.result (MoveRel.chain_minimal D.moveRel_chain hX) hc' rfl
      exact ⟨Y, D.moveRel_chain.trans hY, hYm, hYc, hYs⟩

/-- **Normal form of the trees of duplicates.** Every Markov minimal diagram is connected by
surgeries with (4.1), (4.3) (on the same nodes and edges) to a Markov minimal diagram whose trees of
duplicates are right combs with the leaves sorted by `rk`. -/
theorem normalize [Fintype N] [Fintype E] (rk : E → ℕ) (hrk : Function.Injective rk)
    (X : Diagram G.toFreeGraphMonoid N E) (hX : X.MarkovMinimal) :
    ∃ Y, ReflTransGen MoveRel X Y ∧ Y.MarkovMinimal ∧ Y.IsComb ∧ Sorted rk Y := by
  obtain ⟨Y₁, h₁, hm₁, hc₁⟩ := phase₁ X hX
  obtain ⟨Y, h, hm, hc, hs⟩ := phase₂ rk hrk Y₁ hm₁ hc₁
  exact ⟨Y, h₁.trans h, hm, hc, hs⟩

end Diagram

end FreeMarkov
