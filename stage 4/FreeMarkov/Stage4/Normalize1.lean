/-
Free Markov categories, Stage 4: normalising the trees of duplicates of a Markov minimal diagram,
first phase: rotations until the first prong of every duplicate is a consumer (`IsComb`).

"In general, a leaf at a duplicate `d` other than the root may be moved to the duplicate that
precedes `d` by a surgery with (4.1), after surgeries with (4.3) if necessary."

The measure is the sum, over the duplicates, of the number of consumers following their first
prong; a rotation `p(d(H, C), A) ↦ p(H, d(C, A))` lowers it by the number of consumers following
`H`.
-/
module

public import FreeMarkov.Stage4.MoveFacts

@[expose] public section

universe w v u₁ u₂

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

/-- The edge `c` follows `e` through duplicates. -/
abbrev Sub (X : Diagram G.toFreeGraphMonoid N E) (e c : E) : Prop :=
  ReflTransGen (X.DupStep X.val.IsDup) e c

theorem sub_iff (X : Diagram G.toFreeGraphMonoid N E) (e c : E) :
    X.Sub e c ↔ c = e ∨ ∃ x, X.val.IsDup x ∧ X.tgt e = some x ∧ ∃ e' ∈ X.outs x, X.Sub e' c := by
  constructor
  · intro h
    rcases h.cases_head with rfl | ⟨e', ⟨x, hx, h₁, h₂⟩, h'⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨x, hx, h₁, e', (X.mem_outs x e').2 h₂, h'⟩
  · rintro (rfl | ⟨x, hx, h₁, e', he', h'⟩)
    · exact ReflTransGen.refl
    · exact ReflTransGen.head ⟨x, hx, h₁, (X.mem_outs x e').1 he'⟩ h'

theorem sub_of_tgt_some (X : Diagram G.toFreeGraphMonoid N E) {e c : E} {x : N}
    (hte : X.tgt e = some x) :
    X.Sub e c ↔ c = e ∨ (X.val.IsDup x ∧ ∃ e' ∈ X.outs x, X.Sub e' c) := by
  rw [sub_iff, hte]
  constructor
  · rintro (h | ⟨y, hy, hxy, h⟩)
    · exact Or.inl h
    · rw [Option.some.injEq] at hxy
      subst hxy
      exact Or.inr ⟨hy, h⟩
  · rintro (h | ⟨hy, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x, hy, rfl, h⟩

theorem sub_of_tgt_none (X : Diagram G.toFreeGraphMonoid N E) {e c : E} (hte : X.tgt e = none) :
    X.Sub e c ↔ c = e := by
  rw [sub_iff, hte]
  simp

theorem or_shuffle {a b c d e : Prop} : (e ∨ (a ∨ (b ∨ c ∨ d))) ↔ (e ∨ ((b ∨ a ∨ c) ∨ d)) := by
  tauto

/-- The first prongs of all duplicates are consumers: the trees of duplicates are right combs. -/
def IsComb (X : Diagram G.toFreeGraphMonoid N E) : Prop :=
  ∀ x a, X.val.v₁ x = G.dup a → ∀ o₀ o₁, X.outs x = [o₀, o₁] → X.Consumer o₀

/-- In a Markov minimal diagram an output of a duplicate is a consumer or enters a duplicate. -/
theorem out_cases {X : Diagram G.toFreeGraphMonoid N E} (hX : X.MarkovMinimal) {x : N} {a : S}
    (hx : X.val.v₁ x = G.dup a) {o : E} (ho : o ∈ X.outs x) :
    X.Consumer o ∨ ∃ y b, X.tgt o = some y ∧ X.val.v₁ y = G.dup b := by
  have hq : ¬ X.QuasiTerminal x := fun h => X.val.not_isDup_of_isDisc (hX x h) ⟨a, hx⟩
  rw [PGraph.not_quasiTerminal_dup_iff ⟨a, hx⟩] at hq
  rcases (PGraph.reachCod_iff o).1 (hq.2 o ho) with h | ⟨y, hy, e', he', h'⟩
  · exact Or.inl (Or.inl h)
  · by_cases hD : X.val.IsDup y
    · obtain ⟨b, hb⟩ := hD
      exact Or.inr ⟨y, b, hy, hb⟩
    · exact Or.inl (Or.inr ⟨y, hy, hD, e', he', h'⟩)

theorem reachCod_out {X : Diagram G.toFreeGraphMonoid N E} (hX : X.MarkovMinimal) {x : N} {a : S}
    (hx : X.val.v₁ x = G.dup a) {o : E} (ho : o ∈ X.outs x) : X.ReachCod o := by
  have hq : ¬ X.QuasiTerminal x := fun h => X.val.not_isDup_of_isDisc (hX x h) ⟨a, hx⟩
  rw [PGraph.not_quasiTerminal_dup_iff ⟨a, hx⟩] at hq
  exact hq.2 o ho

/-! ### Subtrees under a rotation -/

section Rotation

variable [Finite E] {X : Diagram G.toFreeGraphMonoid N E} {p d : N} (R : RotData X p d)
include R

/-- Outside the moved edge `m`, the edges following an edge through duplicates are the same
before and after a rotation. -/
theorem sub_rotate (e : E) (he : e ≠ R.m) (c : E) : (X.rotate R).Sub e c ↔ X.Sub e c := by
  induction e using (X.rotate R).wellFounded_down.induction with
  | _ e ih =>
    cases hte : X.tgt e with
    | none => rw [sub_of_tgt_none (X.rotate R) hte, sub_of_tgt_none X hte]
    | some x =>
      rw [sub_of_tgt_some (X.rotate R) hte, sub_of_tgt_some X hte]
      change (c = e ∨ (X.val.IsDup x ∧ ∃ e' ∈ X.rotOuts R x, (X.rotate R).Sub e' c)) ↔ _
      by_cases hDx : X.val.IsDup x
      · simp only [hDx, true_and]
        by_cases hxp : x = p
        · subst hxp
          have hstep : ∀ e', e' ∈ X.rotOuts R x → TransGen (X.rotate R).Step e e' := fun e' h' =>
            TransGen.single ⟨x, hte, ((X.rotate R).mem_outs x e').1 h'⟩
          have hH := ih R.H (hstep R.H (by rw [rotOuts_p]; simp)) R.H_ne_m
          have hmC : TransGen (X.rotate R).Step e R.C :=
            (hstep R.m (by rw [rotOuts_p]; simp)).tail ⟨d, R.tgt_m,
              ((X.rotate R).mem_outs d _).1 (by change R.C ∈ X.rotOuts R d; rw [rotOuts_d]; simp)⟩
          have hmA : TransGen (X.rotate R).Step e R.A :=
            (hstep R.m (by rw [rotOuts_p]; simp)).tail ⟨d, R.tgt_m,
              ((X.rotate R).mem_outs d _).1 (by change R.A ∈ X.rotOuts R d; rw [rotOuts_d]; simp)⟩
          have hC := ih R.C hmC R.C_ne_m
          have hA := ih R.A hmA R.m_ne_A.symm
          have hmY : (X.rotate R).Sub R.m c ↔ c = R.m ∨ (X.rotate R).Sub R.C c ∨
              (X.rotate R).Sub R.A c := by
            rw [sub_of_tgt_some (X.rotate R) R.tgt_m]
            change (c = R.m ∨ (X.val.IsDup d ∧ ∃ e' ∈ X.rotOuts R d, (X.rotate R).Sub e' c)) ↔ _
            rw [rotOuts_d]
            have hDd : X.val.IsDup d := ⟨R.a, R.hd⟩
            simp only [hDd, true_and, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
              exists_eq_left]
          have hmX : X.Sub R.m c ↔ c = R.m ∨ X.Sub R.H c ∨ X.Sub R.C c := by
            rw [sub_of_tgt_some X R.tgt_m, R.hod]
            have hDd : X.val.IsDup d := ⟨R.a, R.hd⟩
            simp only [hDd, true_and, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
              exists_eq_left]
          rw [rotOuts_p, R.hop]
          simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
          rw [hmY, hmX, hH, hC, hA]
          exact or_shuffle
        · by_cases hxd : x = d
          · subst hxd
            have : e ∈ X.ins x := (X.mem_ins x e).2 hte
            rw [R.hid, List.mem_singleton] at this
            exact (he this).elim
          · rw [rotOuts_of_ne R hxp hxd]
            refine or_congr Iff.rfl (exists_congr fun e' => and_congr_right fun he' => ?_)
            refine ih e' (TransGen.single ⟨x, hte, ((X.rotate R).mem_outs x e').1
              (by change e' ∈ X.rotOuts R x; rw [rotOuts_of_ne R hxp hxd]; exact he')⟩) ?_
            intro h
            have h1 := (X.mem_outs x e').1 he'
            rw [h, R.src_m, Option.some.injEq] at h1
            exact hxp h1.symm
      · simp [hDx]

end Rotation


/-! ### The measure of the first phase -/

section Measure

variable [Fintype N] [Fintype E]

open scoped Classical in
/-- The number of consumers following the first prong of a duplicate. -/
noncomputable def firstCount (X : Diagram G.toFreeGraphMonoid N E) (x : N) : ℕ :=
  if X.val.IsDup x then
    (match X.outs x with
      | o :: _ => X.toPGraph.consCount X.val.IsDup o
      | [] => 0)
  else 0

/-- The measure of the first phase. -/
noncomputable def mu₁ (X : Diagram G.toFreeGraphMonoid N E) : ℕ := ∑ x, X.firstCount x

omit [Fintype N] in
theorem firstCount_of_outs {X : Diagram G.toFreeGraphMonoid N E} {x : N} (hx : X.val.IsDup x)
    {o₀ o₁ : E} (h : X.outs x = [o₀, o₁]) : X.firstCount x = X.toPGraph.consCount X.val.IsDup o₀ := by
  classical
  simp [firstCount, hx, h]

omit [Fintype N] in
open scoped Classical in
theorem consCount_dup (X : Diagram G.toFreeGraphMonoid N E) {e : E} {x : N} {a : S}
    (hte : X.tgt e = some x) (hx : X.val.v₁ x = G.dup a) {e₁ e₂ : E} (hxo : X.outs x = [e₁, e₂]) :
    X.toPGraph.consCount X.val.IsDup e =
      X.toPGraph.consCount X.val.IsDup e₁ + X.toPGraph.consCount X.val.IsDup e₂ := by
  have hD : X.val.IsDup x := ⟨a, hx⟩
  have hne : e₁ ≠ e₂ := by
    have := X.outs_nodup x
    rw [hxo] at this
    simpa using this
  have hst₁ : X.DupStep X.val.IsDup e e₁ :=
    ⟨x, hD, hte, (X.mem_outs x e₁).1 (by rw [hxo]; simp)⟩
  have hst₂ : X.DupStep X.val.IsDup e e₂ :=
    ⟨x, hD, hte, (X.mem_outs x e₂).1 (by rw [hxo]; simp)⟩
  have hnc : ¬ X.Consumer e := by
    rintro (h | ⟨y, hy, hy'⟩)
    · rw [hte] at h; cases h
    · rw [hte, Option.some.injEq] at hy
      exact hy'.1 (hy ▸ hD)
  unfold PGraph.consCount
  refine PGraph.card_filter_or_of_disjoint _ _ _ (fun c => ?_) (fun c h h' => ?_)
  · rw [show ReflTransGen (X.DupStep X.val.IsDup) e c ↔ X.Sub e c from Iff.rfl,
      sub_of_tgt_some X hte]
    simp only [hD, true_and, hxo, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left]
    constructor
    · rintro ⟨rfl | h | h, hc⟩
      · exact (hnc hc).elim
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr ⟨h, hc⟩
    · rintro (⟨h, hc⟩ | ⟨h, hc⟩)
      · exact ⟨Or.inr (Or.inl h), hc⟩
      · exact ⟨Or.inr (Or.inr h), hc⟩
  · rcases PGraph.reflTransGen_dup_total X.dupCond h.1 h'.1 with h₁ | h₁
    · exact PGraph.not_reflTransGen_sibling X.dupCond hst₁ hst₂ hne h₁
    · exact PGraph.not_reflTransGen_sibling X.dupCond hst₂ hst₁ hne.symm h₁

omit [Fintype N] in
theorem consCount_pos {X : Diagram G.toFreeGraphMonoid N E} {e : E} (h : X.ReachCod e) :
    0 < X.toPGraph.consCount X.val.IsDup e := by
  classical
  obtain ⟨c, hc, hc'⟩ := (PGraph.useful_iff_reachCod (D := X.val.IsDup) e).2 h
  unfold PGraph.consCount
  exact Finset.card_pos.2 ⟨c, by simp [hc, hc']⟩

open scoped Classical in
theorem consCount_rotate {X : Diagram G.toFreeGraphMonoid N E} {p d : N} (R : RotData X p d)
    {e : E} (he : e ≠ R.m) :
    (X.rotate R).toPGraph.consCount (X.rotate R).val.IsDup e = X.toPGraph.consCount X.val.IsDup e := by
  unfold PGraph.consCount
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr (sub_rotate R e he c) ((moveRel_rotate R).consumer_iff c).symm

/-- **A rotation lowers the measure of the first phase.** -/
theorem mu₁_rotate {X : Diagram G.toFreeGraphMonoid N E} (hX : X.MarkovMinimal) {p d : N}
    (R : RotData X p d) : (X.rotate R).mu₁ < X.mu₁ := by
  classical
  have hDp : X.val.IsDup p := ⟨R.a, R.hp⟩
  have hDd : X.val.IsDup d := ⟨R.a, R.hd⟩
  have hpd := R.p_ne_d
  -- the duplicates other than `p`, `d`
  have hrest : ∀ x, x ≠ p → x ≠ d → (X.rotate R).firstCount x = X.firstCount x := by
    intro x hxp hxd
    unfold firstCount
    change (if X.val.IsDup x then (match X.rotOuts R x with
      | o :: _ => (X.rotate R).toPGraph.consCount (X.rotate R).val.IsDup o | [] => 0) else 0) = _
    rw [rotOuts_of_ne R hxp hxd]
    split_ifs with hx
    · rcases hxo : X.outs x with _ | ⟨o, l⟩
      · rfl
      · refine consCount_rotate R fun h => ?_
        have : o ∈ X.outs x := by rw [hxo]; exact List.mem_cons_self
        rw [h, X.mem_outs, R.src_m, Option.some.injEq] at this
        exact hxp this.symm
    · rfl
  have hYp : (X.rotate R).firstCount p = X.toPGraph.consCount X.val.IsDup R.H := by
    rw [firstCount_of_outs (X := X.rotate R) hDp (rotOuts_p R), consCount_rotate R R.H_ne_m]
  have hYd : (X.rotate R).firstCount d = X.toPGraph.consCount X.val.IsDup R.C := by
    rw [firstCount_of_outs (X := X.rotate R) hDd (rotOuts_d R), consCount_rotate R R.C_ne_m]
  have hXp : X.firstCount p = X.toPGraph.consCount X.val.IsDup R.H +
      X.toPGraph.consCount X.val.IsDup R.C := by
    rw [firstCount_of_outs hDp R.hop, consCount_dup X R.tgt_m R.hd R.hod]
  have hXd : X.firstCount d = X.toPGraph.consCount X.val.IsDup R.H := firstCount_of_outs hDd R.hod
  have hH := consCount_pos (X := X) (reachCod_out hX R.hd (by rw [R.hod]; simp : R.H ∈ X.outs d))
  have key : ∀ f : N → ℕ, ∑ x, f x = f p + f d + ∑ x ∈ (Finset.univ.erase p).erase d, f x := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hpd.symm, Finset.mem_univ d⟩), add_assoc]
  have hsum : ∑ x ∈ (Finset.univ.erase p).erase d, (X.rotate R).firstCount x =
      ∑ x ∈ (Finset.univ.erase p).erase d, X.firstCount x :=
    Finset.sum_congr rfl fun x hx => hrest x (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx))
      (Finset.ne_of_mem_erase hx)
  unfold mu₁
  rw [key (X.rotate R).firstCount, key X.firstCount, hsum, hYp, hYd, hXp, hXd]
  omega

end Measure

/-- **The first phase.** Rotations lead from a Markov minimal diagram to a Markov minimal diagram in
which the first prong of every duplicate is a consumer. -/
theorem phase₁ [Fintype N] [Fintype E] (X : Diagram G.toFreeGraphMonoid N E) (hX : X.MarkovMinimal) :
    ∃ Y, ReflTransGen MoveRel X Y ∧ Y.MarkovMinimal ∧ Y.IsComb := by
  induction h : X.mu₁ using Nat.strong_induction_on generalizing X with
  | _ k ih =>
    by_cases hc : X.IsComb
    · exact ⟨X, ReflTransGen.refl, hX, hc⟩
    · unfold IsComb at hc
      push Not at hc
      obtain ⟨x, a, hx, o₀, o₁, hxo, hnc⟩ := hc
      rcases out_cases hX hx (by rw [hxo]; simp : o₀ ∈ X.outs x) with hco | ⟨y, b, hy, hyb⟩
      · exact (hnc hco).elim
      obtain ⟨g, hg, hgb⟩ := X.val.ins_eq_of_dup hyb
      have hgo : g = o₀ := by
        have : o₀ ∈ X.ins y := (X.mem_ins y o₀).2 hy
        rw [hg, List.mem_singleton] at this
        exact this.symm
      subst hgo
      obtain ⟨f₀, f₁, hf, hf₀, -⟩ := X.val.outs_eq_of_t_dup hx
      rw [hxo, List.cons.injEq] at hf
      have hab : b = a := by rw [← hgb, hf.1, hf₀]
      subst hab
      obtain ⟨H, C, hyo, -, -⟩ := X.val.outs_eq_of_t_dup hyb
      let R : RotData X x y := ⟨b, g, o₁, H, C, hx, hyb, hxo, hg, hyo⟩
      have hm := moveRel_rotate R
      obtain ⟨Y, hY, hYm, hYc⟩ := ih _ (h ▸ mu₁_rotate hX R) (X.rotate R) (hm.minimal hX) rfl
      exact ⟨Y, ReflTransGen.head hm hY, hYm, hYc⟩

end Diagram

end FreeMarkov
