/-
Free Markov categories, Stage 4: the two moves on binary trees of duplicates used in the proof of
the second claim of Lemma 4.4, as diagrams on the same nodes and edges.

* `swap X D`: the prongs of a duplicate `d` exchanged (the result of a surgery with (4.3)).
* `rotate X R`: for a duplicate `p` whose first prong `m` enters a duplicate `d`,
  `p(d(H, C), A) ↦ p(H, d(C, A))` (the result of a surgery with (4.1)): `H` becomes the first
  output of `p`, `A` the second output of `d`.

That these are the results of the surgeries is shown in `RewireStep.lean`.
-/
module

public import FreeMarkov.Stage4.ExistsMinimal

@[expose] public section

universe w v u₁ u₂

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

/-! ### Exchanging the prongs of a duplicate -/

/-- A duplicate `d` with outputs `o₀, o₁`. -/
structure SwapData (X : Diagram G.toFreeGraphMonoid N E) (d : N) where
  a : S
  o₀ : E
  o₁ : E
  hd : X.val.v₁ d = G.dup a
  houts : X.outs d = [o₀, o₁]

namespace SwapData

variable {X : Diagram G.toFreeGraphMonoid N E} {d : N} (D : SwapData X d)

theorem v₀_o₀ : X.val.v₀ D.o₀ = D.a := by
  obtain ⟨e₀, e₁, h, h₀, -⟩ := X.val.outs_eq_of_t_dup D.hd
  rw [D.houts, List.cons.injEq] at h
  rw [h.1, h₀]

theorem v₀_o₁ : X.val.v₀ D.o₁ = D.a := by
  obtain ⟨e₀, e₁, h, -, h₁⟩ := X.val.outs_eq_of_t_dup D.hd
  rw [D.houts, List.cons.injEq, List.cons.injEq] at h
  rw [h.2.1, h₁]

theorem ne : D.o₀ ≠ D.o₁ := by
  have := X.outs_nodup d
  rw [D.houts] at this
  simpa using this

end SwapData

open scoped Classical in
/-- **The swap.** The duplicate `d` with its outputs in the other order. -/
noncomputable def swap (X : Diagram G.toFreeGraphMonoid N E) {d : N} (D : SwapData X d) :
    Diagram G.toFreeGraphMonoid N E where
  src := X.src
  tgt := X.tgt
  ins := X.ins
  outs x := if x = d then [D.o₁, D.o₀] else X.outs x
  ins_nodup := X.ins_nodup
  outs_nodup x := by
    by_cases hx : x = d
    · rw [ite_eq_left hx]
      simpa using D.ne.symm
    · rw [ite_eq_right hx]; exact X.outs_nodup x
  mem_ins := X.mem_ins
  mem_outs x e := by
    by_cases hx : x = d
    · subst hx
      rw [ite_eq_left rfl, ← X.mem_outs, D.houts]
      simp [or_comm]
    · rw [ite_eq_right hx]; exact X.mem_outs x e
  acyclic := X.acyclic
  dom := X.dom
  cod := X.cod
  dom_nodup := X.dom_nodup
  cod_nodup := X.cod_nodup
  mem_dom := X.mem_dom
  mem_cod := X.mem_cod
  val :=
    { v₀ := X.val.v₀
      v₁ := X.val.v₁
      s_v₁ := X.val.s_v₁
      t_v₁ := fun x => by
        by_cases hx : x = d
        · subst hx
          rw [ite_eq_left rfl, D.hd, G.t_dup]
          simp [D.v₀_o₀, D.v₀_o₁]
        · rw [ite_eq_right hx]; exact X.val.t_v₁ x }

namespace swap

variable {X : Diagram G.toFreeGraphMonoid N E} {d : N} (D : SwapData X d)

@[simp] theorem src_eq : (X.swap D).src = X.src := rfl
@[simp] theorem tgt_eq : (X.swap D).tgt = X.tgt := rfl
@[simp] theorem ins_eq : (X.swap D).ins = X.ins := rfl
@[simp] theorem dom_eq : (X.swap D).dom = X.dom := rfl
@[simp] theorem cod_eq : (X.swap D).cod = X.cod := rfl
@[simp] theorem v₀_eq : (X.swap D).val.v₀ = X.val.v₀ := rfl
@[simp] theorem v₁_eq : (X.swap D).val.v₁ = X.val.v₁ := rfl

theorem outs_self : (X.swap D).outs d = [D.o₁, D.o₀] := by
  classical
  show (if d = d then _ else _) = _
  rw [ite_eq_left rfl]

theorem outs_of_ne {x : N} (hx : x ≠ d) : (X.swap D).outs x = X.outs x := by
  classical
  show (if x = d then _ else _) = _
  rw [ite_eq_right hx]

end swap

/-! ### Rotating two duplicates -/

/-- A duplicate `p` whose first output `m` enters a duplicate `d`: `outs p = [m, A]`,
`ins d = [m]`, `outs d = [H, C]`, all on the letter `a`. -/
structure RotData (X : Diagram G.toFreeGraphMonoid N E) (p d : N) where
  a : S
  m : E
  A : E
  H : E
  C : E
  hp : X.val.v₁ p = G.dup a
  hd : X.val.v₁ d = G.dup a
  hop : X.outs p = [m, A]
  hid : X.ins d = [m]
  hod : X.outs d = [H, C]

namespace RotData

variable {X : Diagram G.toFreeGraphMonoid N E} {p d : N} (R : RotData X p d)
include R

theorem src_m : X.src R.m = some p := (X.mem_outs p _).1 (by rw [R.hop]; simp)
theorem src_A : X.src R.A = some p := (X.mem_outs p _).1 (by rw [R.hop]; simp)
theorem src_H : X.src R.H = some d := (X.mem_outs d _).1 (by rw [R.hod]; simp)
theorem src_C : X.src R.C = some d := (X.mem_outs d _).1 (by rw [R.hod]; simp)
theorem tgt_m : X.tgt R.m = some d := (X.mem_ins d _).1 (by rw [R.hid]; simp)

theorem p_ne_d : p ≠ d := by
  intro h
  apply X.acyclic d
  exact TransGen.single ⟨R.m, by rw [R.src_m, h], R.tgt_m⟩

theorem m_ne_A : R.m ≠ R.A := by
  have := X.outs_nodup p
  rw [R.hop] at this
  simpa using this

theorem H_ne_C : R.H ≠ R.C := by
  have := X.outs_nodup d
  rw [R.hod] at this
  simpa using this

omit R in
theorem ne_of_src {e e' : E} {x y : N} (he : X.src e = some x) (he' : X.src e' = some y) (h : x ≠ y) :
    e ≠ e' := by
  rintro rfl
  rw [he, Option.some.injEq] at he'
  exact h he'

theorem H_ne_m : R.H ≠ R.m := ne_of_src R.src_H R.src_m R.p_ne_d.symm
theorem H_ne_A : R.H ≠ R.A := ne_of_src R.src_H R.src_A R.p_ne_d.symm
theorem C_ne_m : R.C ≠ R.m := ne_of_src R.src_C R.src_m R.p_ne_d.symm
theorem C_ne_A : R.C ≠ R.A := ne_of_src R.src_C R.src_A R.p_ne_d.symm

theorem v₀_m : X.val.v₀ R.m = R.a := by
  obtain ⟨e₀, e₁, h, h₀, -⟩ := X.val.outs_eq_of_t_dup R.hp
  rw [R.hop, List.cons.injEq] at h
  rw [h.1, h₀]

theorem v₀_A : X.val.v₀ R.A = R.a := by
  obtain ⟨e₀, e₁, h, -, h₁⟩ := X.val.outs_eq_of_t_dup R.hp
  rw [R.hop, List.cons.injEq, List.cons.injEq] at h
  rw [h.2.1, h₁]

theorem v₀_H : X.val.v₀ R.H = R.a := by
  obtain ⟨e₀, e₁, h, h₀, -⟩ := X.val.outs_eq_of_t_dup R.hd
  rw [R.hod, List.cons.injEq] at h
  rw [h.1, h₀]

theorem v₀_C : X.val.v₀ R.C = R.a := by
  obtain ⟨e₀, e₁, h, -, h₁⟩ := X.val.outs_eq_of_t_dup R.hd
  rw [R.hod, List.cons.injEq, List.cons.injEq] at h
  rw [h.2.1, h₁]

/-- The target of `A` is not below `d` (else there would be a circuit through `p`). -/
theorem not_le_tgt_A {w : N} (hw : X.tgt R.A = some w) : ¬ X.Le w d := by
  rintro (h | rfl)
  · obtain ⟨z, hwz, hzd⟩ := TransGen.tail'_iff.1 h
    obtain ⟨e, he₁, he₂⟩ := hzd
    have : e ∈ X.ins d := (X.mem_ins d e).2 he₂
    rw [R.hid, List.mem_singleton] at this
    subst this
    rw [R.src_m, Option.some.injEq] at he₁
    subst he₁
    exact X.acyclic _ (TransGen.tail' hwz ⟨R.A, R.src_A, hw⟩)
  · have : R.A ∈ X.ins w := (X.mem_ins w _).2 hw
    rw [R.hid, List.mem_singleton] at this
    exact R.m_ne_A this.symm

end RotData

open scoped Classical in
/-- The sources after the rotation. -/
noncomputable def rotSrc (X : Diagram G.toFreeGraphMonoid N E) {p d : N} (R : RotData X p d) (e : E) :
    Option N :=
  if e = R.H then some p else if e = R.A then some d else X.src e

open scoped Classical in
/-- The outputs after the rotation. -/
noncomputable def rotOuts (X : Diagram G.toFreeGraphMonoid N E) {p d : N} (R : RotData X p d) (x : N) :
    List E :=
  if x = p then [R.H, R.m] else if x = d then [R.C, R.A] else X.outs x

theorem rotSrc_H {X : Diagram G.toFreeGraphMonoid N E} {p d : N} (R : RotData X p d) :
    X.rotSrc R R.H = some p := by
  classical
  simp [rotSrc]

theorem rotSrc_A {X : Diagram G.toFreeGraphMonoid N E} {p d : N} (R : RotData X p d) :
    X.rotSrc R R.A = some d := by
  classical
  simp [rotSrc, R.H_ne_A.symm]

theorem rotSrc_of_ne {X : Diagram G.toFreeGraphMonoid N E} {p d : N} (R : RotData X p d) {e : E}
    (hH : e ≠ R.H) (hA : e ≠ R.A) : X.rotSrc R e = X.src e := by
  classical
  simp [rotSrc, hH, hA]

theorem rotOuts_p {X : Diagram G.toFreeGraphMonoid N E} {p d : N} (R : RotData X p d) :
    X.rotOuts R p = [R.H, R.m] := by
  classical
  simp [rotOuts]

theorem rotOuts_d {X : Diagram G.toFreeGraphMonoid N E} {p d : N} (R : RotData X p d) :
    X.rotOuts R d = [R.C, R.A] := by
  classical
  simp [rotOuts, R.p_ne_d.symm]

theorem rotOuts_of_ne {X : Diagram G.toFreeGraphMonoid N E} {p d : N} (R : RotData X p d) {x : N}
    (hp : x ≠ p) (hd : x ≠ d) : X.rotOuts R x = X.outs x := by
  classical
  simp [rotOuts, hp, hd]

theorem rot_mem_outs {X : Diagram G.toFreeGraphMonoid N E} {p d : N} (R : RotData X p d) (x : N)
    (e : E) : e ∈ X.rotOuts R x ↔ X.rotSrc R e = some x := by
  by_cases hH : e = R.H
  · subst hH
    rw [rotSrc_H, Option.some.injEq]
    by_cases hxp : x = p
    · subst hxp; rw [rotOuts_p]; simp
    · by_cases hxd : x = d
      · subst hxd; rw [rotOuts_d]; simp [R.H_ne_C, R.H_ne_A, Ne.symm hxp]
      · rw [rotOuts_of_ne R hxp hxd, X.mem_outs, R.src_H, Option.some.injEq]
        constructor
        · intro h; exact absurd h.symm hxd
        · intro h; exact absurd h.symm hxp
  by_cases hA : e = R.A
  · subst hA
    rw [rotSrc_A, Option.some.injEq]
    by_cases hxp : x = p
    · subst hxp; rw [rotOuts_p]; simp [R.H_ne_A.symm, R.m_ne_A.symm, R.p_ne_d.symm]
    · by_cases hxd : x = d
      · subst hxd; rw [rotOuts_d]; simp
      · rw [rotOuts_of_ne R hxp hxd, X.mem_outs, R.src_A, Option.some.injEq]
        constructor
        · intro h; exact absurd h.symm hxp
        · intro h; exact absurd h.symm hxd
  rw [rotSrc_of_ne R hH hA]
  by_cases hxp : x = p
  · subst hxp
    rw [rotOuts_p, ← X.mem_outs, R.hop]
    simp [hH, hA]
  · by_cases hxd : x = d
    · subst hxd
      rw [rotOuts_d, ← X.mem_outs, R.hod]
      simp [hH, hA, or_comm]
    · rw [rotOuts_of_ne R hxp hxd, X.mem_outs]

theorem rot_adj {X : Diagram G.toFreeGraphMonoid N E} {p d : N} (R : RotData X p d) {u v : N}
    (h : EdgeAdj (X.rotSrc R) X.tgt u v) : X.Lt u v ∨ (u = d ∧ X.tgt R.A = some v) := by
  obtain ⟨e, he₁, he₂⟩ := h
  by_cases hH : e = R.H
  · subst hH
    rw [rotSrc_H, Option.some.injEq] at he₁
    subst he₁
    exact Or.inl ((X.lt_of_edge R.src_m R.tgt_m).trans (X.lt_of_edge R.src_H he₂))
  by_cases hA : e = R.A
  · subst hA
    rw [rotSrc_A, Option.some.injEq] at he₁
    exact Or.inr ⟨he₁.symm, he₂⟩
  rw [rotSrc_of_ne R hH hA] at he₁
  exact Or.inl (X.lt_of_edge he₁ he₂)

theorem rot_acyclic {X : Diagram G.toFreeGraphMonoid N E} {p d : N} (R : RotData X p d) (x : N) :
    ¬ TransGen (EdgeAdj (X.rotSrc R) X.tgt) x x := by
  intro hx
  have key : ∀ a b, TransGen (EdgeAdj (X.rotSrc R) X.tgt) a b →
      X.Lt a b ∨ (X.Le a d ∧ ∃ w, X.tgt R.A = some w ∧ X.Le w b) := by
    intro a b h
    induction h with
    | single h =>
      rcases rot_adj R h with h | ⟨rfl, hw⟩
      · exact Or.inl h
      · exact Or.inr ⟨Or.inr rfl, _, hw, Or.inr rfl⟩
    | tail _ h ih =>
      rcases rot_adj R h with h' | ⟨rfl, hw⟩
      · rcases ih with ih | ⟨h₁, w, hw, h₂⟩
        · exact Or.inl (ih.trans h')
        · exact Or.inr ⟨h₁, w, hw, h₂.trans (Or.inl h')⟩
      · rcases ih with ih | ⟨h₁, -, -, -⟩
        · exact Or.inr ⟨Or.inl ih, _, hw, Or.inr rfl⟩
        · exact Or.inr ⟨h₁, _, hw, Or.inr rfl⟩
  rcases key x x hx with h | ⟨h₁, w, hw, h₂⟩
  · exact X.lt_irrefl x h
  · exact R.not_le_tgt_A hw (h₂.trans h₁)

/-- **The rotation** `p(d(H, C), A) ↦ p(H, d(C, A))`. -/
noncomputable def rotate (X : Diagram G.toFreeGraphMonoid N E) {p d : N} (R : RotData X p d) :
    Diagram G.toFreeGraphMonoid N E where
  src := X.rotSrc R
  tgt := X.tgt
  ins := X.ins
  outs := X.rotOuts R
  ins_nodup := X.ins_nodup
  outs_nodup x := by
    by_cases hxp : x = p
    · subst hxp; rw [rotOuts_p]; simpa using R.H_ne_m
    · by_cases hxd : x = d
      · subst hxd; rw [rotOuts_d]; simpa using R.C_ne_A
      · rw [rotOuts_of_ne R hxp hxd]; exact X.outs_nodup x
  mem_ins := X.mem_ins
  mem_outs := rot_mem_outs R
  acyclic := rot_acyclic R
  dom := X.dom
  cod := X.cod
  dom_nodup := X.dom_nodup
  cod_nodup := X.cod_nodup
  mem_dom e := by
    by_cases hH : e = R.H
    · subst hH
      rw [rotSrc_H, X.mem_dom, R.src_H]
      simp
    by_cases hA : e = R.A
    · subst hA
      rw [rotSrc_A, X.mem_dom, R.src_A]
      simp
    rw [rotSrc_of_ne R hH hA]
    exact X.mem_dom e
  mem_cod := X.mem_cod
  val :=
    { v₀ := X.val.v₀
      v₁ := X.val.v₁
      s_v₁ := X.val.s_v₁
      t_v₁ := fun x => by
        by_cases hxp : x = p
        · subst hxp
          rw [rotOuts_p, R.hp, G.t_dup]
          simp [R.v₀_H, R.v₀_m]
        · by_cases hxd : x = d
          · subst hxd
            rw [rotOuts_d, R.hd, G.t_dup]
            simp [R.v₀_C, R.v₀_A]
          · rw [rotOuts_of_ne R hxp hxd]; exact X.val.t_v₁ x }

end Diagram

end FreeMarkov
