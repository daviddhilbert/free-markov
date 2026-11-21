/-
Free Markov categories, Stage 7: processing nodes beside wires they do not touch.

* `IsMap.steps_append_right`: processing the nodes of one piece with the wires of another piece
  on the right is the monoidal product of the processing with an identity;
* `step_passive_left`: with untouched wires `A` on the left, a step is `1_A ⊗ step` followed by
  moving the outputs in front of `A`;
* `IsMap.val_append_left`: the value with untouched wires `A` on the left is `1_A ⊗ value`.

These give the compatibility of values with disjoint union (Joyal–Street, Theorem 2.2).
-/
module

public import FreeMarkov.Stage7.Steps2

@[expose] public section

universe v u w w' w₂ w₃

namespace FreeMarkov

open CategoryTheory StrictSMC

namespace Wires

open AArr (comp tensor)

variable {C : Type u} [Monoid C] [CategoryTheory.Category.{v} C] [StrictSMC C]

namespace VData

/-! ### Untouched wires on the left of one step -/

section Left

variable {N : Type w'} {E : Type w} [DecidableEq E] (V : VData C N E)

theorem step_passive_left (hV : V.Good) {A W : List E} {y : N} (hAW : (A ++ W).Nodup)
    (hI : ∀ e ∈ V.ins y, e ∈ W) (hAI : ∀ e ∈ A, e ∉ V.ins y) (hAO : ∀ e ∈ A, e ∉ V.outs y) :
    V.step (A ++ W) y = comp (tensor (AArr.id (obj V.lab A)) (V.step W y))
      (perm V.lab (A ++ V.next W y) (V.next (A ++ W) y)) := by
  have hW : W.Nodup := hAW.sublist (by simp)
  have hr : V.rest (A ++ W) y = A ++ V.rest W y := V.rest_append_of_disj A W y hAI
  have gl := hV.gen_left y
  have gr := hV.gen_right y
  have p₁ : W.Perm (V.ins y ++ (V.rest W y)) := V.perm_rest hV hW hI
  have nAI : (A ++ V.ins y).Nodup :=
    List.nodup_append.2 ⟨hAW.sublist (by simp), hV.ins_nodup y,
      fun a ha b hb hab => hAI a ha (hab ▸ hb)⟩
  have nAO : (A ++ V.outs y).Nodup :=
    List.nodup_append.2 ⟨hAW.sublist (by simp), hV.outs_nodup y,
      fun a ha b hb hab => hAO a ha (hab ▸ hb)⟩
  have pA : (A ++ W).Perm (A ++ (V.ins y ++ (V.rest W y))) := List.Perm.append_left _ p₁
  have pB : (A ++ (V.ins y ++ (V.rest W y))).Perm (V.ins y ++ (A ++ (V.rest W y))) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  have q₁ : perm V.lab (A ++ W) (A ++ (V.ins y ++ (V.rest W y))) =
      tensor (AArr.id (obj V.lab A)) (perm V.lab W (V.ins y ++ (V.rest W y))) := by
    rw [perm_append _ (List.Perm.refl _) p₁, perm_self]
  have q₂ : perm V.lab (A ++ (V.ins y ++ (V.rest W y))) (V.ins y ++ (A ++ (V.rest W y))) =
      tensor (AArr.braid (obj V.lab A) (obj V.lab (V.ins y))) (AArr.id (obj V.lab (V.rest W y))) := by
    rw [← List.append_assoc, ← List.append_assoc, perm_append _ List.perm_append_comm
      (List.Perm.refl _), perm_swap _ nAI, perm_self]
  have q₃ : perm V.lab (A ++ V.next W y) (V.next (A ++ W) y) =
      tensor (AArr.braid (obj V.lab A) (obj V.lab (V.outs y))) (AArr.id (obj V.lab (V.rest W y))) := by
    rw [VData.next, VData.next, hr, ← List.append_assoc, ← List.append_assoc,
      perm_append _ List.perm_append_comm (List.Perm.refl _), perm_swap _ nAO, perm_self]
  have n := AArr.braid_natural (AArr.id (obj V.lab A)) (V.gen y)
  rw [gl, gr, AArr.id_left, AArr.id_right] at n
  rw [VData.step, hr, ← perm_comp V.lab hAW pA pB, q₁, q₂, q₃, VData.step,
    obj_append, ← AArr.tensor_id, ← AArr.tensor_assoc, AArr.comp_assoc, ← AArr.tensor_comp_id, ← n,
    AArr.tensor_comp_id, ← AArr.comp_assoc, AArr.tensor_assoc, ← AArr.tensor_id_comp]
  all_goals simp [gl, gr, mul_assoc, perm_right _ p₁]

end Left

/-! ### Renaming with untouched wires -/

section Map

variable {N : Type w'} {E : Type w} [DecidableEq E] {V : VData C N E}
  {N' : Type w₂} {E' : Type w₃} [DecidableEq E'] {V' : VData C N' E'} {φ : E → E'} {ψ : N → N'}

omit [StrictSMC C] [DecidableEq E] [DecidableEq E'] in
theorem IsMap.not_mem_ins (hm : IsMap V V' φ ψ) {b : E'} (hb : ∀ e, φ e ≠ b) (x : N) :
    b ∉ V'.ins (ψ x) := by
  rw [hm.ins]; simp [hb]

omit [StrictSMC C] [DecidableEq E] [DecidableEq E'] in
theorem IsMap.not_mem_outs (hm : IsMap V V' φ ψ) {b : E'} (hb : ∀ e, φ e ≠ b) (x : N) :
    b ∉ V'.outs (ψ x) := by
  rw [hm.outs]; simp [hb]

variable {B : List E'}

omit [StrictSMC C] in
theorem IsMap.rest_append_right (hm : IsMap V V' φ ψ) (hB : ∀ b ∈ B, ∀ e, φ e ≠ b)
    (W : List E) (x : N) :
    V'.rest (W.map φ ++ B) (ψ x) = (V.rest W x).map φ ++ B := by
  rw [VData.rest, List.filter_append, ← VData.rest, hm.rest]
  congr 1
  exact List.filter_eq_self.2 fun b hb => by simpa using hm.not_mem_ins (hB b hb) x

omit [StrictSMC C] in
theorem IsMap.next_append_right (hm : IsMap V V' φ ψ) (hB : ∀ b ∈ B, ∀ e, φ e ≠ b)
    (W : List E) (x : N) :
    V'.next (W.map φ ++ B) (ψ x) = (V.next W x).map φ ++ B := by
  rw [VData.next, hm.rest_append_right hB, VData.next, hm.outs, List.map_append,
    List.append_assoc]

omit [StrictSMC C] in
theorem IsMap.wend_append_right (hm : IsMap V V' φ ψ) (hB : ∀ b ∈ B, ∀ e, φ e ≠ b)
    (W : List E) (xs : List N) :
    V'.wend (W.map φ ++ B) (xs.map ψ) = (V.wend W xs).map φ ++ B := by
  induction xs generalizing W with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, wend_cons, hm.next_append_right hB, ih]; rfl

omit [StrictSMC C] [DecidableEq E] [DecidableEq E'] in
theorem IsMap.nodup_append_right (hm : IsMap V V' φ ψ) (hB : ∀ b ∈ B, ∀ e, φ e ≠ b)
    (hBn : B.Nodup) {W : List E} (hW : W.Nodup) : (W.map φ ++ B).Nodup :=
  List.nodup_append.2 ⟨List.Nodup.map hm.inj hW, hBn, fun a ha b hb hab => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 ha
    exact hB b hb e hab⟩

omit [StrictSMC C] in
theorem IsMap.ok_append_right (hm : IsMap V V' φ ψ) (hB : ∀ b ∈ B, ∀ e, φ e ≠ b) (hBn : B.Nodup)
    {W : List E} {xs : List N} (h : V.Ok W xs) : V'.Ok (W.map φ ++ B) (xs.map ψ) := by
  induction xs generalizing W with
  | nil => exact hm.nodup_append_right hB hBn h
  | cons x xs ih =>
    refine ⟨hm.nodup_append_right hB hBn h.1, fun e he => ?_, fun e he he' => ?_, ?_⟩
    · rw [hm.ins] at he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      exact List.mem_append_left _ (List.mem_map_of_mem (h.2.1 a ha))
    · rw [hm.outs] at he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      rcases List.mem_append.1 he' with h₁ | h₁
      · exact h.2.2.1 a ha ((List.mem_map_of_injective hm.inj).1 h₁)
      · exact hB _ h₁ a rfl
    · rw [hm.next_append_right hB]; exact ih h.2.2.2

theorem IsMap.steps_append_right (hm : IsMap V V' φ ψ) (hV : V.Good) (hB : ∀ b ∈ B, ∀ e, φ e ≠ b)
    {W : List E} {xs : List N} (h : V.Ok W xs) :
    V'.steps (W.map φ ++ B) (xs.map ψ) = tensor (V.steps W xs) (AArr.id (obj V'.lab B)) := by
  induction xs generalizing W with
  | nil => rw [List.map_nil, steps_nil, steps_nil, obj_append, hm.obj_map, AArr.tensor_id]
  | cons x xs ih =>
    have p₁ := V.perm_rest hV h.1 h.2.1
    have hst : V'.step (W.map φ ++ B) (ψ x) = tensor (V.step W x) (AArr.id (obj V'.lab B)) := by
      rw [VData.step, hm.rest_append_right hB, hm.ins, ← List.append_assoc, ← List.map_append,
        perm_append _ (List.Perm.map _ p₁) (List.Perm.refl _), perm_self, perm_map _ _ hm.inj,
        hm.lab_comp, obj_append, hm.obj_map, ← AArr.tensor_id, ← AArr.tensor_assoc, hm.gen,
        ← AArr.tensor_comp_id]
      · rfl
      · rw [perm_right _ p₁, AArr.tensor_left, hV.gen_left]; simp
    rw [List.map_cons, steps_cons, steps_cons, hst, hm.next_append_right hB, ih h.2.2.2,
      ← AArr.tensor_comp_id]
    rw [V.step_right hV h.1 h.2.1, V.steps_left hV h.2.2.2]

/-! ### Untouched wires on the left of a whole value -/

variable {A : List E'}

omit [StrictSMC C] in
theorem IsMap.rest_append_left (hm : IsMap V V' φ ψ) (hA : ∀ a ∈ A, ∀ e, φ e ≠ a)
    (W : List E) (x : N) :
    V'.rest (A ++ W.map φ) (ψ x) = A ++ (V.rest W x).map φ := by
  rw [V'.rest_append_of_disj _ _ _ fun a ha => hm.not_mem_ins (hA a ha) x, hm.rest]

omit [StrictSMC C] in
theorem IsMap.next_append_left (hm : IsMap V V' φ ψ) (hA : ∀ a ∈ A, ∀ e, φ e ≠ a)
    (W : List E) (x : N) :
    V'.next (A ++ W.map φ) (ψ x) = V'.outs (ψ x) ++ (A ++ (V.rest W x).map φ) := by
  rw [VData.next, hm.rest_append_left hA]

omit [StrictSMC C] [DecidableEq E] [DecidableEq E'] in
theorem IsMap.nodup_append_left (hm : IsMap V V' φ ψ) (hA : ∀ a ∈ A, ∀ e, φ e ≠ a)
    (hAn : A.Nodup) {W : List E} (hW : W.Nodup) : (A ++ W.map φ).Nodup :=
  List.nodup_append_comm.1 (hm.nodup_append_right hA hAn hW)

omit [StrictSMC C] in
theorem IsMap.ok_append_left (hm : IsMap V V' φ ψ) (hA : ∀ a ∈ A, ∀ e, φ e ≠ a) (hAn : A.Nodup)
    {W : List E} {xs : List N} (h : V.Ok W xs) : V'.Ok (A ++ W.map φ) (xs.map ψ) :=
  V'.ok_of_perm (hm.ok_append_right hA hAn h) List.perm_append_comm

omit [StrictSMC C] in
theorem IsMap.wend_append_left (hm : IsMap V V' φ ψ) (hA : ∀ a ∈ A, ∀ e, φ e ≠ a)
    (W : List E) (xs : List N) :
    (V'.wend (A ++ W.map φ) (xs.map ψ)).Perm (A ++ (V.wend W xs).map φ) := by
  have := V'.wend_perm (List.perm_append_comm (l₁ := A) (l₂ := W.map φ)) (xs.map ψ)
  rw [hm.wend_append_right hA] at this
  exact this.trans List.perm_append_comm

theorem IsMap.val_append_left (hm : IsMap V V' φ ψ) (hV : V.Good) (hV' : V'.Good)
    (hA : ∀ a ∈ A, ∀ e, φ e ≠ a) (hAn : A.Nodup) {W : List E} {xs : List N} {c : List E}
    (h : V.Ok W xs) (hc : (V.wend W xs).Perm c) :
    V'.val (A ++ W.map φ) (xs.map ψ) (A ++ c.map φ) =
      tensor (AArr.id (obj V'.lab A)) (V.val W xs c) := by
  induction xs generalizing W with
  | nil =>
    have hc0 : W.Perm c := hc
    rw [List.map_nil, V'.val_nil (List.Perm.append_left _ (List.Perm.map _ hc0)), V.val_nil hc0,
      perm_append _ (List.Perm.refl _) (List.Perm.map _ hc0), perm_self, perm_map _ _ hm.inj,
      hm.lab_comp]
  | cons x xs ih =>
    have h' := hm.ok_append_left hA hAn h
    have hc' : (V'.wend (A ++ W.map φ) ((x :: xs).map ψ)).Perm (A ++ c.map φ) :=
      (hm.wend_append_left hA W _).trans (List.Perm.append_left _ (List.Perm.map _ hc))
    have hAW : (A ++ W.map φ).Nodup := hm.nodup_append_left hA hAn h.1
    have hI : ∀ e ∈ V'.ins (ψ x), e ∈ W.map φ := fun e he => by
      rw [hm.ins] at he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      exact List.mem_map_of_mem (h.2.1 a ha)
    have hpn : (A ++ V'.next (W.map φ) (ψ x)).Perm (V'.next (A ++ W.map φ) (ψ x)) := by
      rw [VData.next, VData.next, hm.rest_append_left hA, hm.rest, ← List.append_assoc,
        ← List.append_assoc]
      exact List.Perm.append_right _ List.perm_append_comm
    have hn₀ : V'.next (W.map φ) (ψ x) = (V.next W x).map φ := hm.next W x
    have ok₁ : V'.Ok (A ++ (V.next W x).map φ) (xs.map ψ) := hm.ok_append_left hA hAn h.2.2.2
    have hc₁ : (V'.wend (A ++ (V.next W x).map φ) (xs.map ψ)).Perm (A ++ c.map φ) :=
      (hm.wend_append_left hA _ _).trans (List.Perm.append_left _ (List.Perm.map _ hc))
    have hpn0 := hpn
    have hWn : (W.map φ).Nodup := List.Nodup.map hm.inj h.1
    rw [List.map_cons, V'.val_cons hV' h' hc', V'.step_passive_left hV' hAW hI
      (fun a ha => hm.not_mem_ins (hA a ha) x) (fun a ha => hm.not_mem_outs (hA a ha) x),
      AArr.comp_assoc, hn₀]
    rw [hn₀] at hpn
    rw [← V'.val_perm hV' ok₁ hpn hc₁, ih h.2.2.2 hc, hm.step, ← AArr.tensor_id_comp,
      ← V.val_cons hV h hc]
    all_goals simp [V.step_right hV h.1 h.2.1, V.val_left hV h.2.2.2, V'.step_right hV' hWn hI,
      perm_left _ hpn0, perm_right _ hpn0, V'.val_left hV' h'.2.2.2]

end Map

end VData

end Wires

end FreeMarkov
