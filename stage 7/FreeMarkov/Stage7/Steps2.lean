/-
Free Markov categories, Stage 7: the value of a diagram does not depend on the order in which
the nodes are processed (Joyal–Street, Proposition 2.1: independence of the chain of levels).

* `two_step`: processing two independent nodes `x`, `y` in a row equals permuting the wires so
  that the inputs of `x`, then those of `y`, come first, applying `x ⊗ y`, and permuting back;
* `val_swap`: two independent nodes can be processed in either order;
* `val_indep`: any two orders in which the nodes can be processed give the same value.
-/
module

public import FreeMarkov.Stage7.Steps

@[expose] public section

universe v u w w'

namespace FreeMarkov

open CategoryTheory StrictSMC

namespace Wires

open AArr (comp tensor)

variable {C : Type u} [Monoid C] [CategoryTheory.Category.{v} C] [StrictSMC C]

namespace VData

variable {N : Type w'} {E : Type w} [DecidableEq E] (V : VData C N E)

omit [StrictSMC C] in
theorem rest_rest_comm (W : List E) (x y : N) :
    V.rest (V.rest W x) y = V.rest (V.rest W y) x := by
  simp only [rest, List.filter_filter]
  congr 1
  funext e
  exact Bool.and_comm _ _

omit [StrictSMC C] in
theorem rest_append_of_disj (A W : List E) (y : N) (h : ∀ e ∈ A, e ∉ V.ins y) :
    V.rest (A ++ W) y = A ++ V.rest W y := by
  simp only [rest, List.filter_append]
  congr 1
  exact List.filter_eq_self.2 fun e he => by simpa using h e he

omit [StrictSMC C] in
theorem rest_next_of_disj (W : List E) (x y : N) (h : ∀ e ∈ V.outs x, e ∉ V.ins y) :
    V.rest (V.next W x) y = V.outs x ++ V.rest (V.rest W x) y :=
  V.rest_append_of_disj _ _ _ h

omit [StrictSMC C] in
theorem next_next_perm (W : List E) (x y : N) (hxy : ∀ e ∈ V.outs x, e ∉ V.ins y)
    (hyx : ∀ e ∈ V.outs y, e ∉ V.ins x) :
    (V.next (V.next W x) y).Perm (V.next (V.next W y) x) := by
  have e₁ : V.next (V.next W x) y = V.outs y ++ (V.outs x ++ V.rest (V.rest W x) y) := by
    rw [VData.next, V.rest_next_of_disj W x y hxy]
  have e₂ : V.next (V.next W y) x = V.outs x ++ (V.outs y ++ V.rest (V.rest W x) y) := by
    rw [VData.next, V.rest_next_of_disj W y x hyx, rest_rest_comm]
  rw [e₁, e₂, ← List.append_assoc, ← List.append_assoc]
  exact List.Perm.append_right _ List.perm_append_comm

section TwoStep

variable {V}

/-- **Two independent nodes in a row.** -/
theorem two_step (hV : V.Good) {W : List E} {x y : N} (hW : W.Nodup)
    (hIx : ∀ e ∈ V.ins x, e ∈ W) (hOx : ∀ e ∈ V.outs x, e ∉ W) (hIy : ∀ e ∈ V.ins y, e ∈ W)
    (hxy : x ≠ y) (hxy' : ∀ e ∈ V.outs x, e ∉ V.ins y) :
    comp (V.step W x) (V.step (V.next W x) y) =
      comp (perm V.lab W (V.ins x ++ (V.ins y ++ V.rest (V.rest W x) y)))
        (comp (tensor (V.gen x) (tensor (V.gen y) (AArr.id (obj V.lab (V.rest (V.rest W x) y)))))
          (perm V.lab (V.outs x ++ (V.outs y ++ V.rest (V.rest W x) y))
            (V.outs y ++ (V.outs x ++ V.rest (V.rest W x) y)))) := by
  set R₁ := V.rest W x with hR₁
  set R := V.rest R₁ y with hR
  have hIy' : ∀ e ∈ V.ins y, e ∈ R₁ := fun e he =>
    (V.mem_rest).2 ⟨hIy e he, hV.ins_disj (Ne.symm hxy) e he⟩
  have hR₁n : R₁.Nodup := V.rest_nodup hW x
  have p₁ : W.Perm (V.ins x ++ R₁) := V.perm_rest hV hW hIx
  have p₂ : R₁.Perm (V.ins y ++ R) := V.perm_rest hV hR₁n hIy'
  have hn : V.next W x = V.outs x ++ R₁ := rfl
  have hr : V.rest (V.next W x) y = V.outs x ++ R := V.rest_next_of_disj W x y hxy'
  have gl := hV.gen_left
  have gr := hV.gen_right
  have nOI : (V.outs x ++ V.ins y).Nodup :=
    List.nodup_append.2 ⟨hV.outs_nodup x, hV.ins_nodup y, fun a ha b hb hab => hxy' a ha (hab ▸ hb)⟩
  have nOO : (V.outs x ++ V.outs y).Nodup :=
    List.nodup_append.2 ⟨hV.outs_nodup x, hV.outs_nodup y,
      fun a ha b hb hab => hV.outs_disj hxy a ha (hab ▸ hb)⟩
  -- the pieces
  have q₁ : perm V.lab (V.outs x ++ R₁) (V.outs x ++ (V.ins y ++ R)) =
      tensor (AArr.id (obj V.lab (V.outs x))) (perm V.lab R₁ (V.ins y ++ R)) := by
    rw [perm_append _ (List.Perm.refl _) p₂, perm_self]
  have q₂ : perm V.lab (V.outs x ++ (V.ins y ++ R)) (V.ins y ++ (V.outs x ++ R)) =
      tensor (AArr.braid (obj V.lab (V.outs x)) (obj V.lab (V.ins y))) (AArr.id (obj V.lab R)) := by
    rw [← List.append_assoc, ← List.append_assoc, perm_append _ List.perm_append_comm
      (List.Perm.refl _), perm_swap _ nOI, perm_self]
  have q₃ : perm V.lab (V.outs x ++ (V.outs y ++ R)) (V.outs y ++ (V.outs x ++ R)) =
      tensor (AArr.braid (obj V.lab (V.outs x)) (obj V.lab (V.outs y))) (AArr.id (obj V.lab R)) := by
    rw [← List.append_assoc, ← List.append_assoc, perm_append _ List.perm_append_comm
      (List.Perm.refl _), perm_swap _ nOO, perm_self]
  have q₄ : tensor (AArr.id (obj V.lab (V.ins x))) (perm V.lab R₁ (V.ins y ++ R)) =
      perm V.lab (V.ins x ++ R₁) (V.ins x ++ (V.ins y ++ R)) := by
    rw [perm_append _ (List.Perm.refl _) p₂, perm_self]
  have hp₁ : (V.ins x ++ R₁).Perm (V.ins x ++ (V.ins y ++ R)) := List.Perm.append_left _ p₂
  have hp₂ : (V.outs x ++ R₁).Perm (V.outs x ++ (V.ins y ++ R)) := List.Perm.append_left _ p₂
  have hp₃ : (V.outs x ++ (V.ins y ++ R)).Perm (V.ins y ++ (V.outs x ++ R)) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  have n₁ := AArr.braid_natural (V.gen x) (AArr.id (obj V.lab (V.ins y)))
  rw [gl, gr, AArr.id_left, AArr.id_right] at n₁
  have n₂ := AArr.braid_natural (V.gen x) (V.gen y)
  rw [gl, gr, gl, gr] at n₂
  have s₁ : V.step W x = comp (perm V.lab W (V.ins x ++ R₁))
      (tensor (V.gen x) (AArr.id (obj V.lab R₁))) := rfl
  have s₂ : V.step (V.next W x) y = comp (perm V.lab (V.outs x ++ R₁) (V.ins y ++ (V.outs x ++ R)))
      (tensor (tensor (V.gen y) (AArr.id (obj V.lab (V.outs x)))) (AArr.id (obj V.lab R))) := by
    rw [VData.step, hr, hn, obj_append, ← AArr.tensor_id, AArr.tensor_assoc]
  have ab : comp (tensor (V.gen x) (AArr.id (obj V.lab R₁)))
        (tensor (AArr.id (obj V.lab (V.outs x))) (perm V.lab R₁ (V.ins y ++ R))) =
      comp (tensor (AArr.id (obj V.lab (V.ins x))) (perm V.lab R₁ (V.ins y ++ R)))
        (tensor (V.gen x) (AArr.id (obj V.lab (V.ins y ++ R)))) := by
    rw [← AArr.tensor_comp, ← AArr.tensor_comp, AArr.comp_id, AArr.id_comp, AArr.id_comp,
      AArr.comp_id]
    all_goals simp [gl, gr, perm_left _ p₂, perm_right _ p₂]
  have cc : comp (tensor (V.gen x) (AArr.id (obj V.lab (V.ins y ++ R))))
        (comp (tensor (AArr.braid (obj V.lab (V.outs x)) (obj V.lab (V.ins y))) (AArr.id (obj V.lab R)))
          (tensor (tensor (V.gen y) (AArr.id (obj V.lab (V.outs x)))) (AArr.id (obj V.lab R)))) =
      comp (tensor (V.gen x) (tensor (V.gen y) (AArr.id (obj V.lab R))))
        (perm V.lab (V.outs x ++ (V.outs y ++ R)) (V.outs y ++ (V.outs x ++ R))) := by
    rw [q₃, obj_append, ← AArr.tensor_id, ← AArr.tensor_assoc, ← AArr.comp_assoc,
      ← AArr.tensor_comp_id, ← AArr.tensor_comp_id, ← AArr.tensor_assoc, ← AArr.tensor_comp_id, n₁,
      AArr.comp_assoc, ← AArr.tensor_comp, AArr.id_comp, AArr.comp_id, ← n₂]
    all_goals simp [gl, gr, mul_assoc]
  rw [s₁, s₂, ← perm_comp V.lab (d := V.outs x ++ R₁) (V.next_nodup hV hW hOx) hp₂ hp₃, q₁, q₂,
    AArr.comp_assoc, AArr.comp_assoc, ← AArr.comp_assoc (f := tensor (V.gen x) _), ab,
    AArr.comp_assoc, ← AArr.comp_assoc (f := perm V.lab W _), q₄, perm_comp _ hW p₁ hp₁, cc]
  all_goals simp [gl, gr, mul_assoc, perm_right _ p₁, perm_left _ p₂,
    perm_right _ p₂]

/-- **Two independent nodes can be processed in either order.** -/
theorem val_swap (hV : V.Good) {W : List E} {x y : N} {zs : List N} {c : List E} (hxy : x ≠ y)
    (h₁ : V.Ok W (x :: y :: zs)) (h₂ : V.Ok W (y :: x :: zs))
    (hc : (V.wend W (x :: y :: zs)).Perm c) :
    V.val W (x :: y :: zs) c = V.val W (y :: x :: zs) c := by
  obtain ⟨hW, hIx, hOx, h₁'⟩ := h₁
  obtain ⟨-, hIy, hOy, h₂'⟩ := h₂
  have hxy' : ∀ e ∈ V.outs x, e ∉ V.ins y := fun e he hey => hOx e he (hIy e hey)
  have hyx' : ∀ e ∈ V.outs y, e ∉ V.ins x := fun e he hex => hOy e he (hIx e hex)
  have hW2 := V.next_next_perm W x y hxy' hyx'
  have hc' : (V.wend W (y :: x :: zs)).Perm c := (V.wend_perm hW2.symm zs).trans hc
  have gl := hV.gen_left
  have gr := hV.gen_right
  set R := V.rest (V.rest W x) y with hR
  have hR' : V.rest (V.rest W y) x = R := V.rest_rest_comm W y x
  have e₁ : V.next (V.next W x) y = V.outs y ++ (V.outs x ++ R) := by
    rw [VData.next, V.rest_next_of_disj W x y hxy']
  have e₂ : V.next (V.next W y) x = V.outs x ++ (V.outs y ++ R) := by
    rw [VData.next, V.rest_next_of_disj W y x hyx', hR']
  have TSx := two_step hV hW hIx hOx hIy hxy hxy'
  have TSy := two_step hV hW hIy hOy hIx (Ne.symm hxy) hyx'
  rw [hR'] at TSy
  rw [← e₁, ← e₂] at TSx
  rw [← e₂, ← e₁] at TSy
  have nOO : (V.outs y ++ V.outs x).Nodup :=
    List.nodup_append.2 ⟨hV.outs_nodup y, hV.outs_nodup x,
      fun a ha b hb hab => hV.outs_disj (Ne.symm hxy) a ha (hab ▸ hb)⟩
  have nII : (V.ins x ++ V.ins y).Nodup :=
    List.nodup_append.2 ⟨hV.ins_nodup x, hV.ins_nodup y,
      fun a ha b hb hab => hV.ins_disj hxy a ha (hab ▸ hb)⟩
  have hIy₁ : ∀ e ∈ V.ins y, e ∈ V.rest W x := fun e he =>
    (V.mem_rest).2 ⟨hIy e he, hV.ins_disj (Ne.symm hxy) e he⟩
  have p₁ : W.Perm (V.ins x ++ (V.ins y ++ R)) :=
    (V.perm_rest hV hW hIx).trans (List.Perm.append_left _
      (V.perm_rest hV (V.rest_nodup hW x) hIy₁))
  have pI : (V.ins x ++ (V.ins y ++ R)).Perm (V.ins y ++ (V.ins x ++ R)) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  have pW : (V.next (V.next W x) y).Perm (V.next (V.next W y) x) := hW2
  have qI : perm V.lab (V.ins x ++ (V.ins y ++ R)) (V.ins y ++ (V.ins x ++ R)) =
      tensor (AArr.braid (obj V.lab (V.ins x)) (obj V.lab (V.ins y))) (AArr.id (obj V.lab R)) := by
    rw [← List.append_assoc, ← List.append_assoc, perm_append _ List.perm_append_comm
      (List.Perm.refl _), perm_swap _ nII, perm_self]
  have qO : perm V.lab (V.next (V.next W x) y) (V.next (V.next W y) x) =
      tensor (AArr.braid (obj V.lab (V.outs y)) (obj V.lab (V.outs x))) (AArr.id (obj V.lab R)) := by
    rw [e₁, e₂, ← List.append_assoc, ← List.append_assoc, perm_append _ List.perm_append_comm
      (List.Perm.refl _), perm_swap _ nOO, perm_self]
  have n₂ := AArr.braid_natural (V.gen x) (V.gen y)
  rw [gl, gr, gl, gr] at n₂
  have key : comp (tensor (AArr.braid (obj V.lab (V.ins x)) (obj V.lab (V.ins y))) (AArr.id (obj V.lab R)))
      (comp (tensor (V.gen y) (tensor (V.gen x) (AArr.id (obj V.lab R))))
        (tensor (AArr.braid (obj V.lab (V.outs y)) (obj V.lab (V.outs x))) (AArr.id (obj V.lab R)))) =
      tensor (V.gen x) (tensor (V.gen y) (AArr.id (obj V.lab R))) := by
    rw [← AArr.tensor_assoc, ← AArr.tensor_comp_id, ← AArr.tensor_comp_id, ← AArr.comp_assoc, ← n₂,
      AArr.comp_assoc, AArr.braid_braid, AArr.comp_id, AArr.tensor_assoc]
    all_goals simp [gl, gr]
  have h₁ : V.Ok W (x :: y :: zs) := ⟨hW, hIx, hOx, h₁'⟩
  have h₂ : V.Ok W (y :: x :: zs) := ⟨hW, hIy, hOy, h₂'⟩
  have pL : (V.outs y ++ (V.outs x ++ R)).Perm (V.outs x ++ (V.outs y ++ R)) := by
    rw [← e₁, ← e₂]; exact pW
  have hok2 : V.Ok (V.outs x ++ (V.outs y ++ R)) zs := by rw [← e₂]; exact h₂'.2.2.2
  have hW2'n : (V.next (V.next W y) x).Nodup :=
    V.next_nodup hV (V.next_nodup hV hW hOy) h₂'.2.2.1
  rw [V.val_cons hV h₁ hc, V.val_cons hV h₁' hc, V.val_perm hV h₁'.2.2.2 pW hc,
    V.val_cons hV h₂ hc', V.val_cons hV h₂' hc', ← AArr.comp_assoc, ← AArr.comp_assoc,
    ← AArr.comp_assoc, TSx, TSy]
  · congr 1
    rw [AArr.comp_assoc, AArr.comp_assoc, perm_comp _ hW2'n pW.symm pW, perm_self, AArr.comp_id,
      ← perm_comp V.lab hW p₁ pI, qI, qO, AArr.comp_assoc, key]
    all_goals simp [gl, gr, mul_assoc, ← hR, perm_right _ p₁,
      perm_left _ pL, perm_left _ pL.symm, perm_right _ pL.symm,
      e₁, e₂]
  all_goals simp [
    perm_left _ pL, perm_right _ pL,
    e₁, e₂, V.step_right hV hW hIx,
    V.step_right hV hW hIy, V.step_left hV h₁'.1 h₁'.2.1, V.step_right hV h₁'.1 h₁'.2.1,
    V.step_left hV h₂'.1 h₂'.2.1, V.step_right hV h₂'.1 h₂'.2.1,
    V.val_left hV hok2]

omit [StrictSMC C] in
theorem ok_swap_front (hV : V.Good) {W : List E} {z y : N} {zs : List N} (hzy : z ≠ y)
    (h : V.Ok W (z :: y :: zs)) (hIy : ∀ e ∈ V.ins y, e ∈ W) (hOy : ∀ e ∈ V.outs y, e ∉ W) :
    V.Ok W (y :: z :: zs) := by
  obtain ⟨hW, hIz, hOz, h'⟩ := h
  have hzy' : ∀ e ∈ V.outs z, e ∉ V.ins y := fun e he hey => hOz e he (hIy e hey)
  have hyz' : ∀ e ∈ V.outs y, e ∉ V.ins z := fun e he hez => hOy e he (hIz e hez)
  refine ⟨hW, hIy, hOy, V.next_nodup hV hW hOy, fun e he => ?_, fun e he he' => ?_,
    V.ok_of_perm h'.2.2.2 (V.next_next_perm W z y hzy' hyz')⟩
  · exact (V.mem_next).2 (Or.inr ⟨hIz e he, hV.ins_disj hzy e he⟩)
  · rcases (V.mem_next).1 he' with h₁ | h₁
    · exact hV.outs_disj hzy e he h₁
    · exact hOz e he h₁.1

/-- Moving a node to the front of a processing order, past nodes independent of it. -/
theorem val_move (hV : V.Good) {W : List E} {p q : List N} {y : N} (hp : y ∉ p)
    (h : V.Ok W (p ++ y :: q)) (hIy : ∀ e ∈ V.ins y, e ∈ W) (hOy : ∀ e ∈ V.outs y, e ∉ W) :
    V.Ok W (y :: (p ++ q)) ∧ (V.wend W (p ++ y :: q)).Perm (V.wend W (y :: (p ++ q))) ∧
      ∀ c, (V.wend W (p ++ y :: q)).Perm c → V.val W (p ++ y :: q) c = V.val W (y :: (p ++ q)) c := by
  induction p generalizing W with
  | nil => exact ⟨h, List.Perm.refl _, fun _ _ => rfl⟩
  | cons z p ih =>
    have hzy : z ≠ y := fun e => hp (by simp [e])
    obtain ⟨hW, hIz, hOz, h'⟩ := h
    have hIy' : ∀ e ∈ V.ins y, e ∈ V.next W z := fun e he =>
      (V.mem_next).2 (Or.inr ⟨hIy e he, hV.ins_disj (Ne.symm hzy) e he⟩)
    have hOy' : ∀ e ∈ V.outs y, e ∉ V.next W z := fun e he he' => by
      rcases (V.mem_next).1 he' with h₁ | h₁
      · exact hV.outs_disj (Ne.symm hzy) e he h₁
      · exact hOy e he h₁.1
    obtain ⟨ok₁, wp₁, v₁⟩ := ih (fun h => hp (by simp [h])) h' hIy' hOy'
    have hzy' : ∀ e ∈ V.outs z, e ∉ V.ins y := fun e he hey => hOz e he (hIy e hey)
    have hyz' : ∀ e ∈ V.outs y, e ∉ V.ins z := fun e he hez => hOy e he (hIz e hez)
    have ok₂ : V.Ok W (z :: y :: (p ++ q)) := ⟨hW, hIz, hOz, ok₁⟩
    have ok₃ : V.Ok W (y :: z :: (p ++ q)) := V.ok_swap_front hV hzy ok₂ hIy hOy
    have wp₂ : (V.wend W (z :: (p ++ y :: q))).Perm (V.wend W (y :: z :: (p ++ q))) :=
      wp₁.trans (V.wend_perm (V.next_next_perm W z y hzy' hyz') _)
    refine ⟨ok₃, wp₂, fun c hc => ?_⟩
    have hc₁ : (V.wend W (z :: y :: (p ++ q))).Perm c := wp₁.symm.trans hc
    have h₀ : V.Ok W (z :: (p ++ y :: q)) := ⟨hW, hIz, hOz, h'⟩
    rw [List.cons_append, V.val_cons hV h₀ hc, v₁ c hc,
      ← V.val_cons hV ok₂ hc₁, V.val_swap hV hzy ok₂ ok₃ hc₁]
    rfl

/-- **The value does not depend on the processing order** (Joyal–Street, Proposition 2.1). -/
theorem val_indep (hV : V.Good) {W : List E} {xs ys : List N} (hn : xs.Nodup) (hp : xs.Perm ys)
    (h₁ : V.Ok W xs) (h₂ : V.Ok W ys) :
    (V.wend W xs).Perm (V.wend W ys) ∧
      ∀ c, (V.wend W xs).Perm c → V.val W xs c = V.val W ys c := by
  classical
  induction ys generalizing W xs with
  | nil => rw [List.perm_nil.1 hp]; exact ⟨List.Perm.refl _, fun _ _ => rfl⟩
  | cons y ys ih =>
    have hy : y ∈ xs := hp.symm.subset (List.mem_cons_self ..)
    obtain ⟨P, Q, rfl, hP⟩ := split_first hy
    obtain ⟨hW, hIy, hOy, h₂'⟩ := h₂
    obtain ⟨ok, wp, v⟩ := V.val_move hV hP h₁ hIy hOy
    have hn' : (P ++ Q).Nodup := (List.perm_middle.nodup_iff.1 hn).of_cons
    have hp' : (P ++ Q).Perm ys := (List.perm_middle.symm.trans hp).cons_inv
    obtain ⟨wp', v'⟩ := ih hn' hp' ok.2.2.2 h₂'
    refine ⟨wp.trans wp', fun c hc => ?_⟩
    rw [v c hc, V.val_cons hV ok (wp.symm.trans hc), V.val_cons hV ⟨hW, hIy, hOy, h₂'⟩
      ((wp.trans wp').symm.trans hc), v' c (wp.symm.trans hc)]

end TwoStep

end VData

end Wires

end FreeMarkov
