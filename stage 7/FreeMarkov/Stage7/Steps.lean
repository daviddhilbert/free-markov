/-
Free Markov categories, Stage 7: the value of a diagram computed node by node.

Abstract incidence data `VData` (ordered inputs and outputs of the nodes, the objects labelling
the edges, the arrows labelling the nodes) in a symmetric strict monoidal category.  Given an
ordering `W` of the wires present at some moment and a list `xs` of nodes, `steps W xs`
processes the nodes in order: for each node `x`, the wires are permuted so that the inputs of
`x` come first (in their order), the label of `x` is applied to them, and its outputs take
their place in front of the remaining wires.  `val W xs c` finally permutes the wires into the
ordering `c`.

This is Joyal–Street's computation of the value of a diagram from a chain of levels
(Chapter 2, §1, before Proposition 2.1), one node per level.  The results of this file are the
algebraic part of Proposition 2.1 and Theorem 2.2:

* `val_perm`: the ordering of the wires at the start does not matter (up to the permutation);
* `val_swap`, `val_indep`: the value does not depend on the order in which independent nodes
  are processed, hence on the chain of levels;
* `val_map`: renaming nodes and wires does not change the value;
* `steps_append`, `step_passive`: compatibility with composition and with a passive block of
  wires, used for gluing and disjoint union.
-/
module

public import FreeMarkov.Stage7.Perm2
public import Mathlib.Data.List.Nodup

@[expose] public section

universe v u w w' w₂ w₃

namespace FreeMarkov

open CategoryTheory StrictSMC

namespace Wires

open AArr (comp tensor)

variable {C : Type u} [Monoid C] [CategoryTheory.Category.{v} C] [StrictSMC C]

/-- Incidence data of a diagram with values in `C`. -/
structure VData (C : Type u) [Monoid C] [CategoryTheory.Category.{v} C] (N : Type w')
    (E : Type w) where
  /-- The ordered inputs of a node. -/
  ins : N → List E
  /-- The ordered outputs of a node. -/
  outs : N → List E
  /-- The objects labelling the edges. -/
  lab : E → C
  /-- The arrows labelling the nodes. -/
  gen : N → Arrow C

namespace VData

variable {N : Type w'} {E : Type w} [DecidableEq E] (V : VData C N E)

/-- The conditions on incidence data that hold for diagrams. -/
structure Good : Prop where
  gen_left (x : N) : (V.gen x).left = obj V.lab (V.ins x)
  gen_right (x : N) : (V.gen x).right = obj V.lab (V.outs x)
  ins_nodup (x : N) : (V.ins x).Nodup
  outs_nodup (x : N) : (V.outs x).Nodup
  ins_disj {x y : N} : x ≠ y → ∀ e ∈ V.ins x, e ∉ V.ins y
  outs_disj {x y : N} : x ≠ y → ∀ e ∈ V.outs x, e ∉ V.outs y

/-- The wires that remain when the node `x` takes its inputs from `W`. -/
def rest (W : List E) (x : N) : List E := W.filter fun e => decide (e ∉ V.ins x)

/-- The wires after processing the node `x`: its outputs, then the remaining wires. -/
def next (W : List E) (x : N) : List E := V.outs x ++ V.rest W x

/-- Processing one node. -/
noncomputable def step (W : List E) (x : N) : Arrow C :=
  comp (perm V.lab W (V.ins x ++ V.rest W x)) (tensor (V.gen x) (AArr.id (obj V.lab (V.rest W x))))

/-- The wires after processing a list of nodes. -/
def wend : List E → List N → List E
  | W, [] => W
  | W, x :: xs => wend (V.next W x) xs

/-- Processing a list of nodes. -/
noncomputable def steps : List E → List N → Arrow C
  | W, [] => AArr.id (obj V.lab W)
  | W, x :: xs => comp (V.step W x) (steps (V.next W x) xs)

/-- The value: process the nodes, then permute the wires into the ordering `c`. -/
noncomputable def val (W : List E) (xs : List N) (c : List E) : Arrow C :=
  comp (V.steps W xs) (perm V.lab (V.wend W xs) c)

/-- The list `xs` can be processed starting from the wires `W`. -/
def Ok : List E → List N → Prop
  | W, [] => W.Nodup
  | W, x :: xs => W.Nodup ∧ (∀ e ∈ V.ins x, e ∈ W) ∧ (∀ e ∈ V.outs x, e ∉ W) ∧ Ok (V.next W x) xs

omit [StrictSMC C] in
@[simp] theorem wend_nil (W : List E) : V.wend W [] = W := rfl
omit [StrictSMC C] in
@[simp] theorem wend_cons (W : List E) (x : N) (xs : List N) :
    V.wend W (x :: xs) = V.wend (V.next W x) xs := rfl
@[simp] theorem steps_nil (W : List E) : V.steps W [] = AArr.id (obj V.lab W) := rfl
theorem steps_cons (W : List E) (x : N) (xs : List N) :
    V.steps W (x :: xs) = comp (V.step W x) (V.steps (V.next W x) xs) := rfl
omit [StrictSMC C] in
@[simp] theorem ok_nil (W : List E) : V.Ok W [] ↔ W.Nodup := Iff.rfl
omit [StrictSMC C] in
@[simp] theorem ok_cons (W : List E) (x : N) (xs : List N) :
    V.Ok W (x :: xs) ↔ W.Nodup ∧ (∀ e ∈ V.ins x, e ∈ W) ∧ (∀ e ∈ V.outs x, e ∉ W) ∧
      V.Ok (V.next W x) xs := Iff.rfl

omit [StrictSMC C] in
theorem mem_rest {W : List E} {x : N} {e : E} : e ∈ V.rest W x ↔ e ∈ W ∧ e ∉ V.ins x := by
  simp [rest]

omit [StrictSMC C] in
theorem mem_next {W : List E} {x : N} {e : E} :
    e ∈ V.next W x ↔ e ∈ V.outs x ∨ (e ∈ W ∧ e ∉ V.ins x) := by
  simp [next, mem_rest]

omit [StrictSMC C] in
theorem ok_nodup {W : List E} {xs : List N} (h : V.Ok W xs) : W.Nodup := by
  cases xs with
  | nil => exact h
  | cons x xs => exact h.1

omit [StrictSMC C] in
theorem wend_nodup {W : List E} {xs : List N} (_hV : V.Good) (h : V.Ok W xs) :
    (V.wend W xs).Nodup := by
  induction xs generalizing W with
  | nil => exact h
  | cons x xs ih => exact ih h.2.2.2

omit [StrictSMC C] in
theorem rest_nodup {W : List E} (hW : W.Nodup) (x : N) : (V.rest W x).Nodup :=
  hW.filter _

omit [StrictSMC C] in
theorem perm_rest {W : List E} {x : N} (hV : V.Good) (hW : W.Nodup) (hI : ∀ e ∈ V.ins x, e ∈ W) :
    W.Perm (V.ins x ++ V.rest W x) := by
  have h₁ : W.Perm (W.filter (fun e => decide (e ∈ V.ins x)) ++ V.rest W x) := by
    have := List.filter_append_perm (fun e => decide (e ∈ V.ins x)) W
    simpa [rest] using this.symm
  refine h₁.trans (List.Perm.append_right _ ?_)
  refine (List.perm_ext_iff_of_nodup (hW.filter _) (hV.ins_nodup x)).2 fun e => ?_
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hI e h, h⟩⟩

omit [StrictSMC C] in
theorem next_nodup {W : List E} {x : N} (hV : V.Good) (hW : W.Nodup)
    (hO : ∀ e ∈ V.outs x, e ∉ W) : (V.next W x).Nodup := by
  refine List.nodup_append.2 ⟨hV.outs_nodup x, V.rest_nodup hW x, fun a ha b hb hab => ?_⟩
  subst hab
  exact hO a ha ((V.mem_rest).1 hb).1

omit [StrictSMC C] in
theorem rest_perm {W W' : List E} (h : W.Perm W') (x : N) : (V.rest W x).Perm (V.rest W' x) :=
  h.filter _

omit [StrictSMC C] in
theorem next_perm {W W' : List E} (h : W.Perm W') (x : N) : (V.next W x).Perm (V.next W' x) :=
  (V.rest_perm h x).append_left _

omit [StrictSMC C] in
/-- Processing is insensitive to the ordering of the wires. -/
theorem ok_of_perm {W W' : List E} {xs : List N} (h : V.Ok W xs) (hW : W.Perm W') : V.Ok W' xs := by
  induction xs generalizing W W' with
  | nil => exact hW.nodup_iff.1 h
  | cons x xs ih =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    exact ⟨hW.nodup_iff.1 h₁, fun e he => hW.subset (h₂ e he), fun e he he' => h₃ e he
      (hW.symm.subset he'), ih h₄ (V.next_perm hW x)⟩

omit [StrictSMC C] in
theorem wend_perm {W W' : List E} (hW : W.Perm W') (xs : List N) :
    (V.wend W xs).Perm (V.wend W' xs) := by
  induction xs generalizing W W' with
  | nil => exact hW
  | cons x xs ih => exact ih (V.next_perm hW x)

theorem step_left {W : List E} {x : N} (hV : V.Good) (hW : W.Nodup) (hI : ∀ e ∈ V.ins x, e ∈ W) :
    (V.step W x).left = obj V.lab W := by
  rw [step, AArr.comp_left', perm_left _ (V.perm_rest hV hW hI)]

theorem step_right {W : List E} {x : N} (hV : V.Good) (hW : W.Nodup) (hI : ∀ e ∈ V.ins x, e ∈ W) :
    (V.step W x).right = obj V.lab (V.next W x) := by
  have k : (perm V.lab W (V.ins x ++ V.rest W x)).right =
      (tensor (V.gen x) (AArr.id (obj V.lab (V.rest W x)))).left := by
    rw [perm_right _ (V.perm_rest hV hW hI), AArr.tensor_left, hV.gen_left]; simp
  rw [step, AArr.comp_right k, AArr.tensor_right, hV.gen_right]
  simp [next]

theorem steps_left {W : List E} {xs : List N} (hV : V.Good) (h : V.Ok W xs) :
    (V.steps W xs).left = obj V.lab W := by
  cases xs with
  | nil => rfl
  | cons x xs => rw [steps_cons, AArr.comp_left', V.step_left hV h.1 h.2.1]

theorem steps_right {W : List E} {xs : List N} (hV : V.Good) (h : V.Ok W xs) :
    (V.steps W xs).right = obj V.lab (V.wend W xs) := by
  induction xs generalizing W with
  | nil => rfl
  | cons x xs ih =>
    rw [steps_cons, AArr.comp_right (by rw [V.step_right hV h.1 h.2.1, V.steps_left hV h.2.2.2]),
      ih h.2.2.2]
    rfl

theorem val_left {W : List E} {xs : List N} {c : List E} (hV : V.Good) (h : V.Ok W xs) :
    (V.val W xs c).left = obj V.lab W := by
  rw [val, AArr.comp_left', V.steps_left hV h]

theorem val_right {W : List E} {xs : List N} {c : List E} (hV : V.Good) (h : V.Ok W xs)
    (hc : (V.wend W xs).Perm c) : (V.val W xs c).right = obj V.lab c := by
  rw [val, AArr.comp_right (by rw [V.steps_right hV h, perm_left _ hc]), perm_right _ hc]

theorem val_nil {W c : List E} (hc : W.Perm c) : V.val W [] c = perm V.lab W c := by
  rw [val, steps_nil, wend_nil, AArr.id_comp (perm_left V.lab hc).symm]

theorem val_cons {W : List E} {x : N} {xs : List N} {c : List E} (hV : V.Good)
    (h : V.Ok W (x :: xs)) (hc : (V.wend W (x :: xs)).Perm c) :
    V.val W (x :: xs) c = comp (V.step W x) (V.val (V.next W x) xs c) := by
  rw [val, steps_cons, AArr.comp_assoc]
  · rfl
  · rw [V.step_right hV h.1 h.2.1, V.steps_left hV h.2.2.2]
  · rw [V.steps_right hV h.2.2.2, perm_left _ hc]; rfl

theorem perm_next {W W' : List E} {x : N} (_hV : V.Good) (hW : W.Perm W') :
    perm V.lab (V.next W x) (V.next W' x) =
      tensor (AArr.id (obj V.lab (V.outs x))) (perm V.lab (V.rest W x) (V.rest W' x)) := by
  rw [next, next, perm_append _ (List.Perm.refl _) (V.rest_perm hW x), perm_self]

/-- One step commutes with a permutation of the wires. -/
theorem step_perm {W W' : List E} {x : N} (hV : V.Good) (hWn : W.Nodup) (hW : W.Perm W')
    (hI : ∀ e ∈ V.ins x, e ∈ W) :
    comp (V.step W x) (perm V.lab (V.next W x) (V.next W' x)) =
      comp (perm V.lab W W') (V.step W' x) := by
  have hI' : ∀ e ∈ V.ins x, e ∈ W' := fun e he => hW.subset (hI e he)
  have p₁ := V.perm_rest hV hWn hI
  have p₂ := V.perm_rest hV (hW.nodup_iff.1 hWn) hI'
  have pr := V.rest_perm hW x
  have hg₁ := hV.gen_left x
  have hg₂ := hV.gen_right x
  rw [V.perm_next hV hW, step, step, AArr.comp_assoc, ← AArr.tensor_comp, AArr.comp_id,
    AArr.id_comp, AArr.tensor_eq_comp_id_left, ← AArr.comp_assoc, hg₁,
    ← perm_self V.lab (V.ins x), ← perm_append _ (List.Perm.refl _) pr,
    perm_comp _ hWn p₁ (List.Perm.append_left _ pr), ← AArr.comp_assoc,
    perm_comp _ hWn hW p₂]
  all_goals simp [perm_right _ p₁, perm_left _ p₂, perm_right _ p₂, perm_left _ pr,
    perm_right _ pr, perm_right _ hW, hg₁, hg₂]

/-- **The ordering of the wires at the start does not matter**, up to the permutation. -/
theorem val_perm {W W' : List E} {xs : List N} {c : List E} (hV : V.Good) (h : V.Ok W xs)
    (hW : W.Perm W') (hc : (V.wend W xs).Perm c) :
    V.val W xs c = comp (perm V.lab W W') (V.val W' xs c) := by
  induction xs generalizing W W' with
  | nil =>
    have hc0 : W.Perm c := hc
    rw [V.val_nil hc0, V.val_nil ((hW.symm.trans hc0)), perm_comp _ h hW (hW.symm.trans hc0)]
  | cons x xs ih =>
    have h' : V.Ok W' (x :: xs) := V.ok_of_perm h hW
    have hc' : (V.wend W' (x :: xs)).Perm c := (V.wend_perm hW _).symm.trans hc
    have hn := V.next_perm hW x
    rw [V.val_cons hV h hc, V.val_cons hV h' hc', ih h.2.2.2 hn hc, ← AArr.comp_assoc,
      V.step_perm hV h.1 hW h.2.1, AArr.comp_assoc]
    · rw [perm_right _ hW, V.step_left hV h'.1 h'.2.1]
    · rw [V.step_right hV h'.1 h'.2.1, V.val_left hV h'.2.2.2]
    · rw [V.step_right hV h.1 h.2.1, perm_left _ hn]
    · rw [perm_right _ hn, V.val_left hV h'.2.2.2]

/-! ### Composition of lists of nodes -/

omit [StrictSMC C] in
@[simp] theorem wend_append (W : List E) (xs ys : List N) :
    V.wend W (xs ++ ys) = V.wend (V.wend W xs) ys := by
  induction xs generalizing W with
  | nil => rfl
  | cons x xs ih => exact ih _

omit [StrictSMC C] in
theorem ok_append {W : List E} {xs ys : List N} :
    V.Ok W (xs ++ ys) ↔ V.Ok W xs ∧ V.Ok (V.wend W xs) ys := by
  induction xs generalizing W with
  | nil =>
    simp only [List.nil_append, ok_nil, wend_nil]
    exact ⟨fun h => ⟨V.ok_nodup h, h⟩, fun h => h.2⟩
  | cons x xs ih =>
    simp only [List.cons_append, ok_cons, wend_cons, ih]
    tauto

theorem steps_append {W : List E} {xs ys : List N} (hV : V.Good) (h : V.Ok W (xs ++ ys)) :
    V.steps W (xs ++ ys) = comp (V.steps W xs) (V.steps (V.wend W xs) ys) := by
  induction xs generalizing W with
  | nil =>
    rw [List.nil_append, steps_nil, wend_nil, AArr.id_comp]
    rw [V.steps_left hV (by simpa using h)]
  | cons x xs ih =>
    rw [List.cons_append, steps_cons, steps_cons, ih h.2.2.2, AArr.comp_assoc]
    · rfl
    · have h₂ := (V.ok_append.1 h.2.2.2).1
      rw [V.step_right hV h.1 h.2.1, V.steps_left hV h₂]
    · have h₂ := V.ok_append.1 h.2.2.2
      rw [V.steps_right hV h₂.1, wend_cons, V.steps_left hV h₂.2]

theorem val_append {W : List E} {xs ys : List N} {c : List E} (hV : V.Good)
    (h : V.Ok W (xs ++ ys)) (hc : (V.wend W (xs ++ ys)).Perm c) :
    V.val W (xs ++ ys) c = comp (V.steps W xs) (V.val (V.wend W xs) ys c) := by
  have h₂ := V.ok_append.1 h
  rw [val, V.steps_append hV h, AArr.comp_assoc, wend_append]
  · rfl
  · rw [V.steps_right hV h₂.1, V.steps_left hV h₂.2]
  · rw [V.steps_right hV h₂.2, perm_left _ (by simpa using hc), wend_append]

/-! ### Renaming -/

section Map

variable {N' : Type w₂} {E' : Type w₃} [DecidableEq E'] (V' : VData C N' E') (φ : E → E')
  (ψ : N → N')

/-- `V'` restricted along `φ`, `ψ` is `V`. -/
structure IsMap : Prop where
  inj : Function.Injective φ
  ins (x : N) : V'.ins (ψ x) = (V.ins x).map φ
  outs (x : N) : V'.outs (ψ x) = (V.outs x).map φ
  lab (e : E) : V'.lab (φ e) = V.lab e
  gen (x : N) : V'.gen (ψ x) = V.gen x

variable {V V' φ ψ}

omit [StrictSMC C] [DecidableEq E] [DecidableEq E'] in
theorem IsMap.lab_comp (hm : IsMap V V' φ ψ) : V'.lab ∘ φ = V.lab := funext hm.lab

omit [StrictSMC C] [DecidableEq E] [DecidableEq E'] in
theorem IsMap.obj_map (hm : IsMap V V' φ ψ) (l : List E) : obj V'.lab (l.map φ) = obj V.lab l := by
  rw [Wires.obj_map, hm.lab_comp]

omit [StrictSMC C] in
theorem IsMap.rest (hm : IsMap V V' φ ψ) (W : List E) (x : N) :
    V'.rest (W.map φ) (ψ x) = (V.rest W x).map φ := by
  rw [VData.rest, VData.rest, List.filter_map, hm.ins]
  congr 1
  apply List.filter_congr
  intro e _
  simp only [Function.comp_apply, List.mem_map_of_injective hm.inj]

omit [StrictSMC C] in
theorem IsMap.next (hm : IsMap V V' φ ψ) (W : List E) (x : N) :
    V'.next (W.map φ) (ψ x) = (V.next W x).map φ := by
  rw [VData.next, VData.next, hm.rest, hm.outs, List.map_append]

theorem IsMap.step (hm : IsMap V V' φ ψ) (W : List E) (x : N) :
    V'.step (W.map φ) (ψ x) = V.step W x := by
  rw [VData.step, VData.step, hm.rest, hm.ins, ← List.map_append, perm_map _ _ hm.inj,
    hm.lab_comp, hm.obj_map, hm.gen]

omit [StrictSMC C] in
theorem IsMap.wend (hm : IsMap V V' φ ψ) (W : List E) (xs : List N) :
    V'.wend (W.map φ) (xs.map ψ) = (V.wend W xs).map φ := by
  induction xs generalizing W with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, wend_cons, hm.next, ih]; rfl

theorem IsMap.steps (hm : IsMap V V' φ ψ) (W : List E) (xs : List N) :
    V'.steps (W.map φ) (xs.map ψ) = V.steps W xs := by
  induction xs generalizing W with
  | nil => rw [List.map_nil, steps_nil, steps_nil, hm.obj_map]
  | cons x xs ih => rw [List.map_cons, steps_cons, steps_cons, hm.step, hm.next, ih]

/-- **Renaming nodes and wires does not change the value.** -/
theorem IsMap.val (hm : IsMap V V' φ ψ) (W : List E) (xs : List N) (c : List E) :
    V'.val (W.map φ) (xs.map ψ) (c.map φ) = V.val W xs c := by
  rw [VData.val, VData.val, hm.steps, hm.wend, perm_map _ _ hm.inj, hm.lab_comp]

omit [StrictSMC C] in
theorem IsMap.ok (hm : IsMap V V' φ ψ) {W : List E} {xs : List N} (h : V.Ok W xs) :
    V'.Ok (W.map φ) (xs.map ψ) := by
  induction xs generalizing W with
  | nil => exact List.Nodup.map hm.inj h
  | cons x xs ih =>
    refine ⟨List.Nodup.map hm.inj h.1, ?_, ?_, ?_⟩
    · intro e he
      rw [hm.ins] at he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      exact List.mem_map_of_mem (h.2.1 a ha)
    · intro e he he'
      rw [hm.outs] at he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      exact h.2.2.1 a ha ((List.mem_map_of_injective hm.inj).1 he')
    · rw [hm.next]; exact ih h.2.2.2

end Map

end VData

end Wires

end FreeMarkov
