/-
Free Markov categories, Stage 7: permutations of wires in a symmetric strict monoidal category.

For a list `d` of labelled wires (edges `e` with objects `ℓ e`) and a reordering `c` of `d`, the
arrow `perm ℓ d c : ⊗ d → ⊗ c` is built from symmetries by bringing the first wire of `c` to the
front and recursing.  It is the value of the node-free diagram from `d` to `c`.  Its laws are the
coherence theorem for symmetries that Joyal–Street's Theorem 2.3 contains (the case of diagrams
without nodes):

* `perm_self`: `perm d d = 1`;
* `perm_comp`: `perm d c ∘ perm c c' = perm d c'` (for duplicate-free lists);
* `perm_append`: `perm (d₁ ++ d₂) (c₁ ++ c₂) = perm d₁ c₁ ⊗ perm d₂ c₂`;
* `perm_swap`: `perm (d₁ ++ d₂) (d₂ ++ d₁) = σ_{⊗d₁, ⊗d₂}`;
* `perm_map`: invariance under renaming the wires.

The only braid identity needed beyond the axioms is `dm_obj`, an equation between two ways of
bringing two wires to the front.
-/
module

public import FreeMarkov.Stage7.ArrowAlg

@[expose] public section

universe v u w w'

namespace FreeMarkov

open CategoryTheory StrictSMC

namespace AArr

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictSMC C]

/-- `f ⊗ 1 ⊗ 1 = f ⊗ 1` for the product of the two identities. -/
theorem tensor_id_id (f : Arrow C) (X Y : C) :
    tensor (tensor f (id X)) (id Y) = tensor f (id (X * Y)) := by
  rw [tensor_assoc, tensor_id]

/-- Three wires: bringing `e` and then `f` in front of `a`, against `f` then `e` and a swap. -/
theorem dm_aux (a e f : C) :
    comp (comp (braid (a * e) f) (tensor (id f) (braid a e))) (tensor (braid f e) (id a)) =
      comp (tensor (braid a e) (id f)) (tensor (id e) (braid a f)) := by
  have n := braid_natural (braid a e) (id f)
  simp only [braid_left, braid_right, id_left, id_right] at n
  rw [← n, hexagon_reverse e a f, comp_assoc, comp_assoc, ← tensor_comp, braid_braid, id_comp,
    tensor_id, comp_id]
  all_goals aobj


theorem q4 (a e b f : C) :
    comp (comp (braid (a * (e * b)) f) (tensor (tensor (id f) (braid a e)) (id b)))
        (tensor (tensor (braid f e) (id a)) (id b)) =
      comp (tensor (tensor (braid a e) (id b)) (id f)) (tensor (id e) (braid (a * b) f)) := by
  have h₁ : braid (a * (e * b)) f =
      comp (tensor (id (a * e)) (braid b f)) (tensor (braid (a * e) f) (id b)) := by
    rw [← hexagon_reverse, mul_assoc]
  have hL : comp (comp (braid (a * (e * b)) f) (tensor (tensor (id f) (braid a e)) (id b)))
        (tensor (tensor (braid f e) (id a)) (id b)) =
      comp (tensor (id (a * e)) (braid b f))
        (tensor (comp (tensor (braid a e) (id f)) (tensor (id e) (braid a f))) (id b)) := by
    rw [h₁, comp_assoc, comp_assoc, ← tensor_comp_id, ← tensor_comp_id, ← comp_assoc, dm_aux]
    all_goals aobj
  have t₁ : comp (tensor (tensor (braid a e) (id b)) (id f)) (tensor (id e) (tensor (id a) (braid b f))) =
      tensor (braid a e) (braid b f) := by
    rw [tensor_assoc, tensor_id, ← tensor_assoc, tensor_id, ← tensor_comp, comp_id, id_comp]
    all_goals aobj
  have t₂ : comp (tensor (id (a * e)) (braid b f)) (tensor (tensor (braid a e) (id f)) (id b)) =
      tensor (braid a e) (braid b f) := by
    rw [tensor_assoc, tensor_id, ← tensor_comp, comp_id, id_comp]
    all_goals aobj
  rw [hL, hexagon_reverse a b f, tensor_id_comp, ← comp_assoc, t₁, ← t₂, comp_assoc,
    ← tensor_assoc (id e), ← tensor_comp_id]
  all_goals aobj

theorem dm_obj (a b c e f : C) :
    comp (comp (tensor (braid (a * (e * b)) f) (id c))
        (tensor (id f) (tensor (braid a e) (id (b * c)))))
      (tensor (braid f e) (id (a * (b * c)))) =
    comp (tensor (braid a e) (id (b * (f * c))))
      (tensor (id e) (tensor (braid (a * b) f) (id c))) := by
  have r₁ : tensor (id f) (tensor (braid a e) (id (b * c))) =
      tensor (tensor (tensor (id f) (braid a e)) (id b)) (id c) := by
    rw [tensor_assoc, tensor_assoc, tensor_id]
  have r₂ : tensor (braid f e) (id (a * (b * c))) =
      tensor (tensor (tensor (braid f e) (id a)) (id b)) (id c) := by
    rw [tensor_assoc, tensor_assoc, tensor_id, tensor_id]
  have r₃ : tensor (braid a e) (id (b * (f * c))) =
      tensor (tensor (tensor (braid a e) (id b)) (id f)) (id c) := by
    rw [tensor_assoc, tensor_assoc, tensor_id, tensor_id]
  have r₄ : tensor (id e) (tensor (braid (a * b) f) (id c)) =
      tensor (tensor (id e) (braid (a * b) f)) (id c) := by
    rw [tensor_assoc]
  rw [r₁, r₂, r₃, r₄, ← tensor_comp_id, ← tensor_comp_id, ← tensor_comp_id, q4]
  all_goals aobj

end AArr

/-! ### Wires -/

namespace Wires

open AArr (comp tensor)

variable {C : Type u} [Monoid C] [CategoryTheory.Category.{v} C] [StrictSMC C]
variable {E : Type w} [DecidableEq E] (ℓ : E → C)

/-- The object `⊗_{e ∈ l} ℓ e` of a list of labelled wires. -/
def obj (l : List E) : C := (l.map ℓ).prod

omit [Category.{v, u} C] [StrictSMC C] [DecidableEq E] in
@[simp] theorem obj_nil : obj ℓ [] = 1 := rfl

omit [Category.{v, u} C] [StrictSMC C] [DecidableEq E] in
@[simp] theorem obj_cons (e : E) (l : List E) : obj ℓ (e :: l) = ℓ e * obj ℓ l := by
  simp [obj]

omit [Category.{v, u} C] [StrictSMC C] [DecidableEq E] in
@[simp] theorem obj_append (l l' : List E) : obj ℓ (l ++ l') = obj ℓ l * obj ℓ l' := by
  simp [obj, List.prod_append]

omit [Category.{v, u} C] [StrictSMC C] [DecidableEq E] in
theorem obj_map {E' : Type w'} (φ : E' → E) (l : List E') : obj ℓ (l.map φ) = obj (ℓ ∘ φ) l := by
  simp [obj, List.map_map]

/-- Bringing the wire `e` of `d` to the front. -/
def mv (d : List E) (e : E) : Arrow C :=
  tensor (AArr.braid (obj ℓ (d.take (d.idxOf e))) (ℓ e)) (AArr.id (obj ℓ (d.drop (d.idxOf e + 1))))

/-- The permutation of wires from the ordering `d` to the ordering `c`: bring the first wire of
`c` to the front and recurse. -/
noncomputable def perm : List E → List E → Arrow C
  | d, [] => AArr.id (obj ℓ d)
  | d, e :: c => comp (mv ℓ d e) (tensor (AArr.id (ℓ e)) (perm (d.erase e) c))

theorem perm_cons (d : List E) (e : E) (c : List E) :
    perm ℓ d (e :: c) = comp (mv ℓ d e) (tensor (AArr.id (ℓ e)) (perm ℓ (d.erase e) c)) := rfl

theorem perm_nil (d : List E) : perm ℓ d [] = AArr.id (obj ℓ d) := rfl

omit [DecidableEq E] in
/-- Every element is somewhere first. -/
theorem split_first [DecidableEq E] {d : List E} {e : E} (h : e ∈ d) :
    ∃ P Q, d = P ++ e :: Q ∧ e ∉ P := by
  induction d with
  | nil => simp at h
  | cons a d ih =>
    by_cases hae : a = e
    · exact ⟨[], d, by rw [hae]; rfl, by simp⟩
    · obtain ⟨P, Q, rfl, hP⟩ := ih ((List.mem_cons.1 h).resolve_left (Ne.symm hae))
      exact ⟨a :: P, Q, rfl, by simp [Ne.symm hae, hP]⟩

theorem mv_eq {P Q : List E} {e : E} (h : e ∉ P) :
    mv ℓ (P ++ e :: Q) e = tensor (AArr.braid (obj ℓ P) (ℓ e)) (AArr.id (obj ℓ Q)) := by
  have hi : (P ++ e :: Q).idxOf e = P.length := by
    rw [List.idxOf_append_of_notMem h]; simp
  simp only [mv, hi]
  simp

omit [Monoid C] [CategoryTheory.Category.{v} C] [StrictSMC C] in
theorem erase_eq {P Q : List E} {e : E} (h : e ∉ P) : (P ++ e :: Q).erase e = P ++ Q := by
  rw [List.erase_append_right _ h, List.erase_cons_head]

theorem mv_left {d : List E} {e : E} (h : e ∈ d) : (mv ℓ d e).left = obj ℓ d := by
  obtain ⟨P, Q, rfl, hP⟩ := split_first h
  rw [mv_eq ℓ hP]; simp [mul_assoc]

theorem mv_right {d : List E} {e : E} (h : e ∈ d) :
    (mv ℓ d e).right = ℓ e * obj ℓ (d.erase e) := by
  obtain ⟨P, Q, rfl, hP⟩ := split_first h
  rw [mv_eq ℓ hP, erase_eq hP]; simp [mul_assoc]

omit [Monoid C] [CategoryTheory.Category.{v} C] [StrictSMC C] in
theorem perm_erase {d c : List E} {e : E} (h : d.Perm (e :: c)) : (d.erase e).Perm c := by
  simpa using h.erase e

omit [Monoid C] [CategoryTheory.Category.{v} C] [StrictSMC C] in
omit [DecidableEq E] in
theorem mem_of_perm {d c : List E} {e : E} (h : d.Perm (e :: c)) : e ∈ d :=
  h.symm.subset (List.mem_cons_self ..)

theorem perm_left {d c : List E} (h : d.Perm c) : (perm ℓ d c).left = obj ℓ d := by
  induction c generalizing d with
  | nil => rfl
  | cons e c ih => rw [perm_cons, AArr.comp_left', mv_left ℓ (mem_of_perm h)]

theorem perm_right {d c : List E} (h : d.Perm c) : (perm ℓ d c).right = obj ℓ c := by
  induction c generalizing d with
  | nil => simp [perm_nil, List.perm_nil.1 h]
  | cons e c ih =>
    have k : (mv ℓ d e).right = (tensor (AArr.id (ℓ e)) (perm ℓ (d.erase e) c)).left := by
      rw [mv_right ℓ (mem_of_perm h), AArr.tensor_left, perm_left ℓ (perm_erase h)]; simp
    rw [perm_cons, AArr.comp_right k, AArr.tensor_right, ih (perm_erase h)]
    simp

theorem mv_self (e : E) (d : List E) : mv ℓ (e :: d) e = AArr.id (ℓ e * obj ℓ d) := by
  have := mv_eq ℓ (P := []) (Q := d) (e := e) (by simp)
  simp only [List.nil_append] at this
  rw [this, obj_nil, AArr.braid_one_left, AArr.tensor_id]

/-- `perm d d = 1`. -/
theorem perm_self (d : List E) : perm ℓ d d = AArr.id (obj ℓ d) := by
  induction d with
  | nil => rfl
  | cons e d ih =>
    rw [perm_cons, List.erase_cons_head, ih, mv_self, AArr.tensor_id, AArr.id_comp (by simp), obj_cons]

/-- `perm (d₁ ++ d₂) (c₁ ++ c₂) = perm d₁ c₁ ⊗ perm d₂ c₂`. -/
theorem perm_append {d₁ c₁ d₂ c₂ : List E} (h₁ : d₁.Perm c₁) (h₂ : d₂.Perm c₂) :
    perm ℓ (d₁ ++ d₂) (c₁ ++ c₂) = tensor (perm ℓ d₁ c₁) (perm ℓ d₂ c₂) := by
  induction c₁ generalizing d₁ with
  | nil =>
    rw [List.perm_nil.1 h₁, List.nil_append, List.nil_append, perm_nil, obj_nil,
      AArr.id_one_tensor]
  | cons e c₁ ih =>
    have h₁' := perm_erase h₁
    obtain ⟨P, Q, rfl, hP⟩ := split_first (mem_of_perm h₁)
    have e₁ : P ++ e :: Q ++ d₂ = P ++ e :: (Q ++ d₂) := by simp
    have k : (P ++ Q).Perm c₁ := by rwa [erase_eq hP] at h₁'
    rw [List.cons_append, perm_cons, e₁, mv_eq ℓ hP, erase_eq hP, ← List.append_assoc,
      ih k, perm_cons, mv_eq ℓ hP, erase_eq hP]
    have k₁ : (tensor (AArr.braid (obj ℓ P) (ℓ e)) (AArr.id (obj ℓ Q))).right =
        (tensor (AArr.id (ℓ e)) (perm ℓ (P ++ Q) c₁)).left := by
      rw [AArr.tensor_left, perm_left ℓ k]; simp [mul_assoc]
    have k₂ : (AArr.id (obj ℓ d₂)).right = (perm ℓ d₂ c₂).left := by
      rw [perm_left ℓ h₂]; rfl
    rw [← AArr.id_comp (X := obj ℓ d₂) (f := perm ℓ d₂ c₂) (perm_left ℓ h₂).symm,
      AArr.tensor_comp k₁ k₂, ← AArr.tensor_assoc (AArr.id (ℓ e)), AArr.tensor_id_id, obj_append,
      AArr.id_comp (perm_left ℓ h₂).symm]

/-- `perm (d₁ ++ d₂) (d₂ ++ d₁) = σ_{⊗d₁, ⊗d₂}`. -/
theorem perm_swap {d₁ d₂ : List E} (h : (d₁ ++ d₂).Nodup) :
    perm ℓ (d₁ ++ d₂) (d₂ ++ d₁) = AArr.braid (obj ℓ d₁) (obj ℓ d₂) := by
  induction d₂ with
  | nil => simp [perm_self, AArr.braid_one_right]
  | cons e d₂ ih =>
    have he : e ∉ d₁ := fun h' => (List.nodup_append.1 h).2.2 e h' e (List.mem_cons_self ..) rfl
    have h' : (d₁ ++ d₂).Nodup := h.sublist (by simp)
    rw [List.cons_append, perm_cons, mv_eq ℓ he, erase_eq he, ih h', obj_cons, AArr.hexagon]

theorem idxOf_map_inj {E' : Type w'} [DecidableEq E'] {φ : E' → E} (hφ : Function.Injective φ)
    (e : E') (d : List E') : (d.map φ).idxOf (φ e) = d.idxOf e := by
  induction d with
  | nil => rfl
  | cons a d ih =>
    by_cases h : a = e
    · subst h; simp
    · simp [hφ.ne h, h, ih]

theorem perm_map {E' : Type w'} [DecidableEq E'] (φ : E' → E) (hφ : Function.Injective φ)
    (d c : List E') : perm ℓ (d.map φ) (c.map φ) = perm (ℓ ∘ φ) d c := by
  induction c generalizing d with
  | nil => simp [perm_nil, obj_map]
  | cons e c ih =>
    rw [List.map_cons, perm_cons, perm_cons, ← List.map_erase hφ, ih]
    congr 1
    simp only [mv]
    rw [idxOf_map_inj hφ, ← List.map_take, ← List.map_drop, obj_map, obj_map]
    rfl

end Wires

end FreeMarkov
