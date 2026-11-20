/-
Trial of design decision D3 (PLAN.md): constructions on arbitrary finite types,
isomorphism classes through `Fin` representatives, and a transport lemma.

Toy case: finite sets labelled by `S` (the vertex data of a diagram without its
edges), up to label-preserving bijection, with disjoint union as the operation.
Classes of `Labelled.{u} S` live in `Type (u+1)`; classes of `FinLabelled S` live
in `Type`; `classEquiv` identifies them for every `u`, and disjoint union of
classes computed on representatives agrees with disjoint union on arbitrary types.

Not part of the library; compiled by `scripts/verify.py`.
-/
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum

universe u v w

namespace D3Toy

variable {S : Type}

/-- Labelled finite sets on an arbitrary type of nodes. -/
structure Labelled (S : Type) where
  N : Type u
  [fin : Fintype N]
  lab : N → S

attribute [instance] Labelled.fin

/-- Label-preserving bijection, across universes. -/
def Labelled.Iso (X : Labelled.{u} S) (Y : Labelled.{v} S) : Prop :=
  ∃ e : X.N ≃ Y.N, ∀ n, Y.lab (e n) = X.lab n

theorem Labelled.Iso.refl (X : Labelled.{u} S) : X.Iso X := ⟨Equiv.refl _, fun _ => rfl⟩

theorem Labelled.Iso.symm {X : Labelled.{u} S} {Y : Labelled.{v} S} (h : X.Iso Y) : Y.Iso X := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, fun n => by rw [← he, Equiv.apply_symm_apply]⟩

theorem Labelled.Iso.trans {X : Labelled.{u} S} {Y : Labelled.{v} S} {Z : Labelled.{w} S}
    (h : X.Iso Y) (h' : Y.Iso Z) : X.Iso Z := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun n => by simp [he', he]⟩

/-- Disjoint union, on arbitrary finite types. -/
def Labelled.sum (X Y : Labelled.{u} S) : Labelled.{u} S := ⟨X.N ⊕ Y.N, Sum.elim X.lab Y.lab⟩

theorem Labelled.Iso.sum {X X' : Labelled.{u} S} {Y Y' : Labelled.{v} S} (h : X.Iso Y)
    (h' : X'.Iso Y') : (X.sum X').Iso (Y.sum Y') := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.sumCongr e', by rintro (n | n); exacts [he n, he' n]⟩

/-- Representatives with nodes `Fin n`; this type lives in `Type`. -/
structure FinLabelled (S : Type) where
  n : ℕ
  lab : Fin n → S

/-- A representative, read in any universe. -/
def FinLabelled.toLabelled (X : FinLabelled S) : Labelled.{u} S :=
  ⟨ULift.{u} (Fin X.n), X.lab ∘ ULift.down⟩

/-- Choice of a representative (noncomputable: it chooses an enumeration). -/
noncomputable def Labelled.toFin (X : Labelled.{u} S) : FinLabelled S :=
  ⟨Fintype.card X.N, X.lab ∘ (Fintype.equivFin X.N).symm⟩

/-- Transport lemma: every labelled set is isomorphic to its representative. -/
theorem Labelled.iso_toFin (X : Labelled.{u} S) : X.Iso (X.toFin.toLabelled.{v}) :=
  ⟨(Fintype.equivFin X.N).trans Equiv.ulift.symm, fun n => by
    change X.lab ((Fintype.equivFin X.N).symm ((Fintype.equivFin X.N) n)) = X.lab n
    simp⟩

/-- A representative read in two universes. -/
theorem FinLabelled.iso_univ (X : FinLabelled S) : (X.toLabelled.{u}).Iso (X.toLabelled.{v}) :=
  ⟨Equiv.ulift.trans Equiv.ulift.symm, fun _ => rfl⟩

instance labelledSetoid : Setoid (Labelled.{u} S) :=
  ⟨Labelled.Iso, ⟨Labelled.Iso.refl, Labelled.Iso.symm, Labelled.Iso.trans⟩⟩

instance finSetoid : Setoid (FinLabelled S) :=
  ⟨fun X Y => (X.toLabelled.{0}).Iso (Y.toLabelled.{0}),
    ⟨fun _ => Labelled.Iso.refl _, Labelled.Iso.symm, Labelled.Iso.trans⟩⟩

/-- Classes on arbitrary types (in `Type (u+1)`) and classes of representatives
(in `Type`) correspond. -/
noncomputable def classEquiv : Quotient (labelledSetoid.{u} (S := S)) ≃ Quotient (finSetoid (S := S)) where
  toFun := Quotient.map Labelled.toFin fun X Y h =>
    ((X.iso_toFin.{u, 0}).symm.trans h).trans (Y.iso_toFin.{u, 0})
  invFun := Quotient.map FinLabelled.toLabelled.{u} fun X Y h =>
    (X.iso_univ.{u, 0}.trans h).trans Y.iso_univ.{0, u}
  left_inv q := Quotient.inductionOn q fun X =>
    Quotient.sound ((X.iso_toFin.{u, u}).symm)
  right_inv q := Quotient.inductionOn q fun X =>
    Quotient.sound ((X.toLabelled.{u}.iso_toFin.{u, 0}).symm.trans X.iso_univ.{u, 0})

/-- Disjoint union on representatives. -/
def FinLabelled.sum (X Y : FinLabelled S) : FinLabelled S :=
  ⟨X.n + Y.n, Sum.elim X.lab Y.lab ∘ finSumFinEquiv.symm⟩

/-- Compatibility: `classEquiv` carries disjoint union on arbitrary types to
disjoint union of representatives. -/
theorem toFin_sum (X Y : Labelled.{u} S) :
    (X.sum Y).toFin ≈ (X.toFin.sum Y.toFin) := by
  show Labelled.Iso _ _
  refine (((X.sum Y).iso_toFin.{u, 0}).symm.trans ?_)
  refine ((X.iso_toFin.{u, 0}).sum (Y.iso_toFin.{u, 0})).trans ?_
  refine ⟨((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
      (finSumFinEquiv.trans Equiv.ulift.symm) :
        ULift.{0} (Fin X.toFin.n) ⊕ ULift.{0} (Fin Y.toFin.n) ≃ ULift.{0} (Fin (X.toFin.n + Y.toFin.n))),
    ?_⟩
  rintro (n | n)
  · change Sum.elim X.toFin.lab Y.toFin.lab
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl n.down))) = X.toFin.lab n.down
    simp
  · change Sum.elim X.toFin.lab Y.toFin.lab
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr n.down))) = Y.toFin.lab n.down
    simp

end D3Toy
