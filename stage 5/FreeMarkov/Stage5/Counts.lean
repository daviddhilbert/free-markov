/-
Free Markov categories, Stage 5: the number of nodes with a given value, for classes of diagrams
and for morphisms of `F_s(G)`.

`DClass.card a c` is the number of nodes with the value `a` in a diagram of the class `c`.  It is
additive under gluing and disjoint union, zero on identities and symmetries, and `1` or `0` on a
generator.  Through `J.cls` this counts, for a morphism of `F_s(G)` built from generators, how
often each generator occurs; it is used to recognise effect diagrams ("each node with the value
`κ_i` occurs once, the other nodes are duplicates and discards", Definition 5.4).

No cited result is used beyond the structure `J` through which morphisms of `F_s(G)` are read
as classes of diagrams.
-/
module

public import FreeMarkov.Stage5.Labels

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open CategoryTheory StrictSMC

/-- Nodes of `N ⊕ N'` with a given value under `Sum.elim`. -/
def subtypeSumElimEquiv {α : Type*} {N : Type u₁} {N' : Type u₂} (v : N → α) (v' : N' → α)
    (a : α) : {x : N ⊕ N' // Sum.elim v v' x = a} ≃ {x // v x = a} ⊕ {x // v' x = a} where
  toFun
    | ⟨.inl x, h⟩ => .inl ⟨x, h⟩
    | ⟨.inr x, h⟩ => .inr ⟨x, h⟩
  invFun
    | .inl ⟨x, h⟩ => ⟨.inl x, h⟩
    | .inr ⟨x, h⟩ => ⟨.inr x, h⟩
  left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
  right_inv := by rintro (⟨_, _⟩ | ⟨_, _⟩) <;> rfl

theorem natCard_sumElim {α : Type*} {N : Type u₁} {N' : Type u₂} [Finite N] [Finite N']
    (v : N → α) (v' : N' → α) (a : α) :
    Nat.card {x : N ⊕ N' // Sum.elim v v' x = a} = Nat.card {x // v x = a} + Nat.card {x // v' x = a} := by
  rw [Nat.card_congr (subtypeSumElimEquiv v v' a), Nat.card_sum]

namespace Diagram

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

/-- The number of nodes of `Γ` with the value `a`. -/
noncomputable def card (Γ : Diagram G N E) (a : G.A) : ℕ := Nat.card {x : N // Γ.val.v₁ x = a}

theorem Iso.card_eq {Γ : Diagram G N E} {Γ' : Diagram G N' E'} (i : Γ.Iso Γ') (a : G.A) :
    Γ.card a = Γ'.card a :=
  Nat.card_congr (Equiv.subtypeEquiv i.eN fun x => by rw [i.v₁_map])

end Diagram

namespace DClass

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {N' : Type u₃} {E' : Type u₄}

/-- The number of nodes with the value `a` in (any diagram of) the class `c`. -/
noncomputable def card (a : G.A) (c : DClass G) : ℕ :=
  Quotient.lift (fun Γ : Diagram.FinDiag G => Γ.2.card a)
    (fun _ _ h => (show Nonempty (Diagram.Iso _ _) from h).elim fun i => i.card_eq a) c

theorem card_mk (a : G.A) (Γ : Diagram G N E) [Finite N] [Finite E] :
    card a (mk Γ) = Γ.card a :=
  (Γ.isoToFin.card_eq a).symm

theorem card_tensor (a : G.A) (c d : DClass G) : card a (c.tensor d) = card a c + card a d := by
  induction c using DClass.ind with
  | h n m Γ =>
    induction d using DClass.ind with
    | h n' m' Δ =>
      rw [mk_tensor, card_mk, card_mk, card_mk]
      exact natCard_sumElim _ _ a

theorem card_comp (a : G.A) {c d : DClass G} (h : c.cod = d.dom) :
    card a (c.comp d) = card a c + card a d := by
  induction c using DClass.ind with
  | h n m Γ =>
    induction d using DClass.ind with
    | h n' m' Δ =>
      have h' : Γ.codWord = Δ.domWord := by
        rw [← dom_mk, ← cod_mk]; exact h
      rw [mk_comp _ _ h', card_mk, card_mk, card_mk]
      exact natCard_sumElim _ _ a

theorem card_idD (a : G.A) (b : FreeMonoid S) : card a (mk (Diagram.idD G b)) = 0 := by
  rw [card_mk]
  exact Nat.card_of_isEmpty

theorem card_braidD (a : G.A) (b b' : FreeMonoid S) : card a (mk (Diagram.braidD G b b')) = 0 := by
  rw [card_mk]
  exact Nat.card_of_isEmpty

open Classical in
theorem card_oneNode (a x : G.A) : card a (mk (Diagram.oneNode x)) = if x = a then 1 else 0 := by
  rw [card_mk]
  unfold Diagram.card
  split_ifs with h
  · subst h
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun _ _ => Subtype.ext rfl⟩, ⟨⟨(), rfl⟩⟩⟩
  · rw [Nat.card_eq_zero]
    left
    exact ⟨fun ⟨_, hx⟩ => h hx⟩

end DClass

namespace JoyalStreet

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S} (J : JoyalStreet G)

/-- The number of nodes with the value `a` in a diagram of a morphism of `F_s(G)`. -/
noncomputable def card (a : G.A) {b c : J.Fs} (f : b ⟶ c) : ℕ := DClass.card a (J.cls f)

variable {J}

@[simp] theorem card_comp (a : G.A) {b c d : J.Fs} (f : b ⟶ c) (g : c ⟶ d) :
    J.card a (f ≫ g) = J.card a f + J.card a g := by
  unfold card
  rw [cls_comp, DClass.card_comp _ ((J.cls_cod f).trans (J.cls_dom g).symm)]

@[simp] theorem card_tensor (a : G.A) {b c d e : J.Fs} (f : b ⟶ c) (g : d ⟶ e) :
    J.card a (f ⊗ₛ g) = J.card a f + J.card a g := by
  unfold card
  rw [cls_tensor, DClass.card_tensor]

@[simp] theorem card_id (a : G.A) (b : J.Fs) : J.card a (𝟙 b) = 0 := by
  exact DClass.card_idD a b

@[simp] theorem card_braid (a : G.A) (b c : J.Fs) : J.card a (σ_ b c) = 0 := by
  exact DClass.card_braidD a b c

@[simp] theorem card_eqToHom (a : G.A) {b c : J.Fs} (h : b = c) : J.card a (eqToHom h) = 0 := by
  subst h
  exact card_id a b

open Classical in
@[simp] theorem card_gen (a x : G.A) : J.card a (J.hom (DHom.gen x)) = if x = a then 1 else 0 := by
  unfold card
  rw [cls_hom]
  exact DClass.card_oneNode a x

end JoyalStreet

end FreeMarkov
