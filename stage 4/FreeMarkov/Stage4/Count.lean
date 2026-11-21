/-
Free Markov categories, Stage 4: the count behind the first item of Lemma 4.3.

"Let `d` be a node whose value is a duplicate and `q` the origin of its input. The edges with
the origin `q` form a tree that branches at duplicates, and `d ∈ Δ̃_Γ` if and only if through
each of the two outputs of `d` there is a directed path that ends in `cod(Γ)`, that is, if and
only if each of the two branches at `d` contains a consumer. So, if `n ≥ 1` is the number of the
consumers with the origin `q`, then exactly `n - 1` duplicates in this tree belong to `Δ̃_Γ`."

`binCount_add`: for every edge `e`, the number of duplicates in `Δ̃_Γ` whose input follows `e`
through duplicates, plus one if a consumer follows `e`, is the number of consumers following `e`
through duplicates.
-/
module

public import FreeMarkov.Stage4.Basic

@[expose] public section

universe u₁ u₂

namespace FreeMarkov

open Relation

namespace PGraph

variable {N : Type u₁} {E : Type u₂} {Γ : PGraph N E} {D : N → Prop}

theorem card_filter_or_of_disjoint {α : Type*} [Fintype α] (P q r : α → Prop) [DecidablePred P]
    [DecidablePred q] [DecidablePred r] (h : ∀ y, P y ↔ q y ∨ r y) (hd : ∀ y, q y → ¬ r y) :
    (Finset.univ.filter P).card = (Finset.univ.filter q).card + (Finset.univ.filter r).card := by
  classical
  rw [Finset.filter_congr (fun y _ => h y), Finset.filter_or,
    Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun y _ => hd y)]

theorem card_filter_eq_zero {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (h : ∀ y, ¬ P y) : (Finset.univ.filter P).card = 0 := by
  simp [h]

theorem card_filter_eq_single {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] (a : α) (h : ∀ y, P y ↔ y = a) : (Finset.univ.filter P).card = 1 := by
  classical
  rw [Finset.card_eq_one]
  exact ⟨a, by ext y; simp [h]⟩

theorem reflTransGen_dup_of_not_step {e c : E} (h : ∀ e', ¬ Γ.DupStep D e e')
    (hc : ReflTransGen (Γ.DupStep D) e c) : c = e := by
  rcases hc.cases_head with rfl | ⟨e', he', -⟩
  · rfl
  · exact (h e' he').elim

theorem transGen_step_of_dup {e e' c : E} (h : Γ.DupStep D e e') (hc : ReflTransGen (Γ.DupStep D) e' c) :
    TransGen Γ.Step e c :=
  TransGen.head' h.step (reflTransGen_step_of_dup hc)

/-- Two different outputs of the same duplicate: neither follows the other. -/
theorem not_reflTransGen_sibling (hD : Γ.DupCond D) {e e₁ e₂ : E} (h₁ : Γ.DupStep D e e₁)
    (h₂ : Γ.DupStep D e e₂) (hne : e₁ ≠ e₂) : ¬ ReflTransGen (Γ.DupStep D) e₁ e₂ := by
  intro h
  rcases h.cases_tail with rfl | ⟨g, hg, hg₂⟩
  · exact hne rfl
  · have : g = e := DupStep.unique hD hg₂ h₂
    subst this
    exact not_transGen_step_self _ (transGen_step_of_dup h₁ hg)

variable (Γ D)

/-- A consumer follows `e` through duplicates. -/
def Useful (e : E) : Prop := ∃ c, ReflTransGen (Γ.DupStep D) e c ∧ Γ.Consumer D c

open scoped Classical in
/-- The number of consumers following `e` through duplicates. -/
noncomputable def consCount [Fintype E] (e : E) : ℕ :=
  (Finset.univ.filter fun c => ReflTransGen (Γ.DupStep D) e c ∧ Γ.Consumer D c).card

open scoped Classical in
/-- The number of duplicates in `Δ̃_Γ` whose input follows `e` through duplicates. -/
noncomputable def binCount [Fintype N] (e : E) : ℕ :=
  (Finset.univ.filter fun y =>
    D y ∧ ¬ Γ.QuasiTerminal D y ∧ ∃ f ∈ Γ.ins y, ReflTransGen (Γ.DupStep D) e f).card

variable {Γ D}

theorem useful_iff_reachCod [Finite E] (e : E) : Γ.Useful D e ↔ Γ.ReachCod e := by
  constructor
  · rintro ⟨c, hc, hc'⟩
    exact hc'.reachCod.of_reflTransGen (reflTransGen_step_of_dup hc)
  · exact exists_consumer_of_reachCod

open scoped Classical in
/-- **The count of the proof of Lemma 4.3, first item.** -/
theorem binCount_add [Fintype N] [Fintype E] (hD : Γ.DupCond D)
    (hD₂ : ∀ x, D x → ∃ e₁ e₂, Γ.outs x = [e₁, e₂]) (e : E) :
    Γ.binCount D e + (if Γ.Useful D e then 1 else 0) = Γ.consCount D e := by
  induction e using Γ.wellFounded_down.induction with
  | _ e ih =>
    unfold binCount consCount
    cases hte : Γ.tgt e with
    | none =>
      have hns : ∀ e', ¬ Γ.DupStep D e e' := by
        rintro e' ⟨x, -, hx, -⟩
        rw [hte] at hx
        cases hx
      have hcons : Γ.Consumer D e := Or.inl hte
      rw [card_filter_eq_zero _ (fun y ⟨_, _, f, hf, hef⟩ => by
          have := reflTransGen_dup_of_not_step hns hef
          subst this
          rw [(Γ.mem_ins y f).1 hf] at hte
          cases hte),
        card_filter_eq_single _ e (fun c => ⟨fun h => reflTransGen_dup_of_not_step hns h.1,
          fun h => by subst h; exact ⟨ReflTransGen.refl, hcons⟩⟩),
        ite_eq_left ⟨e, ReflTransGen.refl, hcons⟩]
    | some x =>
      by_cases hDx : D x
      · obtain ⟨e₁, e₂, hx⟩ := hD₂ x hDx
        have hne : e₁ ≠ e₂ := by
          have := Γ.outs_nodup x
          rw [hx] at this
          simpa using this
        have hst₁ : Γ.DupStep D e e₁ :=
          ⟨x, hDx, hte, (Γ.mem_outs x e₁).1 (by rw [hx]; simp)⟩
        have hst₂ : Γ.DupStep D e e₂ :=
          ⟨x, hDx, hte, (Γ.mem_outs x e₂).1 (by rw [hx]; simp)⟩
        have hsub : ∀ c, ReflTransGen (Γ.DupStep D) e c ↔
            c = e ∨ ReflTransGen (Γ.DupStep D) e₁ c ∨ ReflTransGen (Γ.DupStep D) e₂ c := by
          intro c
          constructor
          · intro h
            rcases h.cases_head with rfl | ⟨e', ⟨y, -, hy, hy'⟩, h'⟩
            · exact Or.inl rfl
            · rw [hte, Option.some.injEq] at hy
              subst hy
              have : e' ∈ Γ.outs x := (Γ.mem_outs x e').2 hy'
              rw [hx] at this
              rcases List.mem_pair.1 this with rfl | rfl
              · exact Or.inr (Or.inl h')
              · exact Or.inr (Or.inr h')
          · rintro (rfl | h | h)
            · exact ReflTransGen.refl
            · exact ReflTransGen.head hst₁ h
            · exact ReflTransGen.head hst₂ h
        have hnot₁ : ∀ c, ReflTransGen (Γ.DupStep D) e₁ c → c ≠ e := by
          rintro c h rfl
          exact not_transGen_step_self _ (transGen_step_of_dup hst₁ h)
        have hnot₂ : ∀ c, ReflTransGen (Γ.DupStep D) e₂ c → c ≠ e := by
          rintro c h rfl
          exact not_transGen_step_self _ (transGen_step_of_dup hst₂ h)
        have hdisj : ∀ c, ReflTransGen (Γ.DupStep D) e₁ c → ¬ ReflTransGen (Γ.DupStep D) e₂ c := by
          intro c h₁ h₂
          rcases reflTransGen_dup_total hD h₁ h₂ with h | h
          · exact not_reflTransGen_sibling hD hst₁ hst₂ hne h
          · exact not_reflTransGen_sibling hD hst₂ hst₁ hne.symm h
        have hnc : ¬ Γ.Consumer D e := by
          rintro (h | ⟨y, hy, hy'⟩)
          · rw [hte] at h; cases h
          · rw [hte, Option.some.injEq] at hy
            exact hy'.1 (hy ▸ hDx)
        -- consumers
        have hcons : (Finset.univ.filter fun c => ReflTransGen (Γ.DupStep D) e c ∧ Γ.Consumer D c).card =
            Γ.consCount D e₁ + Γ.consCount D e₂ := by
          unfold consCount
          refine card_filter_or_of_disjoint _ _ _ (fun c => ?_) (fun c h h' => hdisj c h.1 h'.1)
          rw [hsub]
          constructor
          · rintro ⟨rfl | h | h, hc⟩
            · exact (hnc hc).elim
            · exact Or.inl ⟨h, hc⟩
            · exact Or.inr ⟨h, hc⟩
          · rintro (⟨h, hc⟩ | ⟨h, hc⟩)
            · exact ⟨Or.inr (Or.inl h), hc⟩
            · exact ⟨Or.inr (Or.inr h), hc⟩
        -- duplicates
        have hins : Γ.ins x = [e] := by
          obtain ⟨g, hg⟩ := hD x hDx
          have : e ∈ Γ.ins x := (Γ.mem_ins x e).2 hte
          rw [hg, List.mem_singleton] at this
          rw [hg, this]
        have hbin : (Finset.univ.filter fun y =>
            D y ∧ ¬ Γ.QuasiTerminal D y ∧ ∃ f ∈ Γ.ins y, ReflTransGen (Γ.DupStep D) e f).card =
            (if ¬ Γ.QuasiTerminal D x then 1 else 0) + (Γ.binCount D e₁ + Γ.binCount D e₂) := by
          unfold binCount
          rw [card_filter_or_of_disjoint _ (fun y => y = x ∧ ¬ Γ.QuasiTerminal D x)
            (fun y => (D y ∧ ¬ Γ.QuasiTerminal D y ∧ ∃ f ∈ Γ.ins y, ReflTransGen (Γ.DupStep D) e₁ f) ∨
              (D y ∧ ¬ Γ.QuasiTerminal D y ∧ ∃ f ∈ Γ.ins y, ReflTransGen (Γ.DupStep D) e₂ f))]
          · congr 1
            · by_cases h : ¬ Γ.QuasiTerminal D x
              · rw [ite_eq_left h]
                exact card_filter_eq_single _ x (by intro y; exact ⟨fun h' => h'.1, fun h' => ⟨h', h⟩⟩)
              · rw [ite_eq_right h]
                exact card_filter_eq_zero _ (by intro y h'; exact h h'.2)
            · refine card_filter_or_of_disjoint _ _ _ (fun _ => Iff.rfl) ?_
              rintro y ⟨hy, -, f, hf, h₁⟩ ⟨-, -, f', hf', h₂⟩
              obtain ⟨g, hg⟩ := hD y hy
              rw [hg, List.mem_singleton] at hf hf'
              subst hf hf'
              exact hdisj _ h₁ h₂
          · intro y
            constructor
            · rintro ⟨hy, hq, f, hf, h⟩
              rcases (hsub f).1 h with rfl | h | h
              · left
                have : Γ.tgt f = some y := (Γ.mem_ins y f).1 hf
                rw [hte, Option.some.injEq] at this
                subst this
                exact ⟨rfl, hq⟩
              · exact Or.inr (Or.inl ⟨hy, hq, f, hf, h⟩)
              · exact Or.inr (Or.inr ⟨hy, hq, f, hf, h⟩)
            · rintro (⟨rfl, hq⟩ | ⟨hy, hq, f, hf, h⟩ | ⟨hy, hq, f, hf, h⟩)
              · exact ⟨hDx, hq, e, by rw [hins]; simp, ReflTransGen.refl⟩
              · exact ⟨hy, hq, f, hf, ReflTransGen.head hst₁ h⟩
              · exact ⟨hy, hq, f, hf, ReflTransGen.head hst₂ h⟩
          · rintro y ⟨rfl, -⟩ (⟨-, -, f, hf, h⟩ | ⟨-, -, f, hf, h⟩)
            · rw [hins, List.mem_singleton] at hf
              subst hf
              exact hnot₁ _ h rfl
            · rw [hins, List.mem_singleton] at hf
              subst hf
              exact hnot₂ _ h rfl
        rw [hcons, hbin]
        have ih₁ := ih e₁ (TransGen.single hst₁.step)
        have ih₂ := ih e₂ (TransGen.single hst₂.step)
        have hu : Γ.Useful D e ↔ Γ.Useful D e₁ ∨ Γ.Useful D e₂ := by
          constructor
          · rintro ⟨c, hc, hc'⟩
            rcases (hsub c).1 hc with rfl | h | h
            · exact (hnc hc').elim
            · exact Or.inl ⟨c, h, hc'⟩
            · exact Or.inr ⟨c, h, hc'⟩
          · rintro (⟨c, h, hc⟩ | ⟨c, h, hc⟩)
            · exact ⟨c, ReflTransGen.head hst₁ h, hc⟩
            · exact ⟨c, ReflTransGen.head hst₂ h, hc⟩
        have hq : ¬ Γ.QuasiTerminal D x ↔ Γ.Useful D e₁ ∧ Γ.Useful D e₂ := by
          rw [not_quasiTerminal_dup_iff hDx, hx, useful_iff_reachCod, useful_iff_reachCod]
          simp
        rw [← ih₁, ← ih₂]
        by_cases h₁ : Γ.Useful D e₁ <;> by_cases h₂ : Γ.Useful D e₂ <;>
          simp [h₁, h₂, hu, hq] <;> omega
      · have hns : ∀ e', ¬ Γ.DupStep D e e' := by
          rintro e' ⟨y, hy, hy', -⟩
          rw [hte, Option.some.injEq] at hy'
          exact hDx (hy' ▸ hy)
        rw [card_filter_eq_zero _ (fun y ⟨hy, _, f, hf, hef⟩ => by
          have := reflTransGen_dup_of_not_step hns hef
          subst this
          rw [(Γ.mem_ins y f).1 hf, Option.some.injEq] at hte
          exact hDx (hte ▸ hy))]
        by_cases hc : Γ.Consumer D e
        · rw [card_filter_eq_single _ e (fun c => ⟨fun h => reflTransGen_dup_of_not_step hns h.1,
            fun h => by subst h; exact ⟨ReflTransGen.refl, hc⟩⟩), ite_eq_left ⟨e, ReflTransGen.refl, hc⟩]
        · rw [card_filter_eq_zero _ (by intro c h; exact hc (reflTransGen_dup_of_not_step hns h.1 ▸ h.2)),
            ite_eq_right (fun ⟨c, h, h'⟩ => hc (reflTransGen_dup_of_not_step hns h ▸ h'))]

end PGraph

end FreeMarkov
