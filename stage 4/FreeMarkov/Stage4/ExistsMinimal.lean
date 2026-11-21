/-
Free Markov categories, Stage 4: the first claim of Lemma 4.4, "every `S_M`-congruence class
contains a Markov minimal diagram".
-/
module

public import FreeMarkov.Stage4.Minimal

@[expose] public section

universe w v u₁ u₂

namespace FreeMarkov

open Relation

namespace FreeDDGraphMonoid

variable {S : Type w} (G : FreeDDGraphMonoid.{w, v} S)

theorem base_mem_markovTemplates {τ : Template.{0} G.toFreeGraphMonoid}
    (h : τ ∈ G.baseMarkovTemplates) : τ ∈ G.markovTemplates :=
  Or.inr (Or.inl h)

theorem coassT_mem (a : S) : G.coassT a ∈ G.markovTemplates :=
  G.base_mem_markovTemplates (Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩))))

theorem counitT_mem (a : S) : G.counitT a ∈ G.markovTemplates :=
  G.base_mem_markovTemplates (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩))))

theorem counitT'_mem (a : S) : G.counitT' a ∈ G.markovTemplates :=
  G.base_mem_markovTemplates (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩)))

theorem cocommT_mem (a : S) : G.cocommT a ∈ G.markovTemplates :=
  G.base_mem_markovTemplates (Or.inl (Or.inr ⟨a, rfl⟩))

theorem natT_mem (f : G.A) : G.natT f ∈ G.markovTemplates :=
  G.base_mem_markovTemplates (Or.inr ⟨f, rfl⟩)

end FreeDDGraphMonoid

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S}
  {NX : Type u₁} {EX : Type u₂} {X : Diagram G.toFreeGraphMonoid NX EX}

theorem counitΩD_noLoose (a : S) (d) :
    (G.counitΩD a).src d ≠ none ∨ (G.counitΩD a).tgt d ≠ none := by
  unfold FreeDDGraphMonoid.counitΩD
  exact oneNode_glue_noLoose _ _ _ d

theorem counitΩ'D_noLoose (a : S) (d) :
    (G.counitΩ'D a).src d ≠ none ∨ (G.counitΩ'D a).tgt d ≠ none := by
  unfold FreeDDGraphMonoid.counitΩ'D
  exact oneNode_glue_noLoose _ _ _ d

theorem natΩD_noLoose (f : G.A) (d) :
    (G.natΩD f).src d ≠ none ∨ (G.natΩD f).tgt d ≠ none := by
  unfold FreeDDGraphMonoid.natΩD
  exact oneNode_glue_noLoose _ _ _ d

theorem wellFounded_lt_flip [Finite NX] : WellFounded fun a b : NX => X.Lt b a := by
  have : IsTrans NX fun a b : NX => X.Lt b a := ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩
  have : Std.Irrefl fun a b : NX => X.Lt b a := ⟨fun a h => X.lt_irrefl a h⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- **A Markov surgery reducing the number of nodes that are not discards** (proof of
Lemma 4.4, first claim). -/
theorem exists_tStep_of_not_minimal [Finite NX] [Finite EX] (hX : ¬ X.MarkovMinimal) :
    ∃ (NY : Type u₁) (EY : Type u₂) (Y : Diagram G.toFreeGraphMonoid NY EY), Finite NY ∧ Finite EY ∧
      TStep G.markovTemplates X Y ∧ Y.ndCount < X.ndCount := by
  obtain ⟨x0, hx0⟩ : ∃ x, X.QuasiTerminal x ∧ ¬ X.val.IsDisc x := by
    unfold MarkovMinimal at hX
    push Not at hX
    exact hX
  obtain ⟨x, ⟨hxq, hxd⟩, hmax⟩ :=
    wellFounded_lt_flip.has_min {x | X.QuasiTerminal x ∧ ¬ X.val.IsDisc x} ⟨x0, hx0⟩
  -- an output of `x` that does not reach the codomain ends at a discard
  have tgt_disc : ∀ e ∈ X.outs x, ¬ X.ReachCod e → ∃ y, X.tgt e = some y ∧ X.val.IsDisc y := by
    intro e he hnr
    cases hte : X.tgt e with
    | none => exact (hnr (PGraph.reachCod_of_tgt_none hte)).elim
    | some y =>
      refine ⟨y, rfl, ?_⟩
      by_contra hyd
      refine hmax y ⟨Or.inl fun e' he' hr => hnr (hr.of_step ⟨y, hte, (X.mem_outs y e').1 he'⟩), hyd⟩
        (X.lt_of_edge ((X.mem_outs x e).1 he) hte)
  -- the input of such a discard
  have disc_ins : ∀ e ∈ X.outs x, ∀ y, X.tgt e = some y → X.val.IsDisc y →
      X.ins y = [e] ∧ X.val.v₁ y = G.disc (X.val.v₀ e) := by
    rintro e - y hy ⟨b, hb⟩
    obtain ⟨g, hg, hgb⟩ := X.val.ins_eq_of_disc hb
    have : e ∈ X.ins y := (X.mem_ins y e).2 hy
    rw [hg, List.mem_singleton] at this
    subst this
    exact ⟨hg, by rw [hb, hgb]⟩
  by_cases hD : X.val.IsDup x
  · obtain ⟨a, ha⟩ := hD
    obtain ⟨e₀, e₁, hxo, h₀, h₁⟩ := X.val.outs_eq_of_t_dup ha
    obtain ⟨e, he, hnr⟩ : ∃ e ∈ X.outs x, ¬ X.ReachCod e := by
      rcases hxq with h | ⟨-, h⟩
      · exact ⟨e₀, by rw [hxo]; simp, h e₀ (by rw [hxo]; simp)⟩
      · exact h
    obtain ⟨y, hy, hyd⟩ := tgt_disc e he hnr
    obtain ⟨hyi, hyv⟩ := disc_ins e he y hy hyd
    rw [hxo] at he
    rcases List.mem_pair.1 he with rfl | rfl
    · -- the first output ends at a discard: right counitality
      rw [h₀] at hyv
      let pe := counitEmb' ha hyv hxo hyi
      have hA : X.IsNormal (rangeSub pe.ιN pe.ιE) := by
        refine pe.toEmb.isNormal_of_root (.inl ()) ?_ ?_ (counitΩ'D_noLoose a)
        · rintro (z | (z | z))
          · exact Or.inr rfl
          · exact Or.inl (X.lt_of_edge ((X.mem_outs x e).1 (by rw [hxo]; simp)) hy)
          · exact z.elim
        · rintro (z | (z | z)) hz f hf
          · exact (hz rfl).elim
          · change f ∈ X.ins y at hf
            rw [hyi, List.mem_singleton] at hf
            subst hf
            exact ⟨.inl (), (X.mem_outs x _).1 (by rw [hxo]; simp)⟩
          · exact z.elim
      obtain ⟨NY, EY, Y, hst, ⟨P⟩⟩ := pe.toEmb.tStep (G.counitT'_mem a) hA
      obtain ⟨hNY, hEY⟩ := finite_of_canonProj P
      exact ⟨NY, EY, Y, hNY, hEY, hst, ndCount_lt P (fun z => z.elim) (.inl ())
        (fun hd => (X.val.not_isDup_of_isDisc hd) ⟨a, ha⟩)⟩
    · -- the second output ends at a discard
      rw [h₁] at hyv
      let pe := counitEmb ha hyv hxo hyi
      have hA : X.IsNormal (rangeSub pe.ιN pe.ιE) := by
        refine pe.toEmb.isNormal_of_root (.inl ()) ?_ ?_ (counitΩD_noLoose a)
        · rintro (z | (z | z))
          · exact Or.inr rfl
          · exact z.elim
          · exact Or.inl (X.lt_of_edge ((X.mem_outs x e).1 (by rw [hxo]; simp)) hy)
        · rintro (z | (z | z)) hz f hf
          · exact (hz rfl).elim
          · exact z.elim
          · change f ∈ X.ins y at hf
            rw [hyi, List.mem_singleton] at hf
            subst hf
            exact ⟨.inl (), (X.mem_outs x _).1 (by rw [hxo]; simp)⟩
      obtain ⟨NY, EY, Y, hst, ⟨P⟩⟩ := pe.toEmb.tStep (G.counitT_mem a) hA
      obtain ⟨hNY, hEY⟩ := finite_of_canonProj P
      exact ⟨NY, EY, Y, hNY, hEY, hst, ndCount_lt P (fun z => z.elim) (.inl ())
        (fun hd => (X.val.not_isDup_of_isDisc hd) ⟨a, ha⟩)⟩
  · -- not a duplicate: every output ends at a discard
    have hall : ∀ e ∈ X.outs x, ¬ X.ReachCod e := by
      rcases hxq with h | ⟨h, -⟩
      · exact h
      · exact (hD h).elim
    let g : {e // e ∈ X.outs x} → NX := fun e => (tgt_disc e.1 e.2 (hall e.1 e.2)).choose
    have hg : ∀ e, X.tgt e.1 = some (g e) ∧ X.val.IsDisc (g e) := fun e =>
      (tgt_disc e.1 e.2 (hall e.1 e.2)).choose_spec
    have hgi : ∀ e, X.ins (g e) = [e.1] ∧ X.val.v₁ (g e) = G.disc (X.val.v₀ e.1) := fun e =>
      disc_ins e.1 e.2 (g e) (hg e).1 (hg e).2
    let ys := (X.outs x).attach.map g
    have hlen : ys.length = (X.outs x).length := by simp [ys]
    have hys : ∀ (k : ℕ) (hk : k < ys.length),
        ys[k] = g ⟨(X.outs x)[k]'(by omega), List.getElem_mem _⟩ := by
      intro k hk
      simp [ys]
    have hyn : ys.Nodup := by
      refine (List.nodup_attach.2 (X.outs_nodup x)).map fun e e' h => Subtype.ext ?_
      have h₁ := (hgi e).1
      rw [h, (hgi e').1, List.cons.injEq] at h₁
      exact h₁.1.symm
    have hlen' : ys.length = (FreeMonoid.toList (G.t (X.val.v₁ x))).length := by
      rw [hlen, length_outs_eq]
    obtain ⟨pe, hpx, hpys⟩ := natEmb (f := X.val.v₁ x) rfl ys hlen' hyn
      (fun k hk => by
        rw [hys k (by omega), (hgi _).2]
        congr 1
        exact v₀_outs_eq X x k _ hk)
      (fun k hk => by rw [hys k (by omega), (hgi _).1])
      (fun hx => by
        obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
        rw [hys k hk] at hkx
        exact hxd (hkx ▸ (hg _).2))
    have hmem : ∀ z, ∃ (k : ℕ) (hk : k < (X.outs x).length),
        pe.ιN (.inr z) = g ⟨(X.outs x)[k], List.getElem_mem _⟩ := by
      intro z
      obtain ⟨k, hk, hkz⟩ := List.getElem_of_mem (hpys z)
      exact ⟨k, by omega, by rw [← hkz, hys k hk]⟩
    have hA : X.IsNormal (rangeSub pe.ιN pe.ιE) := by
      refine pe.toEmb.isNormal_of_root (.inl ()) ?_ ?_ (natΩD_noLoose _)
      · rintro (z | z)
        · exact Or.inr rfl
        · obtain ⟨k, hk, hkz⟩ := hmem z
          rw [hpx, hkz]
          exact Or.inl (X.lt_of_edge ((X.mem_outs x (X.outs x)[k]).1 (List.getElem_mem hk))
            (hg ⟨(X.outs x)[k], List.getElem_mem hk⟩).1)
      · rintro (z | z) hz f hf
        · exact (hz rfl).elim
        · obtain ⟨k, hk, hkz⟩ := hmem z
          change f ∈ X.ins (pe.ιN (.inr z)) at hf
          rw [hkz, (hgi _).1, List.mem_singleton] at hf
          subst hf
          exact ⟨.inl (), by rw [hpx]; exact (X.mem_outs x _).1 (List.getElem_mem _)⟩
    obtain ⟨NY, EY, Y, hst, ⟨P⟩⟩ := pe.toEmb.tStep (G.natT_mem (X.val.v₁ x)) hA
    obtain ⟨hNY, hEY⟩ := finite_of_canonProj P
    exact ⟨NY, EY, Y, hNY, hEY, hst, ndCount_lt P (FreeDDGraphMonoidAux.discListD_isDisc _)
      (.inl ()) (by rw [hpx]; exact hxd)⟩

/-- Every diagram is `S_M`-equivalent, through a chain of Markov surgeries, to a Markov minimal
one. -/
theorem exists_minimal_tEquiv (X : FinDiag G.toFreeGraphMonoid) :
    ∃ Υ : FinDiag G.toFreeGraphMonoid, Υ.2.MarkovMinimal ∧ TEquiv G.markovTemplates X Υ := by
  induction h : X.2.ndCount using Nat.strong_induction_on generalizing X with
  | _ k ih =>
    by_cases hm : X.2.MarkovMinimal
    · exact ⟨X, hm, ReflTransGen.refl⟩
    · obtain ⟨NY, EY, Y, hNY, hEY, hst, hlt⟩ := exists_tStep_of_not_minimal hm
      let Y' : FinDiag G.toFreeGraphMonoid := ⟨(Nat.card NY, Nat.card EY), Y.toFin⟩
      obtain ⟨Υ, hΥ, hYΥ⟩ := ih _ (by rw [← h, ← ndCount_iso Y.isoToFin]; exact hlt) Y' rfl
      exact ⟨Υ, hΥ, ReflTransGen.head (hst.iso_right Y.isoToFin) hYΥ⟩

/-- **Lemma 4.4, first claim.** "Every `S_M`-congruence class contains a Markov minimal
diagram." -/
theorem lemma_4_4_exists_minimal (c : DClass G.toFreeGraphMonoid) :
    ∃ (n m : ℕ) (Υ : Diagram G.toFreeGraphMonoid (Fin n) (Fin m)), Υ.MarkovMinimal ∧
      SRel G.markovTemplates c (DClass.mk Υ) := by
  obtain ⟨X, rfl⟩ := Quotient.exists_rep c
  obtain ⟨Υ, hΥ, hXΥ⟩ := exists_minimal_tEquiv X
  exact ⟨_, _, Υ.2, hΥ, X, Υ, rfl, DClass.mk_fin Υ, hXΥ⟩

end Diagram

end FreeMarkov
