/-
Free Markov categories, Stage 4: the swap is a surgery with (4.3), the rotation a surgery with
(4.1) (`tStep_swap`, `tStep_rotate`).
-/
module

public import FreeMarkov.Stage4.RewireStep

@[expose] public section

universe u w v u₁ u₂

namespace FreeMarkov

open Relation

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}
  {X : Diagram G.toFreeGraphMonoid N E}

theorem cocommΩD_noLoose (a : S) (d) :
    (G.cocommΩD a).src d ≠ none ∨ (G.cocommΩD a).tgt d ≠ none := by
  unfold FreeDDGraphMonoid.cocommΩD
  exact oneNode_glue_noLoose _ _ _ d

theorem coassΩD_noLoose (a : S) (d) :
    (G.coassΩD a).src d ≠ none ∨ (G.coassΩD a).tgt d ≠ none := by
  unfold FreeDDGraphMonoid.coassΩD
  exact oneNode_glue_noLoose _ _ _ d

/-- The position matching of a template built from two diagrams, as a condition on embeddings. -/
theorem matching_emb {NΩ EΩ NΛ EΛ EX : Type*} {Ω : Diagram G.toFreeGraphMonoid NΩ EΩ}
    {Λ : Diagram G.toFreeGraphMonoid NΛ EΛ} (h : Λ.toAGraph.domEnum.list.length = Ω.toAGraph.domEnum.list.length)
    {ιE : EΩ → EX} {κE : EΛ → EX} (hl : Λ.dom.map κE = Ω.dom.map ιE) (l : {l // Λ.IsDom l}) :
    κE l.1 = ιE (Λ.toAGraph.domEnum.matching Ω.toAGraph.domEnum h l).1 :=
  (Enumeration.matching_spec _ _ h κE ιE hl l).symm

theorem matching_emb' {NΩ EΩ NΛ EΛ EX : Type*} {Ω : Diagram G.toFreeGraphMonoid NΩ EΩ}
    {Λ : Diagram G.toFreeGraphMonoid NΛ EΛ} (h : Λ.toAGraph.codEnum.list.length = Ω.toAGraph.codEnum.list.length)
    {ιE : EΩ → EX} {κE : EΛ → EX} (hl : Λ.cod.map κE = Ω.cod.map ιE) (l : {l // Λ.IsCod l}) :
    κE l.1 = ιE (Λ.toAGraph.codEnum.matching Ω.toAGraph.codEnum h l).1 :=
  (Enumeration.matching_spec _ _ h κE ιE hl l).symm

/-! ### The swap -/

namespace SwapData

variable {d : N} (D : SwapData X d)

/-- `Ω` of (4.3) at the duplicate `d`. -/
noncomputable def embΩ : PEmb (G.cocommΩD D.a) X :=
  PEmb.glue' (PEmb.oneNode d D.hd)
    (PEmb.braidD (FreeMonoid.of D.a) (FreeMonoid.of D.a) [D.o₀] [D.o₁] (by simpa using D.ne)
      (by simp [D.v₀_o₀]) (by simp [D.v₀_o₁])) _
    (by rw [PEmb.oneNode_cod, PEmb.braidD_dom, D.houts]; rfl) (fun _ z => z.elim) (fun _ _ z => z.elim)

theorem hd_swap : (X.swap D).val.v₁ d = G.dup D.a := D.hd

/-- `Λ` of (4.3) in the swapped diagram. -/
noncomputable def embΛ : PEmb (G.dupD D.a) (X.swap D) := PEmb.oneNode d D.hd_swap

theorem embΩ_dom : (G.cocommΩD D.a).dom.map D.embΩ.ιE = X.ins d :=
  (PEmb.glue'_dom _ _ _ _ _ _).trans (PEmb.oneNode_dom _ _)

theorem embΩ_cod : (G.cocommΩD D.a).cod.map D.embΩ.ιE = [D.o₁, D.o₀] :=
  (PEmb.glue'_cod _ _ _ _ _ _).trans (PEmb.braidD_cod _ _ _ _ _ _ _)

theorem embΛ_dom : (G.dupD D.a).dom.map D.embΛ.ιE = X.ins d :=
  PEmb.oneNode_dom (X := X.swap D) _ _

theorem embΛ_cod : (G.dupD D.a).cod.map D.embΛ.ιE = [D.o₁, D.o₀] :=
  (PEmb.oneNode_cod (X := X.swap D) _ _).trans (swap.outs_self D)

theorem embΩ_ιN (z) : D.embΩ.ιN z = d := by
  rcases z with z | z
  · rfl
  · exact z.elim

end SwapData

namespace SwapData

variable {d : N} (D : SwapData X d)

theorem normal : X.IsNormal (rangeSub D.embΩ.ιN D.embΩ.ιE) := by
  refine D.embΩ.toEmb.isNormal_of_root (.inl ()) ?_ ?_ (cocommΩD_noLoose D.a)
  · rintro (z | z)
    · exact Or.inr rfl
    · exact z.elim
  · rintro (z | z) h
    · exact (h rfl).elim
    · exact z.elim

theorem hN (x : N) : (∃ z, D.embΩ.ιN z = x) ↔ ∃ z, D.embΛ.ιN z = x := by
  constructor
  · rintro ⟨z, rfl⟩; exact ⟨(), (D.embΩ_ιN z).symm⟩
  · rintro ⟨z, rfl⟩; exact ⟨.inl (), rfl⟩

theorem hinner (e : E) : (∃ δ, (G.cocommΩD D.a).src δ ≠ none ∧ D.embΩ.ιE δ = e) ↔
    ∃ l, (G.dupD D.a).src l ≠ none ∧ D.embΛ.ιE l = e := by
  rw [D.embΩ.exists_inner_iff, D.embΛ.exists_inner_iff]
  constructor
  · rintro ⟨z, hz⟩; exact ⟨(), by rw [D.embΩ_ιN] at hz; exact hz⟩
  · rintro ⟨z, hz⟩; exact ⟨.inl (), hz⟩

/-- The canonical description of the swap as the result of the surgery. -/
noncomputable def canon : CanonProj X (G.cocommT D.a).Ω D.embΩ.ιN D.embΩ.ιE (G.cocommT D.a).α
    (G.cocommT D.a).β (X.swap D) :=
  canonProj_of_rewire D.embΩ.toEmb D.embΛ.toEmb D.hN D.hinner
    (matching_emb _ (by rw [D.embΛ_dom, D.embΩ_dom])) (matching_emb' _ (by rw [D.embΛ_cod, D.embΩ_cod]))
    rfl (fun _ hx => swap.outs_of_ne D fun h => hx (.inl ()) h.symm) rfl rfl rfl (fun _ _ => rfl)

end SwapData

/-- **The swap is a surgery with (4.3).** -/
theorem tStep_swap {T : Set (Template.{0} G.toFreeGraphMonoid)} {d : N} (D : SwapData X d)
    (hT : G.cocommT D.a ∈ T) : TStep T X (X.swap D) := by
  obtain ⟨NY, EY, Y, hst, ⟨P⟩⟩ := D.embΩ.toEmb.tStep hT D.normal
  exact hst.iso_right (P.iso D.canon)

/-! ### The rotation -/

namespace RotData

variable {p d : N} (R : RotData X p d)
include R

theorem hp_rot : (X.rotate R).val.v₁ p = G.dup R.a := R.hp
theorem hd_rot : (X.rotate R).val.v₁ d = G.dup R.a := R.hd

theorem not_src_ins_p {e : E} (he : e ∈ X.ins p) : X.src e ≠ some d := by
  intro h
  have h₁ : e ∈ X.outs d := (X.mem_outs d e).2 h
  exact X.acyclic p ((TransGen.single ⟨R.m, R.src_m, R.tgt_m⟩).tail ⟨e, h, (X.mem_ins p e).1 he⟩)

theorem ne_H_of_ins_p {e : E} (he : e ∈ X.ins p) : e ≠ R.H := by
  rintro rfl
  exact R.not_src_ins_p he R.src_H

theorem ne_A_of_ins_p {e : E} (he : e ∈ X.ins p) : e ≠ R.A := by
  rintro rfl
  exact X.acyclic p (TransGen.single ⟨R.A, R.src_A, (X.mem_ins p _).1 he⟩)

/-- `Ω` of (4.1) at `p`, `d`. -/
noncomputable def embΩ : PEmb (G.coassΩD R.a) X :=
  PEmb.glue' (PEmb.oneNode p R.hp)
    (PEmb.tensor (PEmb.oneNode d R.hd)
      (PEmb.idD (FreeMonoid.of R.a) [R.A] (List.nodup_singleton _) (by simp [R.v₀_A]))
      (fun _ z => z.elim)
      (fun δ δ' h => by
        have h₁ := PEmb.idD_mem (X := X) (FreeMonoid.of R.a) [R.A] (List.nodup_singleton _)
          (by simp [R.v₀_A]) δ'
        rw [List.mem_singleton] at h₁
        rw [h₁] at h
        rcases PEmb.oneNode_mem d R.hd δ with h₂ | h₂
        · rw [R.hid, List.mem_singleton, h] at h₂
          exact R.m_ne_A h₂.symm
        · rw [R.hod, h] at h₂
          rcases List.mem_pair.1 h₂ with h₂ | h₂
          · exact R.H_ne_A h₂.symm
          · exact R.C_ne_A h₂.symm))
    _ (by rw [PEmb.oneNode_cod, PEmb.tensor_dom, PEmb.oneNode_dom, PEmb.idD_dom, R.hop, R.hid]; rfl)
    (by rintro - (z | z); exact R.p_ne_d; exact z.elim)
    (by
      rintro δ - (z | z) h
      · rcases PEmb.oneNode_mem p R.hp δ with h₂ | h₂
        · exact R.not_src_ins_p h₂ h
        · rw [(X.mem_outs p _).1 h₂, Option.some.injEq] at h
          exact R.p_ne_d h
      · exact z.elim)

/-- `Λ` of (4.1) in the rotated diagram. -/
noncomputable def embΛ : PEmb (G.coassΛD R.a) (X.rotate R) :=
  PEmb.glue' (PEmb.oneNode (X := X.rotate R) p R.hp_rot)
    (PEmb.tensor (PEmb.idD (X := X.rotate R) (FreeMonoid.of R.a) [R.H] (List.nodup_singleton _)
        (by simp [rotate, R.v₀_H]))
      (PEmb.oneNode (X := X.rotate R) d R.hd_rot)
      (fun z _ => z.elim)
      (fun δ δ' h => by
        have h₁ := PEmb.idD_mem (X := X.rotate R) (FreeMonoid.of R.a) [R.H] (List.nodup_singleton _)
          (by simp [rotate, R.v₀_H]) δ
        rw [List.mem_singleton] at h₁
        rw [h₁] at h
        rcases PEmb.oneNode_mem (X := X.rotate R) d R.hd_rot δ' with h₂ | h₂
        · change _ ∈ X.ins d at h₂
          rw [R.hid, List.mem_singleton, ← h] at h₂
          exact R.H_ne_m h₂
        · change _ ∈ X.rotOuts R d at h₂
          rw [rotOuts_d, ← h] at h₂
          rcases List.mem_pair.1 h₂ with h₂ | h₂
          · exact R.H_ne_C h₂
          · exact R.H_ne_A h₂))
    _ (by
      rw [PEmb.oneNode_cod, PEmb.tensor_dom, PEmb.oneNode_dom, PEmb.idD_dom]
      change X.rotOuts R p = [R.H] ++ X.ins d
      rw [rotOuts_p, R.hid]; rfl)
    (by rintro - (z | z); exact z.elim; exact R.p_ne_d)
    (by
      rintro δ - (z | z) h
      · exact z.elim
      · rcases PEmb.oneNode_mem (X := X.rotate R) p R.hp_rot δ with h₂ | h₂
        · change _ ∈ X.ins p at h₂
          change X.rotSrc R _ = some d at h
          rw [rotSrc_of_ne R (R.ne_H_of_ins_p h₂) (R.ne_A_of_ins_p h₂)] at h
          exact R.not_src_ins_p h₂ h
        · rw [((X.rotate R).mem_outs p _).1 h₂, Option.some.injEq] at h
          exact R.p_ne_d h)

theorem embΩ_dom : (G.coassΩD R.a).dom.map R.embΩ.ιE = X.ins p :=
  (PEmb.glue'_dom _ _ _ _ _ _).trans (PEmb.oneNode_dom _ _)

theorem embΩ_cod : (G.coassΩD R.a).cod.map R.embΩ.ιE = [R.H, R.C, R.A] := by
  refine (PEmb.glue'_cod _ _ _ _ _ _).trans ?_
  refine (PEmb.tensor_cod _ _ _ _).trans ?_
  rw [PEmb.oneNode_cod, PEmb.idD_cod, R.hod]; rfl

theorem embΛ_dom : (G.coassΛD R.a).dom.map R.embΛ.ιE = X.ins p :=
  (PEmb.glue'_dom _ _ _ _ _ _).trans (PEmb.oneNode_dom (X := X.rotate R) _ _)

theorem embΛ_cod : (G.coassΛD R.a).cod.map R.embΛ.ιE = [R.H, R.C, R.A] := by
  refine (PEmb.glue'_cod _ _ _ _ _ _).trans ?_
  refine (PEmb.tensor_cod _ _ _ _).trans ?_
  rw [PEmb.oneNode_cod, PEmb.idD_cod]
  change [R.H] ++ X.rotOuts R d = _
  rw [rotOuts_d]; rfl

theorem embΩ_ιN_inl (z) : R.embΩ.ιN (.inl z) = p := rfl
theorem embΩ_ιN_inr (z) : R.embΩ.ιN (.inr (.inl z)) = d := rfl
theorem embΛ_ιN_inl (z) : R.embΛ.ιN (.inl z) = p := rfl
theorem embΛ_ιN_inr (z) : R.embΛ.ιN (.inr (.inr z)) = d := rfl

theorem embΩ_range (x : N) : (∃ z, R.embΩ.ιN z = x) ↔ x = p ∨ x = d := by
  constructor
  · rintro ⟨(z | (z | z)), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact z.elim
  · rintro (rfl | rfl)
    · exact ⟨.inl (), rfl⟩
    · exact ⟨.inr (.inl ()), rfl⟩

theorem embΛ_range (x : N) : (∃ z, R.embΛ.ιN z = x) ↔ x = p ∨ x = d := by
  constructor
  · rintro ⟨(z | (z | z)), rfl⟩
    · exact Or.inl rfl
    · exact z.elim
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨.inl (), rfl⟩
    · exact ⟨.inr (.inr ()), rfl⟩

end RotData

namespace RotData

variable {p d : N} (R : RotData X p d)

theorem normal : X.IsNormal (rangeSub R.embΩ.ιN R.embΩ.ιE) := by
  refine R.embΩ.toEmb.isNormal_of_root (.inl ()) ?_ ?_ (coassΩD_noLoose R.a)
  · rintro (z | (z | z))
    · exact Or.inr rfl
    · exact Or.inl (X.lt_of_edge R.src_m R.tgt_m)
    · exact z.elim
  · rintro (z | (z | z)) h e he
    · exact (h rfl).elim
    · change e ∈ X.ins d at he
      rw [R.hid, List.mem_singleton] at he
      subst he
      exact ⟨.inl (), R.src_m⟩
    · exact z.elim

theorem hN (x : N) : (∃ z, R.embΩ.ιN z = x) ↔ ∃ z, R.embΛ.ιN z = x := by
  rw [R.embΩ_range, R.embΛ_range]

theorem hinner (e : E) : (∃ δ, (G.coassΩD R.a).src δ ≠ none ∧ R.embΩ.ιE δ = e) ↔
    ∃ l, (G.coassΛD R.a).src l ≠ none ∧ R.embΛ.ιE l = e := by
  rw [R.embΩ.exists_inner_iff, R.embΛ.exists_inner_iff]
  have h₁ : (∃ z, X.src e = some (R.embΩ.ιN z)) ↔ X.src e = some p ∨ X.src e = some d := by
    constructor
    · rintro ⟨z, hz⟩
      rcases (R.embΩ_range _).1 ⟨z, rfl⟩ with h | h <;> rw [h] at hz
      · exact Or.inl hz
      · exact Or.inr hz
    · rintro (h | h)
      · exact ⟨.inl (), h⟩
      · exact ⟨.inr (.inl ()), h⟩
  have h₂ : (∃ z, (X.rotate R).src e = some (R.embΛ.ιN z)) ↔
      X.rotSrc R e = some p ∨ X.rotSrc R e = some d := by
    constructor
    · rintro ⟨z, hz⟩
      rcases (R.embΛ_range _).1 ⟨z, rfl⟩ with h | h <;> rw [h] at hz
      · exact Or.inl hz
      · exact Or.inr hz
    · rintro (h | h)
      · exact ⟨.inl (), h⟩
      · exact ⟨.inr (.inr ()), h⟩
  rw [h₁, h₂]
  by_cases hH : e = R.H
  · subst hH; simp [rotSrc_H, R.src_H]
  by_cases hA : e = R.A
  · subst hA; simp [rotSrc_A, R.src_A]
  rw [rotSrc_of_ne R hH hA]

/-- The canonical description of the rotation as the result of the surgery. -/
noncomputable def canon : CanonProj X (G.coassT R.a).Ω R.embΩ.ιN R.embΩ.ιE (G.coassT R.a).α
    (G.coassT R.a).β (X.rotate R) :=
  canonProj_of_rewire R.embΩ.toEmb R.embΛ.toEmb R.hN R.hinner
    (matching_emb _ (by rw [R.embΛ_dom, R.embΩ_dom])) (matching_emb' _ (by rw [R.embΛ_cod, R.embΩ_cod]))
    rfl (fun x hx => rotOuts_of_ne R (fun h => hx (.inl ()) h.symm) (fun h => hx (.inr (.inl ())) h.symm))
    rfl rfl rfl (fun _ _ => rfl)

end RotData

/-- **The rotation is a surgery with (4.1).** -/
theorem tStep_rotate {T : Set (Template.{0} G.toFreeGraphMonoid)} {p d : N} (R : RotData X p d)
    (hT : G.coassT R.a ∈ T) : TStep T X (X.rotate R) := by
  obtain ⟨NY, EY, Y, hst, ⟨P⟩⟩ := R.embΩ.toEmb.tStep hT R.normal
  exact hst.iso_right (P.iso R.canon)

end Diagram

end FreeMarkov
