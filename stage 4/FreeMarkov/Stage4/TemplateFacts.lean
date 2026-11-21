/-
Free Markov categories, Stage 4: the Markov templates satisfy the conditions used in the proof
of Lemma 4.3.

"If the template is one of (4.1), (4.2), (4.3), in either direction, then the nodes of `Ω` and
`Λ` are duplicates and discards, so none of them is live, the domain of each of `Ω`, `Λ` is a
single edge, and this edge is the origin, in `Ω` or `Λ`, of every edge in the codomain. ...
If the template is (4.4), in either direction, then the codomains of `Ω` and `Λ` are empty."
-/
module

public import FreeMarkov.Stage4.StepSkeleton

@[expose] public section

universe w v u₁ u₂ u₃ u₄

namespace FreeMarkov

open Relation

namespace PDiagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

/-- All nodes are duplicates or discards. -/
def DupDisc (Ω : PDiagram G.toFreeGraphMonoid N E) : Prop :=
  ∀ z, Ω.val.IsDup z ∨ Ω.val.IsDisc z

/-- The domain is a single edge `b`. -/
def SingleDom (Ω : PDiagram G.toFreeGraphMonoid N E) (b : E) : Prop :=
  ∀ e, Ω.IsDom e ↔ e = b

/-- In a diagram whose nodes are duplicates and discards and whose domain is the single edge
`b`, `b` is the origin of every edge ("this edge is the origin ... of every edge"). -/
theorem chain_of_dupDisc [Finite E] {Ω : PDiagram G.toFreeGraphMonoid N E} (hΩ : Ω.DupDisc) {b : E}
    (hb : Ω.SingleDom b) (e : E) : ReflTransGen (Ω.DupStep Ω.val.IsDup) b e := by
  obtain ⟨q, hq, hr⟩ := PGraph.exists_isOrigin Ω.dupCond e
  cases hqs : Ω.src q with
  | none => rwa [(hb q).1 hqs] at hq
  | some z =>
    rcases hΩ z with h | ⟨a, ha⟩
    · exact (hr z hqs h).elim
    · have := (Ω.mem_outs z q).2 hqs
      rw [Ω.val.outs_eq_nil_of_disc ha] at this
      cases this

variable {N' : Type u₃} {E' : Type u₄}

/-- **Templates (4.1)–(4.3).** -/
theorem stepCond_of_dupDisc [Finite E'] {Ω : PDiagram G.toFreeGraphMonoid N E}
    {Λ : PDiagram G.toFreeGraphMonoid N' E'} (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e})
    (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}) (hΩ : Ω.DupDisc) (hΛ : Λ.DupDisc) {b' : E'}
    (hb' : Λ.SingleDom b') : Diagram.StepCond Ω Λ α β where
  live z := by
    rcases hΩ z with h | ⟨a, ha⟩
    · exact Or.inl h
    · right
      intro d hd
      rw [Ω.val.outs_eq_nil_of_disc ha] at hd
      cases hd
  path b c _ := by
    rw [(hb' _).1 (α.symm b).2]
    exact PGraph.reflTransGen_step_of_dup (chain_of_dupDisc hΛ hb' _)
  chain b c _ := by
    rw [(hb' _).1 (α.symm b).2]
    exact chain_of_dupDisc hΛ hb' _

/-- **Template (4.4).** -/
theorem stepCond_of_noCod {Ω : PDiagram G.toFreeGraphMonoid N E}
    {Λ : PDiagram G.toFreeGraphMonoid N' E'} (α : {e // Λ.IsDom e} ≃ {e // Ω.IsDom e})
    (β : {e // Λ.IsCod e} ≃ {e // Ω.IsCod e}) (hΩ : ∀ e, ¬ Ω.IsCod e) :
    Diagram.StepCond Ω Λ α β where
  live _ := Or.inr fun _ _ ⟨c, _, hc⟩ => hΩ c hc
  path _ c := (hΩ c.1 c.2).elim
  chain _ c := (hΩ c.1 c.2).elim

end PDiagram

namespace Diagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} {N : Type u₁} {E : Type u₂}

theorem singleDom_of_domWord (D : Diagram G.toFreeGraphMonoid N E) {a : S}
    (h : D.domWord = FreeMonoid.of a) : ∃ b, D.toPDiagram.SingleDom b := by
  have h' : D.dom.map D.val.v₀ = [a] := FreeMonoid.ofList.injective h
  obtain ⟨b, hb⟩ : ∃ b, D.dom = [b] := by
    rcases hd : D.dom with _ | ⟨b, _ | ⟨b', l⟩⟩ <;> rw [hd] at h' <;> simp at h'
    exact ⟨b, rfl⟩
  refine ⟨b, fun e => ?_⟩
  show D.src e = none ↔ e = b
  rw [← D.mem_dom, hb, List.mem_singleton]

theorem noCod_of_codWord (D : Diagram G.toFreeGraphMonoid N E) (h : D.codWord = 1) (e : E) :
    ¬ D.toPDiagram.IsCod e := by
  have h' : D.cod.map D.val.v₀ = [] := FreeMonoid.ofList.injective h
  show ¬ D.tgt e = none
  rw [← D.mem_cod, List.map_eq_nil_iff.1 h']
  exact List.not_mem_nil

end Diagram

namespace FreeDDGraphMonoid

variable {S : Type w} (G : FreeDDGraphMonoid.{w, v} S)

open Diagram

theorem coassΩD_dupDisc (a : S) : (G.coassΩD a).toPDiagram.DupDisc := by
  rintro (x | (x | x))
  all_goals first | exact Or.inl ⟨a, rfl⟩ | exact x.elim

theorem coassΛD_dupDisc (a : S) : (G.coassΛD a).toPDiagram.DupDisc := by
  rintro (x | (x | x))
  all_goals first | exact Or.inl ⟨a, rfl⟩ | exact x.elim

theorem counitΩD_dupDisc (a : S) : (G.counitΩD a).toPDiagram.DupDisc := by
  rintro (x | (x | x))
  · exact Or.inl ⟨a, rfl⟩
  · exact x.elim
  · exact Or.inr ⟨a, rfl⟩

theorem counitΩ'D_dupDisc (a : S) : (G.counitΩ'D a).toPDiagram.DupDisc := by
  rintro (x | (x | x))
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨a, rfl⟩
  · exact x.elim

theorem idDa_dupDisc (a : S) : (G.idDa a).toPDiagram.DupDisc := fun x => x.elim

theorem cocommΩD_dupDisc (a : S) : (G.cocommΩD a).toPDiagram.DupDisc := by
  rintro (x | x)
  · exact Or.inl ⟨a, rfl⟩
  · exact x.elim

theorem dupD_dupDisc (a : S) : (G.dupD a).toPDiagram.DupDisc := fun _ => Or.inl ⟨a, rfl⟩

theorem coassΩD_domWord (a : S) : (G.coassΩD a).domWord = FreeMonoid.of a := by
  simp [coassΩD, G.dupD_domWord]

theorem coassΛD_domWord (a : S) : (G.coassΛD a).domWord = FreeMonoid.of a := by
  simp [coassΛD, G.dupD_domWord]

theorem counitΩD_domWord (a : S) : (G.counitΩD a).domWord = FreeMonoid.of a := by
  simp [counitΩD, G.dupD_domWord]

theorem counitΩ'D_domWord (a : S) : (G.counitΩ'D a).domWord = FreeMonoid.of a := by
  simp [counitΩ'D, G.dupD_domWord]

theorem cocommΩD_domWord (a : S) : (G.cocommΩD a).domWord = FreeMonoid.of a := by
  simp [cocommΩD, G.dupD_domWord]

theorem natΩD_codWord (f : G.A) : (G.natΩD f).codWord = 1 := by
  simp [natΩD, discListD_codWord]

/-- **The Markov templates satisfy the conditions of the proof of Lemma 4.3**, in both
directions. -/
theorem markovTemplates_stepCond : ∀ τ ∈ G.markovTemplates, StepCond τ.Ω τ.Λ τ.α τ.β := by
  have base : ∀ τ ∈ G.baseMarkovTemplates,
      StepCond τ.Ω τ.Λ τ.α τ.β ∧ StepCond τ.symm.Ω τ.symm.Λ τ.symm.α τ.symm.β := by
    rintro τ ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨f, rfl⟩)
    · obtain ⟨b, hb⟩ := (G.coassΩD a).singleDom_of_domWord (G.coassΩD_domWord a)
      obtain ⟨b', hb'⟩ := (G.coassΛD a).singleDom_of_domWord (G.coassΛD_domWord a)
      exact ⟨PDiagram.stepCond_of_dupDisc _ _ (G.coassΩD_dupDisc a) (G.coassΛD_dupDisc a) hb',
        PDiagram.stepCond_of_dupDisc _ _ (G.coassΛD_dupDisc a) (G.coassΩD_dupDisc a) hb⟩
    · obtain ⟨b, hb⟩ := (G.counitΩD a).singleDom_of_domWord (G.counitΩD_domWord a)
      obtain ⟨b', hb'⟩ := (G.idDa a).singleDom_of_domWord (idD_domWord _)
      exact ⟨PDiagram.stepCond_of_dupDisc _ _ (G.counitΩD_dupDisc a) (G.idDa_dupDisc a) hb',
        PDiagram.stepCond_of_dupDisc _ _ (G.idDa_dupDisc a) (G.counitΩD_dupDisc a) hb⟩
    · obtain ⟨b, hb⟩ := (G.counitΩ'D a).singleDom_of_domWord (G.counitΩ'D_domWord a)
      obtain ⟨b', hb'⟩ := (G.idDa a).singleDom_of_domWord (idD_domWord _)
      exact ⟨PDiagram.stepCond_of_dupDisc _ _ (G.counitΩ'D_dupDisc a) (G.idDa_dupDisc a) hb',
        PDiagram.stepCond_of_dupDisc _ _ (G.idDa_dupDisc a) (G.counitΩ'D_dupDisc a) hb⟩
    · obtain ⟨b, hb⟩ := (G.cocommΩD a).singleDom_of_domWord (G.cocommΩD_domWord a)
      obtain ⟨b', hb'⟩ := (G.dupD a).singleDom_of_domWord (G.dupD_domWord a)
      exact ⟨PDiagram.stepCond_of_dupDisc _ _ (G.cocommΩD_dupDisc a) (G.dupD_dupDisc a) hb',
        PDiagram.stepCond_of_dupDisc _ _ (G.dupD_dupDisc a) (G.cocommΩD_dupDisc a) hb⟩
    · exact ⟨PDiagram.stepCond_of_noCod _ _ ((G.natΩD f).noCod_of_codWord (G.natΩD_codWord f)),
        PDiagram.stepCond_of_noCod _ _ ((G.natΛD f).noCod_of_codWord (discListD_codWord _ _))⟩
  rintro τ (rfl | hτ | ⟨σ, hσ, rfl⟩)
  · exact PDiagram.stepCond_of_noCod _ _ (fun e => e.elim)
  · exact (base τ hτ).1
  · exact (base σ hσ).2

end FreeDDGraphMonoid

end FreeMarkov
