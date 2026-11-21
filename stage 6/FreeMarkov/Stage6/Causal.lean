/-
Free Markov categories, Stage 6: causal effects in `Cau(G)` (Definition 6.3).

For `J : G.JS` (so `J.FsM = Cau(G)`):

* `causalEffectSets J S T = [v_T ‖ v_S]`: the `(V, K)`-effect of `v_S` on `v_T` in `Cau(G)`
  (Definition 5.4 for the family `K_G`); it is Stage 5's `EffSig.freeEffect`.
* `singular_unique`: for a singular variable `v` there are a unique `S` and a unique ordering
  (permutation `ρ` of `S`, given by the list of the elements of `S` in the order `ρ(s_1), …`) with
  `v = v_{ρ(S)}`.
* `causalEffect J v w = [w ‖ v] = τ_* ∘ [v_T ‖ v_S] ∘ ρ_*⁻¹ : v → w` for singular `v`, `w`;
  `prior J w = [w]`, the case `v = ∅`.
* `causalEffect_finWord`: for `v = v_S`, `w = v_T` the twist is `[v_T ‖ v_S]` itself.
* `twist_isMultiplier`, `multiplier_unique`: "since the atomic variables are pairwise distinct letters,
  `τ_*` and `ρ_*` are the multipliers `ι_{v_T → w}` and `ι_{v_S → v}` of Remark 5.3": the symmetry
  `τ_*` is a multiplier on the letters of its domain, and it is the only one with its domain and
  codomain.

The cited result C1 enters through `J`.
-/
module

public import FreeMarkov.Stage6.Coherence

@[expose] public section

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov JoyalStreet

namespace FinODAG

variable {G : FinODAG} (J : G.JS)

/-- *Definition 6.3.* The **causal effect** of `v_S` on `v_T` in `Cau(G)`: the `(V, K)`-effect
`[v_T ‖ v_S]` for the family `K_G` of the pairs `(S_i, κ_{v_i})` (Definition 5.4). -/
noncomputable abbrev causalEffectSets (S T : Finset (Fin G.n)) :
    J.wordM (finWord S) ⟶ J.wordM (finWord T) :=
  EffSig.freeEffect J S T

/-- The set `S` of the atomic variables of a variable `v`. -/
noncomputable def letterSet {n : ℕ} (v : FreeMonoid (Fin n)) : Finset (Fin n) :=
  (FreeMonoid.toList v).toFinset

theorem mem_letterSet {n : ℕ} {v : FreeMonoid (Fin n)} {i : Fin n} :
    i ∈ letterSet v ↔ i ∈ FreeMonoid.toList v := List.mem_toFinset

theorem sort_perm_of_singular {n : ℕ} {v : FreeMonoid (Fin n)} (hv : Singular v) :
    ((letterSet v).sort (· ≤ ·)).Perm (FreeMonoid.toList v) :=
  List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _) hv (by
    rw [Finset.sort_toFinset]; rfl)

/-- *Definition 6.3.* "If `v` is a singular variable then there are unique `S` and a unique
permutation `ρ` of `S` such that `v = v_{ρ(S)}`": the permutation is the list of the elements of `S`
in the order `ρ(s_1), …, ρ(s_k)` (Stage 5, twists), so the pair is unique. -/
theorem singular_unique {n : ℕ} {v : FreeMonoid (Fin n)} (hv : Singular v) :
    ∃! p : Finset (Fin n) × List (Fin n), p.2.Perm (p.1.sort (· ≤ ·)) ∧ FreeMonoid.ofList p.2 = v := by
  refine ⟨(letterSet v, FreeMonoid.toList v), ⟨(sort_perm_of_singular hv).symm, rfl⟩, ?_⟩
  rintro ⟨S, l⟩ ⟨hp, rfl⟩
  simp only [Prod.mk.injEq]
  refine ⟨?_, rfl⟩
  ext i
  rw [mem_letterSet, ← Finset.mem_sort (· ≤ ·)]
  exact hp.mem_iff.symm

theorem eWord {G : FinODAG} (J : G.JS) (v : FreeMonoid (Fin G.n)) :
    J.wordM v = J.projM.obj (Fs.of J (FreeMonoid.ofList (FreeMonoid.toList v))) := rfl

/-- `ρ_*⁻¹ : v → v_S`, the node-free diagram connecting each atomic variable of `v` with the same
atomic variable of `v_S`. -/
noncomputable def twistIn (v : FreeMonoid (Fin G.n)) (hv : Singular v) :
    J.wordM v ⟶ J.wordM (finWord (letterSet v)) :=
  eqToHom (eWord J v) ≫
    J.projM.map (permFs J (FreeMonoid.toList v) ((letterSet v).sort (· ≤ ·)) hv
      (sort_perm_of_singular hv))

/-- `τ_* : v_T → w`, the node-free diagram connecting each atomic variable of `v_T` with the same
atomic variable of `w`. -/
noncomputable def twistOut (w : FreeMonoid (Fin G.n)) (hw : Singular w) :
    J.wordM (finWord (letterSet w)) ⟶ J.wordM w :=
  J.projM.map (permFs J ((letterSet w).sort (· ≤ ·)) (FreeMonoid.toList w)
      (Finset.sort_nodup _ _) (sort_perm_of_singular hw).symm) ≫ eqToHom (eWord J w).symm

/-- *Definition 6.3.* The **causal effect** of the singular variable `v` on the singular variable
`w`: the twist `[w ‖ v] = τ_* ∘ [v_T ‖ v_S] ∘ ρ_*⁻¹ : v → w`, where `v = v_{ρ(S)}`, `w = v_{τ(T)}`. -/
noncomputable def causalEffect (v w : FreeMonoid (Fin G.n)) (hv : Singular v) (hw : Singular w) :
    J.wordM v ⟶ J.wordM w :=
  twistIn J v hv ≫ causalEffectSets J (letterSet v) (letterSet w) ≫ twistOut J w hw

/-- *Definition 6.3.* The **prior** `[w]` on a singular variable `w`: the causal effect of `∅` on
`w`. -/
noncomputable def prior (w : FreeMonoid (Fin G.n)) (hw : Singular w) : J.wordM 1 ⟶ J.wordM w :=
  causalEffect J 1 w singular_one hw

theorem letterSet_finWord (S : Finset (Fin G.n)) : letterSet (finWord S) = S := by
  ext i; rw [mem_letterSet, mem_finWord]

theorem card_permFs_zero {l l' : List (Fin G.n)} (hl : l.Nodup) (hp : l'.Perm l) (p : Fin G.n) :
    J.card (.mech p) (permFs J l l' hl hp) = 0 :=
  card_permFs (J := J) p l l' hl hp

/-- For `v = v_S`, `w = v_T` the twists are identities and `[w ‖ v] = [v_T ‖ v_S]`. -/
theorem causalEffect_finWord (S T : Finset (Fin G.n)) :
    Arrow.mk (causalEffect J (finWord S) (finWord T) (singular_finWord S) (singular_finWord T)) =
      Arrow.mk (causalEffectSets J S T) := by
  have h₁ : Arrow.mk (J.projM.map (permFs J (FreeMonoid.toList (finWord S))
      ((letterSet (finWord S)).sort (· ≤ ·)) (singular_finWord S)
      (sort_perm_of_singular (singular_finWord S)))) =
      Arrow.mk (J.projM.map (𝟙 (Fs.of J (finWord S)))) :=
    ProdSig.arrow_projM_eq_of_card_zero (Q := G.K.sig) (J := J) (singular_finWord S) (FreeMonoid.ofList_toList _)
      (by rw [letterSet_finWord]; rfl) (card_permFs_zero J _ _) (fun p => card_id _ _)
  have h₂ : Arrow.mk (J.projM.map (permFs J ((letterSet (finWord T)).sort (· ≤ ·))
      (FreeMonoid.toList (finWord T)) (Finset.sort_nodup _ _)
      (sort_perm_of_singular (singular_finWord T)).symm)) =
      Arrow.mk (J.projM.map (𝟙 (Fs.of J (finWord T)))) :=
    ProdSig.arrow_projM_eq_of_card_zero (Q := G.K.sig) (J := J) (finWord_nodup _)
      (by rw [letterSet_finWord]) (FreeMonoid.ofList_toList _) (card_permFs_zero J _ _) (fun p => card_id _ _)
  rw [CategoryTheory.Functor.map_id] at h₁ h₂
  have h₃ : Arrow.mk (causalEffectSets J (letterSet (finWord S)) (letterSet (finWord T))) =
      Arrow.mk (causalEffectSets J S T) := by
    rw [letterSet_finWord, letterSet_finWord]
  have hA : Arrow.mk (twistIn J (finWord S) (singular_finWord S)) =
      Arrow.mk (𝟙 (J.wordM (finWord S))) := by
    unfold twistIn
    exact (Arrow.arrow_mk_eqToHom_comp _ _).trans h₁
  have hB : Arrow.mk (twistOut J (finWord T) (singular_finWord T)) =
      Arrow.mk (𝟙 (J.wordM (finWord T))) := by
    unfold twistOut
    exact (Arrow.arrow_mk_comp_eqToHom _ _).trans h₂
  calc Arrow.mk (causalEffect J (finWord S) (finWord T) (singular_finWord S) (singular_finWord T))
      = Arrow.mk (𝟙 _ ≫ causalEffectSets J S T ≫ 𝟙 _) :=
        Arrow.mk_comp_congr hA (Arrow.mk_comp_congr h₃ hB)
    _ = _ := by simp

/-! ### The twists are the multipliers of Remark 5.3 -/

/-- Every multiplier on the letters of a word in `Cau(G)` is the image of a morphism of `F_s(W(G))`
without nodes of causal mechanisms. -/
theorem isMult_lift {W : List (Fin G.n)} {f : Arrow J.FsM}
    (hf : IsMult (W.map fun x => J.wordM (FreeMonoid.of x)) f) :
    ∃ (a b : J.Fs) (g : a ⟶ b), (∀ p, J.card (.mech p) g = 0) ∧ f = Arrow.mk (J.projM.map g) := by
  induction hf with
  | @copy w hw =>
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hw
    exact ⟨_, _, EffSig.dupF J x, fun p => EffSig.card_dupF _ _, (ProdSig.projM_dupF J x).symm⟩
  | @discard w hw =>
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hw
    exact ⟨_, _, EffSig.discF J x, fun p => EffSig.card_discF _ _, congrArg Arrow.mk (eq_discard _).symm⟩
  | @braid w w' _ _ =>
    exact ⟨Fs.of J w * Fs.of J w', Fs.of J w' * Fs.of J w, σ_ (Fs.of J w) (Fs.of J w'),
      fun p => card_braid _ _ _, rfl⟩
  | @id w _ => exact ⟨Fs.of J w, Fs.of J w, 𝟙 (Fs.of J w), fun p => card_id _ _, rfl⟩
  | idOne => exact ⟨(1 : J.Fs), (1 : J.Fs), 𝟙 (1 : J.Fs), fun p => card_id _ _, rfl⟩
  | @comp a b c f g _ _ ihf ihg =>
    obtain ⟨a₁, b₁, f₁, hf₁, ef⟩ := ihf
    obtain ⟨a₂, b₂, g₁, hg₁, eg⟩ := ihg
    have hb : b₁ = a₂ := (Arrow.right_eq_of_mk_eq ef).symm.trans (Arrow.left_eq_of_mk_eq eg)
    subst hb
    refine ⟨a₁, b₂, f₁ ≫ g₁, fun p => by rw [card_comp, hf₁, hg₁], ?_⟩
    rw [Functor.map_comp]
    exact Arrow.mk_comp_congr ef eg
  | @tensor a b c d f g _ _ ihf ihg =>
    obtain ⟨a₁, b₁, f₁, hf₁, ef⟩ := ihf
    obtain ⟨a₂, b₂, g₁, hg₁, eg⟩ := ihg
    refine ⟨a₁ * a₂, b₁ * b₂, f₁ ⊗ₛ g₁, fun p => by rw [card_tensor, hf₁, hg₁], ?_⟩
    exact mk_tensorHom_congr ef eg

theorem prod_map_wordM : ∀ l : List (Fin G.n),
    (l.map fun x => J.wordM (FreeMonoid.of x)).prod = J.wordM (FreeMonoid.ofList l)
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.prod_cons, prod_map_wordM l]; rfl

/-- *Definition 6.3.* "Since the atomic variables are pairwise distinct letters, `τ_*` and `ρ_*` are
the multipliers `ι` of Remark 5.3", uniqueness part: in `Cau(G)` any two multipliers on the letters
of a singular word `w`, with the same codomain, are equal. -/
theorem multiplier_unique {l : List (Fin G.n)} (hl : l.Nodup) {f g : Arrow J.FsM}
    (hf : IsMult (l.map fun x => J.wordM (FreeMonoid.of x)) f)
    (hg : IsMult (l.map fun x => J.wordM (FreeMonoid.of x)) g)
    (hfl : f.left = J.wordM (FreeMonoid.ofList l)) (hgl : g.left = J.wordM (FreeMonoid.ofList l))
    (hr : f.right = g.right) : f = g := by
  obtain ⟨a, b, f', hf', rfl⟩ := isMult_lift J hf
  obtain ⟨a', b', g', hg', rfl⟩ := isMult_lift J hg
  exact ProdSig.arrow_projM_eq_of_card_zero (Q := G.K.sig) (a := a) (b := b) (a' := a') (b' := b')
    (by change (FreeMonoid.toList a).Nodup; rw [show a = FreeMonoid.ofList l from hfl]; exact hl)
    (hfl.trans hgl.symm) hr hf' hg'

/-- *Definition 6.3*, existence part: the twist `τ_*` (a node-free diagram) is a multiplier on the
letters of its domain. -/
theorem twist_isMultiplier {l l' : List (Fin G.n)} (hl : l.Nodup) (hp : l'.Perm l) :
    IsMult (l.map fun x => J.wordM (FreeMonoid.of x))
      (Arrow.mk (J.projM.map (permFs J l l' hl hp))) := by
  have hv : ∀ y ∈ l', y ∈ l := fun y hy => hp.mem_iff.1 hy
  obtain ⟨f, hf⟩ := exists_multiplier (l.map fun x => J.wordM (FreeMonoid.of x))
    (v := J.wordM (FreeMonoid.ofList l'))
    ⟨l'.map fun x => J.wordM (FreeMonoid.of x), fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
        exact List.mem_map_of_mem (hv x hx), prod_map_wordM J l'⟩
  obtain ⟨a, b, f', hf', ef⟩ := isMult_lift J hf
  have ha : J.wordM (FreeMonoid.ofList l) = a :=
    (prod_map_wordM J l).symm.trans (Arrow.left_eq_of_mk_eq ef)
  have hb : J.wordM (FreeMonoid.ofList l') = b := Arrow.right_eq_of_mk_eq ef
  have e : Arrow.mk (J.projM.map (permFs J l l' hl hp)) = Arrow.mk f :=
    (ProdSig.arrow_projM_eq_of_card_zero (Q := G.K.sig) hl ha hb (card_permFs_zero J hl hp) hf').trans
      ef.symm
  rw [e]
  exact hf

end FinODAG

end FreeMarkov
