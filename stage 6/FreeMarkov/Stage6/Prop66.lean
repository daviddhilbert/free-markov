/-
Free Markov categories, Stage 6: **Proposition 6.6**, `φ^*([w ‖ v]) = [φ^*(w) ‖ φ^*(v)]`.

The proof follows the paper.  For `v = v_S`, `w = v_T`: `Γ_{φ^* G}` is the substitution `subst(f)` of
an effect diagram `f` for `(S, T)` in `W(G)` (`Lift.lean`); it represents `φ^*([w ‖ v])`
(`refine_projM`); it has one node `κ_x` for each `x ∈ φ⁻¹(D ∖ S)` (`card_subst` with the note on
`H_{φ⁻¹(pa y) → φ⁻¹(y)}`) and no other node of a causal mechanism; its live nodes are those `κ_x`
with `x ∈ D' ∖ S'` (the paper's path arguments, `liveSet_iff`), and so are those of an effect diagram
`Γ_H` for `(S', T')`; by label coherence (the paper's claim (∗), `ProdSig.projM_eq_of_live`) the two
have the same skeleton and represent the same morphism (Lemma 4.4).  The general case reduces to this
one through the twists, which `φ^*` sends to twists.

The cited result C1 enters through `JG` and `JH`.
-/
module

public import FreeMarkov.Stage6.Causal

@[expose] public section

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov JoyalStreet Relation

namespace FinODAG

/-! ### Graph theory -/

section Graph

variable {n : ℕ} (K : EffSig n)

/-- Connection to the codomain letters through producers satisfying `P`, as directed paths: `ℓ`
reaches `T` by arrows `a → b` (`a` a parent of `b`) with `P b`. -/
theorem liveLab_iff (P : Fin n → Prop) (T : List (Fin n)) (x : Fin n) :
    K.sig.LiveLab P T x ↔ ∃ t ∈ T, ReflTransGen (fun a b => a ∈ K.pa b ∧ P b) x t := by
  constructor
  · intro h
    refine ProdSig.LiveLab.rec
      (motive := fun x _ => ∃ t ∈ T, ReflTransGen (fun a b => a ∈ K.pa b ∧ P b) x t)
      (fun hl => ⟨_, hl, ReflTransGen.refl⟩) (fun {p ℓ} hp _ hℓ ih => ?_) h
    obtain ⟨t, ht, h⟩ := ih
    exact ⟨t, ht, ReflTransGen.head ⟨mem_finWord.1 hℓ, hp⟩ h⟩
  · rintro ⟨t, ht, h⟩
    induction h using ReflTransGen.head_induction_on with
    | refl => exact .cod ht
    | @head a c hac _ ih => exact .step hac.2 ih (mem_finWord.2 hac.1)

variable {K}

/-- From a vertex of `V(G_{S → T}) ∖ S` a directed path through such vertices ends in `T` (as in
"since a directed path leads from it to the codomain", Definition 5.4). -/
theorem path_of_R {S T : Finset (Fin n)} {x : Fin n} (hx : K.R S T x) :
    ∃ t ∈ T, ReflTransGen (fun a b => a ∈ K.pa b ∧ K.R S T b) x t := by
  obtain ⟨hxS, t, ht, h⟩ := hx
  refine ⟨t, ht, ?_⟩
  clear hxS
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ReflTransGen.refl
  | @head a c hac hct ih => exact ReflTransGen.head ⟨hac.1, hac.2, t, ht, hct⟩ ih

end Graph

variable {H G : FinODAG} (φ : H ⟶ G)

/-- *Proposition 6.6, proof.* "Erasing the repetitions in `φ(p_0), …, φ(p_r)` gives a directed path
in `G` that ends in `T` and does not contain any vertex in `S`; so `φ(p_i) ∈ D ∖ S`": a vertex on a
directed path of `H` through vertices outside `S' = φ⁻¹(S)` that ends in `T' = φ⁻¹(T)` is sent into
`V(G_{S → T}) ∖ S`. -/
theorem R_image {S T : Finset (Fin G.n)} {a t : Fin H.n} (ht : t ∈ preimS φ T)
    (h : ReflTransGen (H.K.Avoid (preimS φ S)) a t) (ha : a ∉ preimS φ S) :
    G.K.R S T (φ.onV a) := by
  induction h using ReflTransGen.head_induction_on with
  | refl =>
    exact ⟨fun h' => ha ((mem_preimS φ).2 h'), _, (mem_preimS φ).1 ht, ReflTransGen.refl⟩
  | @head a c hac _ ih =>
    have hc := ih hac.2
    rcases φ.map_pa hac.1 with h' | h'
    · rw [h']; exact hc
    · obtain ⟨hcS, t', ht', hp⟩ := hc
      exact ⟨fun h'' => ha ((mem_preimS φ).2 h''), t', ht', ReflTransGen.head ⟨h', hcS⟩ hp⟩

theorem R_preimS_of {S T : Finset (Fin G.n)} {x t : Fin H.n} (ht : t ∈ preimS φ T)
    (h : ReflTransGen (fun a b => a ∈ H.pa b ∧ G.K.R S T (φ.onV b)) x t)
    (hx : G.K.R S T (φ.onV x)) : H.K.R (preimS φ S) (preimS φ T) x := by
  refine ⟨fun h' => hx.1 ((mem_preimS φ).1 h'), t, ht, ?_⟩
  exact ReflTransGen.mono (fun a b hab => ⟨hab.1, fun h' => hab.2.1 ((mem_preimS φ).1 h')⟩) _ _ h

/-- *Proposition 6.6, proof.* The live nodes of `Γ_{φ^* G}`: a node `k_x` (`x ∈ φ⁻¹(D ∖ S)`) is
connected to the codomain through nodes `k_p` exactly when `x ∈ D' ∖ S'`, and the nodes of `Γ_H` are
the `k_x`, `x ∈ D' ∖ S'`, all of them connected. -/
theorem liveSet_iff (S T : Finset (Fin G.n)) (x : Fin H.n) :
    (G.K.R S T (φ.onV x) ∧ ∃ t ∈ preimS φ T,
        ReflTransGen (fun a b => a ∈ H.pa b ∧ G.K.R S T (φ.onV b)) x t) ↔
      (H.K.R (preimS φ S) (preimS φ T) x ∧ ∃ t ∈ preimS φ T,
        ReflTransGen (fun a b => a ∈ H.pa b ∧ H.K.R (preimS φ S) (preimS φ T) b) x t) := by
  constructor
  · rintro ⟨hx, t, ht, h⟩
    have hR := R_preimS_of φ ht h hx
    exact ⟨hR, path_of_R hR⟩
  · rintro ⟨hR, -⟩
    obtain ⟨hxS, t, ht, h⟩ := hR
    refine ⟨R_image φ ht h hxS, t, ht, ?_⟩
    clear hxS
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ReflTransGen.refl
    | @head a c hac hct ih => exact ReflTransGen.head ⟨hac.1, R_image φ ht hct hac.2⟩ ih

/-! ### Proposition 6.6 for `v = v_S`, `w = v_T` -/

variable (JG : G.JS) (JH : H.JS)

theorem eSubstDom (S : Finset (Fin G.n)) :
    Fs.of JH (finWord (preimS φ S)) = (subst φ JG JH).obj (Fs.of JG (finWord S)) := by
  rw [subst_obj, preimW_finWord]

theorem eSubstCod (S : Finset (Fin G.n)) :
    (subst φ JG JH).obj (Fs.of JG (finWord S)) = Fs.of JH (finWord (preimS φ S)) :=
  (eSubstDom φ JG JH S).symm

/-- The diagram `Γ_{φ^* G}` with its domain and codomain written as `u_{S'}`, `u_{T'}`. -/
noncomputable def substEffect (S T : Finset (Fin G.n))
    (f : Fs.of JG (finWord S) ⟶ Fs.of JG (finWord T)) :
    Fs.of JH (finWord (preimS φ S)) ⟶ Fs.of JH (finWord (preimS φ T)) :=
  eqToHom (eSubstDom φ JG JH S) ≫ (subst φ JG JH).map f ≫ eqToHom (eSubstCod φ JG JH T)

open Classical in
theorem card_substEffect {S T : Finset (Fin G.n)} {f : Fs.of JG (finWord S) ⟶ Fs.of JG (finWord T)}
    (hf : EffSig.IsEffect JG f) (x : Fin H.n) :
    JH.card (.mech x) (substEffect φ JG JH S T f) = if G.K.R S T (φ.onV x) then 1 else 0 := by
  unfold substEffect
  rw [card_comp, card_comp, card_eqToHom, card_eqToHom, card_subst, hf]
  simp

/-- **Proposition 6.6** for `v = v_S` and `w = v_T`:
`φ^*([v_T ‖ v_S]_{(V_G, K_G)}) = [u_{T'} ‖ u_{S'}]_{(V_H, K_H)}` with `S' = φ⁻¹(S)`, `T' = φ⁻¹(T)`. -/
theorem prop_6_6_sets (S T : Finset (Fin G.n)) :
    Arrow.mk ((refine φ JH JG).map (causalEffectSets JG S T)) =
      Arrow.mk (causalEffectSets JH (preimS φ S) (preimS φ T)) := by
  classical
  obtain ⟨f, hf⟩ := EffSig.exists_effect JG S T
  obtain ⟨g, hg⟩ := EffSig.exists_effect JH (preimS φ S) (preimS φ T)
  rw [causalEffectSets, ← EffSig.projM_eq_freeEffect hf, causalEffectSets,
    ← EffSig.projM_eq_freeEffect hg]
  refine (refine_projM φ JG JH f).trans ?_
  have e : Arrow.mk (JH.projM.map ((subst φ JG JH).map f)) =
      Arrow.mk (JH.projM.map (substEffect φ JG JH S T f)) := by
    unfold substEffect
    simp only [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]
  rw [e]
  refine congrArg Arrow.mk (ProdSig.projM_eq_of_live (finWord_nodup _) ?_
    (EffSig.labelOK_of_isEffect hg) fun p => ?_)
  · intro x
    rw [card_substEffect φ JG JH hf x]
    refine ⟨by split_ifs <;> simp, fun h => ?_⟩
    split_ifs at h with hx
    · change x ∉ FreeMonoid.toList (finWord (preimS φ S))
      rw [mem_finWord, mem_preimS]
      exact hx.1
    · exact absurd rfl h
  · have h₁ : (fun q => JH.card (.mech q) (substEffect φ JG JH S T f) ≠ 0) =
        fun q => G.K.R S T (φ.onV q) := by
      funext q; rw [card_substEffect φ JG JH hf q]; split_ifs with h <;> simp [h]
    have h₂ : (fun q => JH.card (.mech q) g ≠ 0) = fun q => H.K.R (preimS φ S) (preimS φ T) q := by
      funext q; rw [hg q]; split_ifs with h <;> simp [h]
    have hT : ∀ t, t ∈ H.K.sig.letters (finWord (preimS φ T)) ↔ t ∈ preimS φ T :=
      fun t => mem_finWord
    have e₁ : JH.card (.mech p) (substEffect φ JG JH S T f) ≠ 0 ↔ G.K.R S T (φ.onV p) :=
      iff_of_eq (congrFun h₁ p)
    have e₂ : JH.card (.mech p) g ≠ 0 ↔ H.K.R (preimS φ S) (preimS φ T) p :=
      iff_of_eq (congrFun h₂ p)
    rw [h₁, h₂, e₁, e₂]
    change (G.K.R S T (φ.onV p) ∧ H.K.sig.LiveLab _ _ p) ↔
      (H.K.R (preimS φ S) (preimS φ T) p ∧ H.K.sig.LiveLab _ _ p)
    rw [liveLab_iff, liveLab_iff]
    simp only [hT]
    exact liveSet_iff φ S T p

/-! ### Proposition 6.6 -/

theorem letterSet_preimW {v : FreeMonoid (Fin G.n)} :
    letterSet (preimW φ v) = preimS φ (letterSet v) := by
  ext x; rw [mem_letterSet, mem_preimW, mem_preimS, mem_letterSet]

/-- `φ^*` sends a twist `τ_*` of `Cau(G)` to the twist of `Cau(H)` between the images: "since `φ^*`
is a strict symmetric monoidal functor, `φ^*(τ_*)` is represented by the diagram without nodes in
which each atomic variable in `φ⁻¹(v_T)` is connected with the same atomic variable in
`φ⁻¹(w)`." -/
theorem refine_perm {l l' : List (Fin G.n)} (hl : l.Nodup) (hp : l'.Perm l)
    {m m' : List (Fin H.n)} (hm : m.Nodup) (hq : m'.Perm m)
    (h₁ : preimW φ (FreeMonoid.ofList l) = FreeMonoid.ofList m)
    (h₂ : preimW φ (FreeMonoid.ofList l') = FreeMonoid.ofList m') :
    Arrow.mk ((refine φ JH JG).map (JG.projM.map (permFs JG l l' hl hp))) =
      Arrow.mk (JH.projM.map (permFs JH m m' hm hq)) := by
  rw [refine_projM]
  refine Eq.trans ?_ (ProdSig.arrow_projM_eq_of_card_zero (Q := H.K.sig) (J := JH)
    (a := preimW φ (FreeMonoid.ofList l)) (b := preimW φ (FreeMonoid.ofList l'))
    (f := eqToHom (subst_obj φ JG JH _).symm ≫ (subst φ JG JH).map (permFs JG l l' hl hp) ≫
      eqToHom (subst_obj φ JG JH _))
    (by rw [h₁]; exact hm) h₁ h₂ (fun p => ?_) (fun p => card_permFs (J := JH) p m m' hm hq))
  · simp only [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]
  · rw [card_comp, card_comp, card_eqToHom, card_eqToHom, card_subst, card_permFs]

theorem mk_map_twist {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {a a' b c d d' : C}
    (h : a = a') (A : a' ⟶ b) (B : b ⟶ c) (Cm : c ⟶ d) (h' : d = d') :
    Arrow.mk (F.map ((eqToHom h ≫ A) ≫ B ≫ Cm ≫ eqToHom h')) =
      Arrow.mk (F.map A ≫ F.map B ≫ F.map Cm) := by
  subst h h'; simp

theorem mk_twist {C : Type*} [Category C] {a a' b c d d' : C}
    (h : a = a') (A : a' ⟶ b) (B : b ⟶ c) (Cm : c ⟶ d) (h' : d = d') :
    Arrow.mk ((eqToHom h ≫ A) ≫ B ≫ Cm ≫ eqToHom h') = Arrow.mk (A ≫ B ≫ Cm) := by
  subst h h'; simp

theorem refine_map_eqToHom {a b : JG.FsM} (h : a = b) :
    Arrow.mk ((refine φ JH JG).map (eqToHom h)) = Arrow.mk (𝟙 ((refine φ JH JG).obj a)) := by
  subst h; simp

/-- **Proposition 6.6.** For singular variables `v`, `w` of `Cau(G)`,
`φ^*([w ‖ v]) = [φ^*(w) ‖ φ^*(v)]`, where `φ^*(v) = φ⁻¹(v)` (singular by `singular_preimW`); in the
unabbreviated form (6.2) of the paper, `φ^*([w ‖ v]_{(V_G, K_G)}) = [φ^*(w) ‖ φ^*(v)]_{(V_H, K_H)}`. -/
theorem prop_6_6 (v w : FreeMonoid (Fin G.n)) (hv : Singular v) (hw : Singular w) :
    Arrow.mk ((refine φ JH JG).map (causalEffect JG v w hv hw)) =
      Arrow.mk (causalEffect JH (preimW φ v) (preimW φ w) (singular_preimW φ hv)
        (singular_preimW φ hw)) := by
  unfold causalEffect twistIn twistOut
  refine (mk_map_twist _ _ _ _ _ _).trans ((Arrow.mk_comp_congr ?_ (Arrow.mk_comp_congr ?_ ?_)).trans
    (mk_twist _ _ _ _ _).symm)
  · refine refine_perm φ JG JH _ _ _ _ ?_ ?_
    · rw [FreeMonoid.ofList_toList, FreeMonoid.ofList_toList]
    · change preimW φ (finWord _) = finWord _
      rw [preimW_finWord, letterSet_preimW]
  · rw [prop_6_6_sets, letterSet_preimW, letterSet_preimW]
  · refine refine_perm φ JG JH _ _ _ _ ?_ ?_
    · change preimW φ (finWord _) = finWord _
      rw [preimW_finWord, letterSet_preimW]
    · rw [FreeMonoid.ofList_toList, FreeMonoid.ofList_toList]

end FinODAG

end FreeMarkov
