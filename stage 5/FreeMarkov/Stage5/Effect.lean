/-
Free Markov categories, Stage 5: effects in a strict Markov category (Definition 5.4 in the
generality of Remark 5.7, design decision D6), Lemma 5.5, Proposition 5.6, twists.

* `EffData C n`: a sequence `W = (w_1, …, w_n)` of objects of the strict Markov category `C`
  (repetitions and `w_i = 1` allowed) and a family `K` of pairs `(S_i, κ_i)`, `κ_i : w_{S_i} → w_i`,
  whose associated directed graph is acyclic.
* `EffData.functor D J`: the strict Markov functor `F_{(W,K)} : F_s(W(K))/S_M → C` sending the letter
  `i` to `w_i` and the producer `κ_i` to `κ_i` (Theorem 4.1).
* `EffData.effect D J S T : w_S → w_T`, the **`(W, K)`-effect** `[w_T ‖ w_S]_{(W,K)}`: the image under
  `F_{(W,K)}` of the effect in the free Markov category.  With the multipliers read as `m`-fold copies
  (Remark 5.7), the diagram `Γ_{[w_T ‖ w_S]}` of Definition 5.4 in `C` is the image of an effect
  diagram of `W(K)` (its nodes `κ_i` sent to `κ_i`, its duplicates and discards on `i` to those on
  `w_i`); so this is the morphism it represents.  No straightness is assumed.
* `EffData.lemma_5_5`: `[T ‖ S] = [T ‖ T_i] ∘ [T_i ‖ S]`.
* `EffData.prop_5_6`: `F([T ‖ S]_{(W,K)}) = [T ‖ S]_{(F(W), F(K))}` for a strict Markov functor `F`.
* `EffData.effect_freeData`: in the free Markov category of `K` itself, with `w_i = i` and
  `κ_i` the generators, the effect is `freeEffect` (the causal effect of Definition 6.3).
* Twists: `EffData.permStar` (the symmetry `τ_*` given by the node-free diagram that connects equal
  indices), `EffData.twist` (`[τ(T) ‖ σ(S)] = τ_* ∘ [T ‖ S] ∘ σ_*⁻¹`).

The cited result C1 enters through `J`.
-/
module

public import FreeMarkov.Stage5.EffectFree

@[expose] public section

universe v u v₂ u₂

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov JoyalStreet Relation

variable {n : ℕ}

/-! ### Node-free diagrams of permutations -/

section Perm

variable {Q : ProdSig} (J : JoyalStreet Q.G.toFreeGraphMonoid)

open Classical in
/-- The positions in `l` of the members of `l'`. -/
noncomputable def posList (l l' : List Q.X) (h : ∀ x ∈ l', x ∈ l) :
    List (Fin (Diagram.wlen (FreeMonoid.ofList l))) :=
  l'.attach.map fun x => ⟨l.idxOf x.1, List.idxOf_lt_length_of_mem (h _ x.2)⟩

theorem posList_nodup {l l' : List Q.X} (h : ∀ x ∈ l', x ∈ l) (hl' : l'.Nodup) :
    (posList l l' h).Nodup := by
  classical
  refine (List.nodup_attach.2 hl').map fun x y hxy => Subtype.ext ?_
  have := congrArg Fin.val hxy
  exact (List.idxOf_inj (h _ x.2)).1 this

theorem mem_posList {l l' : List Q.X} (h : ∀ x ∈ l', x ∈ l) (hl : l.Nodup) (hp : l'.Perm l)
    (i : Fin (Diagram.wlen (FreeMonoid.ofList l))) : i ∈ posList l l' h := by
  classical
  have hi : (i : ℕ) < l.length := i.2
  have hx : l[(i : ℕ)] ∈ l' := hp.mem_iff.2 (List.getElem_mem hi)
  refine List.mem_map.2 ⟨⟨l[(i : ℕ)], hx⟩, List.mem_attach _ _, Fin.ext ?_⟩
  exact hl.idxOf_getElem _ hi

theorem posList_letters {l l' : List Q.X} (h : ∀ x ∈ l', x ∈ l) :
    (posList l l' h).map (Diagram.letters (FreeMonoid.ofList l)) = l' := by
  classical
  unfold posList
  rw [List.map_map]
  conv_rhs => rw [← List.attach_map_subtype_val l']
  refine List.map_congr_left fun x _ => ?_
  exact List.getElem_idxOf _

/-- The symmetry of `F_s(Q.G)` from `w_l` to `w_{l'}` for a permutation `l'` of the duplicate-free
list `l`: the node-free diagram in which each letter of the domain is connected with the same letter
of the codomain. -/
noncomputable def permFs (l l' : List Q.X) (hl : l.Nodup) (hp : l'.Perm l) :
    Fs.of J (FreeMonoid.ofList l) ⟶ Fs.of J (FreeMonoid.ofList l') :=
  J.hom (⟨DClass.mk (Diagram.permNF (G := Q.G) (FreeMonoid.ofList l)
      (posList l l' fun x hx => hp.mem_iff.1 hx) (posList_nodup _ (hp.nodup_iff.2 hl)) (mem_posList _ hl hp)),
    by rw [DClass.dom_mk, Diagram.permNF_domWord],
    by rw [DClass.cod_mk, Diagram.permNF_codWord, posList_letters]⟩ :
      DHom Q.G.toFreeGraphMonoid (FreeMonoid.ofList l) (FreeMonoid.ofList l'))

theorem card_permFs (k : Q.P) (l l' : List Q.X) (hl : l.Nodup) (hp : l'.Perm l) :
    J.card (.mech k) (permFs J l l' hl hp) = 0 := by
  unfold permFs JoyalStreet.card
  change DClass.card (ProdSig.Arr.mech k) (DClass.mk (Diagram.permNF (G := Q.G) _ _ _ _)) = 0
  rw [DClass.card_mk]
  exact Nat.card_of_isEmpty

/-- Two symmetries in opposite directions compose to the identity in `F_s(Q.G)/S_M`. -/
theorem permFs_comp (l l' : List Q.X) (hl : l.Nodup) (hp : l'.Perm l) :
    J.projM.map (permFs J l l' hl hp ≫ permFs J l' l (hp.nodup_iff.2 hl) hp.symm) = 𝟙 _ := by
  rw [← J.projM.map_id]
  refine ProdSig.projM_eq_of_card (a := FreeMonoid.ofList l) (b := FreeMonoid.ofList l) hl (fun p => ?_) (fun p => ?_) fun p => ?_
  · rw [card_comp, card_permFs, card_permFs]; simp
  · rw [card_id]; simp
  · rw [card_comp, card_permFs, card_permFs, card_id]

end Perm

/-! ### Effects in a strict Markov category -/

/-- *Definition 5.4.* The data of an effect in the strict Markov category `C`: a sequence
`W = (w_1, …, w_n)` of objects ("repetitions are allowed, and so is `w_i = 1`") and the family `K`
of the pairs `(S_i, κ_i)`, `κ_i : w_{S_i} → w_i`, whose associated directed graph is acyclic. -/
structure EffData (C : Type u) [Monoid C] [Category.{v} C] [StrictMarkov C] (n : ℕ) extends EffSig n where
  /-- The objects `w_i`. -/
  w : Fin n → C
  /-- The morphisms `κ_i : w_{S_i} → w_i`. -/
  κ (i : Fin n) : FreeMonoid.lift w (finWord (pa i)) ⟶ w i

namespace EffData

variable {C : Type u} [Monoid C] [Category.{v} C] [StrictMarkov C] (D : EffData C n)

/-- `w_S = ⊗_{i ∈ S} w_i`, in the increasing order of `i` (`w_∅ = 1`). -/
abbrev wS (S : Finset (Fin n)) : C := FreeMonoid.lift D.w (finWord S)

variable (J : JoyalStreet D.sig.G.toFreeGraphMonoid)

/-- The strict Markov functor `F_{(W,K)} : F_s(W(K))/S_M → C` with `F(i) = w_i` and `F(κ_i) = κ_i`
(Theorem 4.1). -/
noncomputable def functor : StrictMarkovFunctor J.FsM C :=
  J.lift (D.sig.toHom D.w D.κ) (D.sig.toHom_matches _ _)

theorem functor_obj (a : FreeMonoid (Fin n)) :
    (D.functor J).obj (J.projM.obj (Fs.of J a)) = FreeMonoid.lift D.w a :=
  lift_obj _ _ a

/-- *Definition 5.4.* The **`(W, K)`-effect** of `w_S` on `w_T`, `[w_T ‖ w_S]_{(W,K)} : w_S → w_T`. -/
noncomputable def effect (S T : Finset (Fin n)) : D.wS S ⟶ D.wS T :=
  eqToHom (D.functor_obj J (finWord S)).symm ≫ (D.functor J).map (EffSig.freeEffect J S T) ≫
    eqToHom (D.functor_obj J (finWord T))

theorem arrow_effect (S T : Finset (Fin n)) :
    Arrow.mk (D.effect J S T) = Arrow.mk ((D.functor J).map (EffSig.freeEffect J S T)) :=
  arrow_mk_cast _ _ _

/-- **Lemma 5.5.** For `i ∈ V(G_{S → T}) ∖ S`, `[T ‖ S] = [T ‖ T_i] ∘ [T_i ‖ S]` (in every strict
Markov category, with the multipliers read as `m`-fold copies; D6). -/
theorem lemma_5_5 {S T : Finset (Fin n)} {i : Fin n} (hi : D.R S T i) :
    D.effect J S T = D.effect J S (D.Ti S T i) ≫ D.effect J (D.Ti S T i) T := by
  unfold effect
  rw [EffSig.lemma_5_5_free hi, Functor.map_comp]
  simp

/-! ### Proposition 5.6 -/

variable {D' : Type u₂} [Monoid D'] [Category.{v₂} D'] [StrictMarkov D']

theorem _root_.FreeMarkov.StrictFunctor.lift_comp (F : StrictFunctor C D') (w : Fin n → C)
    (a : FreeMonoid (Fin n)) : FreeMonoid.lift (F.obj ∘ w) a = F.obj (FreeMonoid.lift w a) := by
  have : F.objHom.comp (FreeMonoid.lift w) = FreeMonoid.lift (F.obj ∘ w) :=
    FreeMonoid.hom_eq fun x => by simp [StrictFunctor.objHom]
  rw [← this]; rfl

/-- *Proposition 5.6.* `F(W) = (F(w_1), …, F(w_n))` and `F(K)`, the family of the pairs
`(S_i, F(κ_i))`, "so that the directed graph associated with `F(K)` is `G` again". -/
noncomputable abbrev map (F : StrictMarkovFunctor C D') : EffData D' n where
  toEffSig := D.toEffSig
  w := F.obj ∘ D.w
  κ i := eqToHom (StrictFunctor.lift_comp F.toStrictFunctor D.w _) ≫ F.map (D.κ i)

theorem functor_map (F : StrictMarkovFunctor C D') :
    F.comp (D.functor J) = (D.map F).functor J := by
  refine eq_lift _ _ _ ?_
  have hs : (D.functor J).toGraphMonoidHom.comp J.iM = D.sig.toHom D.w D.κ := (lift_spec _ _).symm
  change D.sig.toHom (F.obj ∘ D.w) (D.map F).κ =
    F.toGraphMonoidHom.comp ((D.functor J).toGraphMonoidHom.comp J.iM)
  rw [hs]
  refine GraphMonoid.Hom.ext ?_ (funext fun x => ?_)
  · exact (FreeMonoid.hom_eq fun x => by simp [ProdSig.toHom]; rfl)
  · rcases x with x | x | i
    · exact (F.map_copy _).symm
    · exact (F.map_discard _).symm
    · change Arrow.mk (eqToHom _ ≫ F.map (D.κ i)) = Arrow.mk (F.map (D.κ i))
      simp

/-- **Proposition 5.6.** "Let `N` be another straight Markov category and `F : M → N` a strict Markov
functor ... Then `F([T ‖ S]_{(W,K)}) = [T ‖ S]_{(F(W), F(K))}`" — here for any strict Markov
categories (D6), as an equation of arrows (the two sides have the same source `F(w_S) = F(W)_S` and
target, up to the identification `F(⊗ w_i) = ⊗ F(w_i)`). -/
theorem prop_5_6 (F : StrictMarkovFunctor C D') (S T : Finset (Fin n)) :
    Arrow.mk (F.map (D.effect J S T)) = Arrow.mk ((D.map F).effect J S T) := by
  rw [arrow_effect, ← functor_map]
  unfold effect
  simp only [Functor.map_comp, eqToHom_map]
  exact arrow_mk_cast _ _ _

/-! ### The effect in the free Markov category of `K` -/

theorem _root_.FreeMarkov.JoyalStreet.lift_word (K : EffSig n) (J : JoyalStreet K.sig.G.toFreeGraphMonoid)
    (a : FreeMonoid (Fin n)) :
    FreeMonoid.lift (fun i => J.projM.obj (Fs.of J (FreeMonoid.of i))) a = J.projM.obj (Fs.of J a) := by
  have : FreeMonoid.lift (fun i => J.projM.obj (Fs.of J (FreeMonoid.of i))) =
      (MonoidHom.id (FreeMonoid (Fin n)) : FreeMonoid (Fin n) →* J.FsM) :=
    FreeMonoid.hom_eq fun x => by simp; rfl
  rw [this]; rfl

/-- The data `(W, K)` in the free Markov category of `K` itself: `w_i = i`, `κ_i` the generator. -/
noncomputable abbrev freeData (K : EffSig n) (J : JoyalStreet K.sig.G.toFreeGraphMonoid) :
    EffData J.FsM n where
  toEffSig := K
  w i := J.projM.obj (Fs.of J (FreeMonoid.of i))
  κ i := eqToHom (J.lift_word K _) ≫ J.projM.map (EffSig.mechF J i)

/-- In the free Markov category of `K`, the `(W, K)`-effect with `w_i = i` and the generators `κ_i`
is the effect of `freeEffect` (the functor `F_{(W,K)}` is the identity). -/
theorem effect_freeData (K : EffSig n) (J : JoyalStreet K.sig.G.toFreeGraphMonoid)
    (S T : Finset (Fin n)) :
    Arrow.mk ((freeData K J).effect J S T) = Arrow.mk (EffSig.freeEffect J S T) := by
  have h : (freeData K J).functor J = StrictMarkovFunctor.id J.FsM := by
    refine (eq_lift _ _ _ ?_).symm
    refine GraphMonoid.Hom.ext ?_ (funext fun x => ?_)
    · exact (FreeMonoid.hom_eq fun x => by simp [ProdSig.toHom]; rfl)
    · rcases x with x | x | i
      · exact (J.iM_matches.dup x).symm
      · exact (J.iM_matches.disc x).symm
      · show Arrow.mk ((freeData K J).κ i) = Arrow.mk ((J.iM.A (.mech i)).hom)
        rw [iM_A]
        simp [EffSig.mechF]
  rw [arrow_effect, h]
  rfl

/-! ### Twists -/

/-- `w_l = ⊗_{i ∈ l} w_i` for a list of indices. -/
abbrev wL (l : List (Fin n)) : C := FreeMonoid.lift D.w (FreeMonoid.ofList l)

/-- The symmetry `τ_* : w_l → w_{l'}` for a permutation `l'` of a duplicate-free list `l`: "the
morphism represented by the diagram without nodes in which, for each `i`, an edge connects the
factor `w_i` of the domain with the factor `w_i` of the codomain" (the image under `F_{(W,K)}` of
the node-free diagram of `W(K)`). -/
noncomputable def permStar (l l' : List (Fin n)) (hl : l.Nodup) (hp : l'.Perm l) : D.wL l ⟶ D.wL l' :=
  eqToHom (D.functor_obj J _).symm ≫ (D.functor J).map (J.projM.map (permFs J l l' hl hp)) ≫
    eqToHom (D.functor_obj J _)

theorem permStar_comp (l l' : List (Fin n)) (hl : l.Nodup) (hp : l'.Perm l) :
    D.permStar J l l' hl hp ≫ D.permStar J l' l (hp.nodup_iff.2 hl) hp.symm = 𝟙 _ := by
  unfold permStar
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, permFs_comp, CategoryTheory.Functor.map_id]
  simp

/-- *Twists.* For orderings `lS`, `lT` of `S`, `T` (permutations `σ`, `τ`), the twist
`[τ(T) ‖ σ(S)] = τ_* ∘ [T ‖ S] ∘ σ_*⁻¹ : w_{σ(S)} → w_{τ(T)}`; "such a twist is determined by the
pair of permutations". -/
noncomputable def twist (S T : Finset (Fin n)) (lS lT : List (Fin n)) (hS : lS.Perm (S.sort (· ≤ ·)))
    (hT : lT.Perm (T.sort (· ≤ ·))) : D.wL lS ⟶ D.wL lT :=
  D.permStar J lS (S.sort (· ≤ ·)) (hS.nodup_iff.2 (Finset.sort_nodup _ _)) hS.symm ≫
    D.effect J S T ≫ D.permStar J (T.sort (· ≤ ·)) lT (Finset.sort_nodup _ _) hT

end EffData

end FreeMarkov
