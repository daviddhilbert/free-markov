/-
Free Markov categories, Stage 7 (follow-up): the single diagrams of `δ_a` and `ε_a` on words
(Section 4, before the proof of Theorem 4.1; Stage 3's open item 2).

"Let `a = a_1 … a_n` be an object in `F_s(G)`, where `a_i ∈ S`. Let `Γ` be the diagram that joins
those of `⊗_i δ_{a_i}`, `(⊗_i 1_{a_i}) ⊗ (⊗_i 1_{a_i})` together by connecting, for each `i`, the
two outputs of `δ_{a_i}` with the `i`th and the `(n+i)`th edges of the latter ... Of course `Γ` is
not unique, as the two outputs of each `δ_{a_i}` may be connected in either order. On the other
hand, in light of (4.3), all such `Γ` represent the same morphism in the quotient category
`F_s(G)/S_M`, which is denoted by `δ_a` ... Also set `ε_a = ⊗_i ε_{a_i}`."

* `Diagram.copyD G a c`: the diagram `Γ` literally, for letters `a : Fin n → S` and a prong order
  `c : Fin n → Bool`: nodes `Fin n` (the duplicate on `a_i`), edges the `n` inputs and the `2n`
  outputs; the domain is the inputs in order, the codomain lists the outputs going to the `i`th
  edge, then those going to the `(n+i)`th edge; `c i` says which prong of the `i`th duplicate goes
  to the `i`th edge.  `Diagram.copyWordD G w c` for a word `w`.
* `Diagram.discardD G a`: one discard per letter (`ε_{a_1} ⊗ ⋯ ⊗ ε_{a_n}` as one diagram).
* **`JoyalStreet.projM_copyD`** / `projM_copyWordD`: for every prong order the class of `Γ` in
  `F_s(G)/S_M` is `copyM a`, the duplicate on `a` of the strict Markov structure of Theorem 4.1;
  `projM_discardD` / `projM_discardWordD`: the class of the diagram of discards is `discardM a`.

Method (not the paper's surgery with (4.3), which is not needed): over the free `DD`-graph monoid
with the pairwise distinct letters `0, …, n-1` there is only one morphism from `0 ⋯ (n-1)` to any
word in `F_s/S_M` (Stage 5, `ProdSig.free_hom_eq`, by label coherence and Lemma 4.4), so the
diagram with letters `0, …, n-1` represents the duplicate there; relabelling `i ↦ a_i` is the strict
Markov functor of Theorem 4.1 (naturality of C1 under relabelling, Stage 1's `val_synMap`), which
preserves duplicates.  For the letters `0, …, n-1` C1 is the theorem of Stage 7
(`JoyalStreet.ofCombinatorial`), so the statement for `J : JoyalStreet G` assumes nothing else.
-/
module

public import FreeMarkov.Stage7.JoyalStreet

@[expose] public section

universe w v

namespace FreeMarkov

open CategoryTheory StrictSMC StrictMarkov FreeGraphMonoid

/-! ### The diagrams -/

namespace PGraph

/-- The graph of `δ_{a_1 ⋯ a_n}`: nodes `Fin n`; edges `inl i` (the input of the `i`th node),
`inr (inl i)` (its output going to the `i`th codomain edge), `inr (inr i)` (its output going to the
`(n+i)`th codomain edge).  `c i = false`: the first prong goes to the `i`th edge. -/
def copyPG (n : ℕ) (c : Fin n → Bool) : PGraph (Fin n) (Fin n ⊕ (Fin n ⊕ Fin n)) where
  src := Sum.elim (fun _ => none) (Sum.elim some some)
  tgt := Sum.elim some (fun _ => none)
  ins x := [Sum.inl x]
  outs x := cond (c x) [Sum.inr (Sum.inr x), Sum.inr (Sum.inl x)]
    [Sum.inr (Sum.inl x), Sum.inr (Sum.inr x)]
  ins_nodup _ := List.nodup_singleton _
  outs_nodup x := by cases c x <;> simp
  mem_ins x e := by rcases e with e | e | e <;> simp [eq_comm]
  mem_outs x e := by cases c x <;> rcases e with e | e | e <;> simp [eq_comm]
  acyclic _ := not_transGen_of_forall_not fun _ _ ⟨e, h₁, h₂⟩ => by
    rcases e with e | e | e <;> simp at h₁ h₂

/-- The graph of `ε_{a_1} ⊗ ⋯ ⊗ ε_{a_n}`: nodes `Fin n`, edge `i` enters node `i`. -/
def discardPG (n : ℕ) : PGraph (Fin n) (Fin n) where
  src _ := none
  tgt := some
  ins x := [x]
  outs _ := []
  ins_nodup _ := List.nodup_singleton _
  outs_nodup _ := List.nodup_nil
  mem_ins x e := by simp [eq_comm]
  mem_outs x e := by simp
  acyclic _ := not_transGen_of_forall_not fun _ _ ⟨e, h₁, _⟩ => by simp at h₁

end PGraph

namespace Diagram

variable {S : Type w} (G : FreeDDGraphMonoid.{w, v} S) {n : ℕ}

/-- **The diagram `Γ` of `δ_a`** (Section 4) for the letters `a : Fin n → S` and the prong order
`c`: one duplicate on `a_i` for each `i`, the domain the `n` inputs in order, the codomain the
outputs ordered so that the codomain word is `a a`; the two outputs of the `i`th duplicate are
the `i`th and the `(n+i)`th codomain edges, in the order given by `c i`. -/
def copyD (a : Fin n → S) (c : Fin n → Bool) :
    Diagram G.toFreeGraphMonoid (Fin n) (Fin n ⊕ (Fin n ⊕ Fin n)) where
  toPGraph := PGraph.copyPG n c
  dom := (List.finRange n).map Sum.inl
  cod := (List.finRange n).map (fun i => Sum.inr (Sum.inl i)) ++
    (List.finRange n).map (fun i => Sum.inr (Sum.inr i))
  dom_nodup := (List.nodup_finRange n).map Sum.inl_injective
  cod_nodup := by
    refine List.Nodup.append ((List.nodup_finRange n).map fun _ _ h => by simpa using h)
      ((List.nodup_finRange n).map fun _ _ h => by simpa using h) ?_
    simp [List.disjoint_left]
  mem_dom e := by rcases e with e | e | e <;> simp [PGraph.copyPG]
  mem_cod e := by rcases e with e | e | e <;> simp [PGraph.copyPG]
  val :=
    { v₀ := Sum.elim a (Sum.elim a a)
      v₁ := fun x => G.dup (a x)
      s_v₁ := fun x => by rw [G.s_dup]; rfl
      t_v₁ := fun x => by
        rw [G.t_dup]
        cases h : c x <;> simp [PGraph.copyPG, h] }

theorem copyD_domWord (a : Fin n → S) (c : Fin n → Bool) :
    (copyD G a c).domWord = FreeMonoid.ofList ((List.finRange n).map a) := by
  simp [domWord, copyD, List.map_map, Function.comp_def]

theorem copyD_codWord (a : Fin n → S) (c : Fin n → Bool) :
    (copyD G a c).codWord =
      FreeMonoid.ofList ((List.finRange n).map a) * FreeMonoid.ofList ((List.finRange n).map a) := by
  simp [codWord, copyD, List.map_map, Function.comp_def]

/-- **The diagram of `ε_a`**: one discard on `a_i` for each `i`, the domain the `n` inputs in
order, the codomain empty. -/
def discardD (a : Fin n → S) : Diagram G.toFreeGraphMonoid (Fin n) (Fin n) where
  toPGraph := PGraph.discardPG n
  dom := List.finRange n
  cod := []
  dom_nodup := List.nodup_finRange n
  cod_nodup := List.nodup_nil
  mem_dom e := by simp [PGraph.discardPG]
  mem_cod e := by simp [PGraph.discardPG]
  val :=
    { v₀ := a
      v₁ := fun x => G.disc (a x)
      s_v₁ := fun x => by rw [G.s_disc]; rfl
      t_v₁ := fun x => by rw [G.t_disc]; rfl }

theorem discardD_domWord (a : Fin n → S) :
    (discardD G a).domWord = FreeMonoid.ofList ((List.finRange n).map a) := rfl

theorem discardD_codWord (a : Fin n → S) : (discardD G a).codWord = 1 := rfl

/-- The diagram `Γ` of `δ_w` for a word `w`, with the prong order `c`. -/
abbrev copyWordD (w : FreeMonoid S) (c : Fin (wlen w) → Bool) :
    Diagram G.toFreeGraphMonoid (Fin (wlen w)) (Fin (wlen w) ⊕ (Fin (wlen w) ⊕ Fin (wlen w))) :=
  copyD G (letters w) c

theorem copyWordD_domWord (w : FreeMonoid S) (c : Fin (wlen w) → Bool) :
    (copyWordD G w c).domWord = w :=
  (copyD_domWord G _ c).trans (ofList_map_letters w)

theorem copyWordD_codWord (w : FreeMonoid S) (c : Fin (wlen w) → Bool) :
    (copyWordD G w c).codWord = w * w :=
  (copyD_codWord G _ c).trans (by rw [ofList_map_letters])

/-- The diagram of `ε_w` for a word `w`. -/
abbrev discardWordD (w : FreeMonoid S) : Diagram G.toFreeGraphMonoid (Fin (wlen w)) (Fin (wlen w)) :=
  discardD G (letters w)

theorem discardWordD_domWord (w : FreeMonoid S) : (discardWordD G w).domWord = w :=
  ofList_map_letters w

end Diagram

/-! ### Relabelling the distinct letters `0, …, n-1` -/

namespace CopyDiagram

variable {S : Type w} (G : FreeDDGraphMonoid.{w, v} S) {n : ℕ} (a : Fin n → S)

/-- The relabelling of the free `DD`-graph monoid on the Diagram.letters `Fin n` (only duplicates and
discards) into `G`, sending the letter `i` to `a i`. -/
def relab : (ProdSig.free (Fin n)).G.toFreeGraphMonoid.Relabel G.toFreeGraphMonoid where
  onS := a
  onA
    | .dup x => G.dup (a x)
    | .disc x => G.disc (a x)
    | .mech p => p.elim
  s_onA := by
    rintro (x | x | p)
    · rw [G.s_dup]; rfl
    · rw [G.s_disc]; rfl
    · exact p.elim
  t_onA := by
    rintro (x | x | p)
    · rw [G.t_dup]; rfl
    · rw [G.t_disc]; rfl
    · exact p.elim

/-- Relabelling the diagram of `δ_{0 ⋯ (n-1)}` gives the diagram of `δ_a`. -/
def relabelCopyIso (c : Fin n → Bool) :
    ((Diagram.copyD (ProdSig.free (Fin n)).G id c).relabel (relab G a)).Iso
      (Diagram.copyD G a c) where
  eN := Equiv.refl _
  eE := Equiv.refl _
  ins_map _ := (List.map_id _).symm
  outs_map _ := (List.map_id _).symm
  dom_map := (List.map_id _).symm
  cod_map := (List.map_id _).symm
  v₀_map e := by rcases e with e | e | e <;> rfl
  v₁_map _ := rfl

end CopyDiagram

/-! ### The classes -/

namespace JoyalStreet

open CopyDiagram

variable {S : Type w} {G : FreeDDGraphMonoid.{w, v} S} (J : JoyalStreet G.toFreeGraphMonoid)
  {n : ℕ}

/-- **The diagram `Γ` represents `δ_a`** (Section 4): for every choice of the order of the prongs,
the class of the diagram `Γ` of `δ_a` in `F_s(G)/S_M` is the duplicate `copyM a` of the strict
Markov structure of Theorem 4.1. -/
theorem projM_copyD (a : Fin n → S) (c : Fin n → Bool) :
    Arrow.mk (J.projM.map (J.hom (DHom.mk (Diagram.copyD G a c)))) =
      Arrow.mk (J.copyM (J.wordM (FreeMonoid.ofList ((List.finRange n).map a)))) := by
  let Q := ProdSig.free (Fin n)
  let JX := JoyalStreet.ofCombinatorial Q.G.toFreeGraphMonoid
  let φ := relab G a
  let Γ' := Diagram.copyD Q.G id c
  let obj : Fin n → J.FsM := fun i => J.wordM (FreeMonoid.of (a i))
  let κ : ∀ p, FreeMonoid.lift obj (Q.src p) ⟶ obj (Q.out p) := fun p => p.elim
  let F := JX.lift (Q.toHom obj κ) (Q.toHom_matches obj κ)
  let m := (JX.equiv _ _).symm (DHom.mk Γ')
  -- the class of the relabelled diagram is the image of `m` under `Syn(φ)`
  have h₁ : Arrow.mk (J.toFsStrict.map (φ.synMap.map m)) =
      Arrow.mk (J.hom (DHom.mk (Diagram.copyD G a c))) := by
    apply J.arrow_eq_of_cls_eq
    change (J.equiv _ _ (φ.synMap.map m)).1 = DClass.mk _
    rw [JoyalStreet.val_synMap JX J φ m, Equiv.apply_symm_apply]
    exact (DClass.mk_relabel φ Γ').trans (DClass.mk_eq_mk (relabelCopyIso G a c))
  -- the two strict functors `Syn_s(Q.G) → F_s(G)/S_M` agree on generators
  have h₂ : ((J.quotProjStrict _ _).comp J.toFsStrict).comp φ.synMap =
      F.toStrictFunctor.comp ((JX.quotProjStrict _ _).comp JX.toFsStrict) := by
    have e₁ : ((J.quotProjStrict _ _).comp J.toFsStrict).comp φ.synMap =
        Syn.lift (Q.toHom obj κ) := by
      refine Syn.eq_lift _ ?_
      change ((J.quotProjStrict _ _).comp J.toFsStrict).toGraphMonoidHom.comp
        (φ.synMap.toGraphMonoidHom.comp (Syn.ι _)) = _
      rw [FreeGraphMonoid.Relabel.synMap, Syn.lift_comp_ι]
      ext x
      · rfl
      · rcases x with x | x | p
        · change Arrow.mk (J.projM.map (J.equiv _ _ (Syn.gen (G.dup (a x))))) = _
          rw [J.map_gen]
          exact (J.iM_matches.dup (a x)).trans rfl
        · change Arrow.mk (J.projM.map (J.equiv _ _ (Syn.gen (G.disc (a x))))) = _
          rw [J.map_gen]
          exact (J.iM_matches.disc (a x)).trans rfl
        · exact p.elim
    have e₂ : F.toStrictFunctor.comp ((JX.quotProjStrict _ _).comp JX.toFsStrict) =
        Syn.lift (Q.toHom obj κ) := by
      refine Syn.eq_lift _ ?_
      have hs := lift_spec (J := JX) (Q.toHom obj κ) (Q.toHom_matches obj κ)
      conv_rhs => rw [hs]
      change F.toGraphMonoidHom.comp
        (((JX.quotProjStrict _ _).comp JX.toFsStrict).toGraphMonoidHom.comp (Syn.ι _)) =
          F.toGraphMonoidHom.comp JX.iM
      congr 1
      change (JX.quotProjStrict _ _).toGraphMonoidHom.comp
        (JX.toFsStrict.toGraphMonoidHom.comp (Syn.ι _)) =
          (JX.quotProjStrict _ _).toGraphMonoidHom.comp JX.ι
      rw [JX.toFsStrict_comp_ι]
    rw [e₁, e₂]
  have h₃ : JX.toFsStrict.map m = JX.hom (DHom.mk Γ') := Equiv.apply_symm_apply _ _
  -- in `F_s(Q.G)/S_M` the class of `Γ'` is the duplicate, by uniqueness
  let w' : FreeMonoid (Fin n) := FreeMonoid.ofList ((List.finRange n).map id)
  have hd' : Γ'.domWord = w' := Diagram.copyD_domWord _ _ _
  have hc' : JX.wordM w' * JX.wordM w' = JX.projM.obj (Fs.of JX Γ'.codWord) :=
    (Diagram.copyD_codWord _ _ _).symm
  have hnd : (FreeMonoid.toList Γ'.domWord).Nodup := by
    rw [hd']
    exact (List.nodup_finRange n).map fun _ _ h => h
  have h0 : JX.projM.obj (Fs.of JX Γ'.domWord) = JX.wordM w' :=
    (congrArg (fun x => JX.wordM x) hd' : _)
  have h₄ : JX.projM.map (JX.hom (DHom.mk Γ')) =
      eqToHom h0 ≫ δ_ (JX.wordM w') ≫ eqToHom hc' :=
    ProdSig.free_hom_eq JX hnd _ _
  -- the functor `F` preserves duplicates
  have hobj : F.obj (JX.wordM w') = J.wordM (FreeMonoid.ofList ((List.finRange n).map a)) := by
    rw [lift_obj]
    change FreeMonoid.lift obj (FreeMonoid.ofList ((List.finRange n).map id)) = _
    rw [List.map_id]
    induction (List.finRange n) with
    | nil => rfl
    | cons i l ih =>
      rw [FreeMonoid.ofList_cons, map_mul, ih, FreeMonoid.lift_eval_of]
      rfl
  calc Arrow.mk (J.projM.map (J.hom (DHom.mk (Diagram.copyD G a c))))
      = Arrow.mk (J.projM.map (J.toFsStrict.map (φ.synMap.map m))) :=
        J.projM.mk_map_congr h₁.symm
    _ = Arrow.mk ((((J.quotProjStrict _ _).comp J.toFsStrict).comp φ.synMap).map m) := rfl
    _ = Arrow.mk ((F.toStrictFunctor.comp ((JX.quotProjStrict _ _).comp JX.toFsStrict)).map m) := by
        rw [h₂]
    _ = Arrow.mk (F.map (JX.projM.map (JX.toFsStrict.map m))) := rfl
    _ = Arrow.mk (F.map (eqToHom h0 ≫ δ_ (JX.wordM w') ≫ eqToHom hc')) := by
        exact congrArg (fun t => Arrow.mk (F.map t)) ((congrArg JX.projM.map h₃).trans h₄)
    _ = Arrow.mk (F.map (δ_ (JX.wordM w'))) := by
        rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
          Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]
    _ = Arrow.mk (δ_ (F.obj (JX.wordM w'))) := F.map_copy _
    _ = _ := by rw [hobj]; rfl

/-- **`δ_w` is the class of the diagram `Γ`**, for a word `w` and every prong order (the paper's
form: a morphism `w → w w` of `F_s(G)/S_M`). -/
theorem projM_copyWordD (w : FreeMonoid S) (c : Fin (Diagram.wlen w) → Bool) :
    J.projM.map (J.hom ((DHom.mk (Diagram.copyWordD G w c)).cast
        (Diagram.copyWordD_domWord G w c) (Diagram.copyWordD_codWord G w c))) =
      J.copyM (J.wordM w) := by
  refine Arrow.eq_of_mk_eq ?_
  have e : Arrow.mk (J.hom ((DHom.mk (Diagram.copyWordD G w c)).cast
      (Diagram.copyWordD_domWord G w c) (Diagram.copyWordD_codWord G w c))) =
      Arrow.mk (J.hom (DHom.mk (Diagram.copyD G (Diagram.letters w) c))) :=
    J.arrow_eq_of_cls_eq rfl
  refine (J.projM.mk_map_congr e).trans ((J.projM_copyD (Diagram.letters w) c).trans ?_)
  rw [Diagram.ofList_map_letters]
  rfl

/-- **The diagram of discards represents `ε_a`.** -/
theorem projM_discardD (a : Fin n → S) :
    Arrow.mk (J.projM.map (J.hom (DHom.mk (Diagram.discardD G a)))) =
      Arrow.mk (J.discardM (J.wordM (FreeMonoid.ofList ((List.finRange n).map a)))) :=
  congrArg Arrow.mk
    (eq_discard (C := J.FsM) (J.projM.map (J.hom (DHom.mk (Diagram.discardD G a)))))

/-- **`ε_w` is the class of the diagram of discards**, for a word `w`. -/
theorem projM_discardWordD (w : FreeMonoid S) :
    J.projM.map (J.hom ((DHom.mk (Diagram.discardWordD G w)).cast
        (Diagram.discardWordD_domWord G w) rfl)) = J.discardM (J.wordM w) :=
  eq_discard (C := J.FsM) _

end JoyalStreet

/-! ### Unconditional forms -/

namespace Combinatorial

variable {S : Type w} (G : FreeDDGraphMonoid.{w, v} S)

/-- **The diagram `Γ` represents `δ_w`**, unconditional: in the free Markov category
`F_s(G)/S_M` of the combinatorial diagrams, the class of the diagram `Γ` of `δ_w` (one duplicate
per letter, codomain ordered as `w w`) is the duplicate on `w`, for every order of the prongs. -/
theorem copy_diagram (w : FreeMonoid S) (c : Fin (Diagram.wlen w) → Bool) :
    (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).projM.map
        ((JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).hom
          ((DHom.mk (Diagram.copyWordD G w c)).cast
            (Diagram.copyWordD_domWord G w c) (Diagram.copyWordD_codWord G w c))) =
      (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).copyM
        ((JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).wordM w) :=
  (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).projM_copyWordD w c

/-- **The diagram of discards represents `ε_w`**, unconditional. -/
theorem discard_diagram (w : FreeMonoid S) :
    (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).projM.map
        ((JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).hom
          ((DHom.mk (Diagram.discardWordD G w)).cast (Diagram.discardWordD_domWord G w) rfl)) =
      (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).discardM
        ((JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).wordM w) :=
  (JoyalStreet.ofCombinatorial G.toFreeGraphMonoid).projM_discardWordD w

end Combinatorial

end FreeMarkov
