/-
Free Markov categories, Stage 7: every class of diagrams is the image of a formal composite
(the comparison map `Syn_s(G) → F_s(G)` is surjective; generation of `F_s(G)`).

* node-free diagrams are composites of symmetries and identities (`inIm_nodeFree`): bring the
  wires into the order of the codomain one at a time;
* a diagram with nodes is `[P] ∘ ([x] ⊗ 1) ∘ [Γ']` for a minimal node `x`, a node-free `P` and
  the layer `Γ'` above `x` (`mk_eq_first_node`), by an embedding into `Γ`; induction on the
  number of nodes.

No cited result is used.
-/
module

public import FreeMarkov.Stage7.FsCat
public import FreeMarkov.Stage7.Perm
public import FreeMarkov.Stage2.Gluing

@[expose] public section

universe w v

namespace FreeMarkov

open CategoryTheory StrictSMC FreeGraphMonoid Diagram

namespace DClass

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-- The classes that are images of formal composites. -/
def InIm (c : DClass G) : Prop :=
  ∃ (a b : FreeMonoid S) (f : Syn.of G a ⟶ Syn.of G b), (FsC.toDHom f).1 = c

theorem InIm.comp {c d : DClass G} (hc : c.InIm) (hd : d.InIm) (h : c.cod = d.dom) :
    (c.comp d).InIm := by
  obtain ⟨a, b, f, rfl⟩ := hc
  obtain ⟨b', e, g, rfl⟩ := hd
  have hb : b = b' := (FsC.toDHom f).2.2.symm.trans (h.trans (FsC.toDHom g).2.1)
  subst hb
  exact ⟨a, e, f ≫ g, congrArg Subtype.val (FsC.toDHom_comp f g)⟩

theorem InIm.tensor {c d : DClass G} (hc : c.InIm) (hd : d.InIm) : (c.tensor d).InIm := by
  obtain ⟨a, b, f, rfl⟩ := hc
  obtain ⟨a', b', g, rfl⟩ := hd
  exact ⟨a * a', b * b', f ⊗ₛ g, congrArg Subtype.val (FsC.toDHom_tensor f g)⟩

theorem inIm_gen (x : G.A) : (mk (oneNode x)).InIm :=
  ⟨_, _, Syn.gen x, congrArg Subtype.val (FsC.toDHom_gen x)⟩

theorem inIm_idD (a : FreeMonoid S) : (mk (idD G a)).InIm :=
  ⟨a, a, 𝟙 (Syn.of G a), congrArg Subtype.val (FsC.toDHom_id a)⟩

theorem inIm_braidD (a b : FreeMonoid S) : (mk (braidD G a b)).InIm :=
  ⟨a * b, b * a, _, congrArg Subtype.val (FsC.toDHom_braid (G := G) a b)⟩

/-! ### Node-free diagrams -/

section NodeFree

variable {E : Type} [Finite E] (v₀ : E → S)

omit [Finite E] in
theorem card_eq_length_of_full {d : List E} (hd : d.Nodup) (hd' : ∀ e, e ∈ d) [Finite E] :
    Nat.card E = d.length := by
  rw [← Nat.card_subtype_true]
  exact Enumeration.card_eq_length ⟨d, hd, fun e => iff_of_true (hd' e) trivial⟩

/-- The word of a list of labelled edges. -/
def wrd (l : List E) : FreeMonoid S := FreeMonoid.ofList (l.map v₀)

omit [Finite E] in
theorem toList_wrd (l : List E) : FreeMonoid.toList (wrd v₀ l) = l.map v₀ := rfl

omit [Finite E] in
@[simp] theorem wlen_wrd (l : List E) : wlen (wrd v₀ l) = l.length := by
  simp [wlen, toList_wrd]

/-- A node-free diagram on all of `E`, from the ordering `d` to the ordering `c`. -/
def nf (d c : List E) (hd : d.Nodup) (hd' : ∀ e, e ∈ d) (hc : c.Nodup) (hc' : ∀ e, e ∈ c) :
    Diagram G Empty E :=
  nodeFree v₀ d c hd hd' hc hc'

/-- The embedding of a node-free diagram on `E` into another one with the same labels. -/
def nfEmb {d c d' c' : List E} {hd hd' hc hc' kd kd' kc kc'} :
    PEmb (nf (G := G) v₀ d c hd hd' hc hc') (nf (G := G) v₀ d' c' kd kd' kc kc') where
  ιN := Empty.elim
  ιE := id
  injN x := x.elim
  injE := Function.injective_id
  ins x := x.elim
  outs x := x.elim
  v₀ _ := rfl
  v₁ x := x.elim

theorem mk_nf_self (d : List E) (hd : d.Nodup) (hd' : ∀ e, e ∈ d) :
    (mk (nf (G := G) v₀ d d hd hd' hd hd')).InIm := by
  have hv : d.map (nf (G := G) v₀ d d hd hd' hd hd').val.v₀ = FreeMonoid.toList (wrd v₀ d) := rfl
  have e := (PEmb.idD (X := nf (G := G) v₀ d d hd hd' hd hd') (wrd v₀ d) d hd hv).mk_eq
    (by simp) (by
      rw [card_eq_length_of_full hd hd']
      simp [wlen, toList_wrd])
    (PEmb.idD_dom _ _ _ _) (PEmb.idD_cod _ _ _ _)
  rw [← e]
  exact inIm_idD _

/-- One step of sorting: bring `e` from behind `t₁` to the front of the unsorted part. -/
theorem mk_nf_step (P t₁ t₂ c : List E) (e : E) (hd : (P ++ t₁ ++ e :: t₂).Nodup)
    (hd' : ∀ f, f ∈ P ++ t₁ ++ e :: t₂) (hc : c.Nodup) (hc' : ∀ f, f ∈ c)
    (hd₂ : (P ++ e :: (t₁ ++ t₂)).Nodup) (hd₂' : ∀ f, f ∈ P ++ e :: (t₁ ++ t₂)) :
    mk (nf (G := G) v₀ (P ++ t₁ ++ e :: t₂) c hd hd' hc hc') =
      (mk ((idD G (wrd v₀ P)).tensor ((braidD G (wrd v₀ t₁) (wrd v₀ [e])).tensor
        (idD G (wrd v₀ t₂))))).comp (mk (nf (G := G) v₀ (P ++ e :: (t₁ ++ t₂)) c hd₂ hd₂' hc hc')) := by
  set X := nf (G := G) v₀ (P ++ t₁ ++ e :: t₂) c hd hd' hc hc'
  have hX : X.dom = P ++ t₁ ++ e :: t₂ := rfl
  have n₁ : (P ++ (t₁ ++ ([e] ++ t₂))).Nodup := by simpa using hd
  have nP : P.Nodup := n₁.sublist (by simp)
  have n₂ : (t₁ ++ [e]).Nodup := n₁.sublist (by simp)
  have nt₂ : t₂.Nodup := n₁.sublist (by
    simpa using ((List.sublist_cons_self e t₂).trans (List.sublist_append_right t₁ _)).trans
      (List.sublist_append_right P _))
  have dP : ∀ a ∈ P, ∀ b ∈ t₁ ++ ([e] ++ t₂), a ≠ b := (List.nodup_append.1 n₁).2.2
  have dT : ∀ a ∈ t₁ ++ [e], ∀ b ∈ t₂, a ≠ b := by
    have : (t₁ ++ [e] ++ t₂).Nodup := by simpa using (List.nodup_append.1 n₁).2.1
    exact (List.nodup_append.1 this).2.2
  let eB := PEmb.braidD (X := X) (wrd v₀ t₁) (wrd v₀ [e]) t₁ [e] n₂ rfl rfl
  let eT := PEmb.idD (X := X) (wrd v₀ t₂) t₂ nt₂ rfl
  let eBT := PEmb.tensor eB eT (fun z => z.elim) (fun d d' => dT _
    (PEmb.braidD_ιE_mem _ _ _ _ _ _ _ d) _ (PEmb.idD_ιE_mem _ _ _ _ d'))
  let eP := PEmb.idD (X := X) (wrd v₀ P) P nP rfl
  have mBT : ∀ d, eBT.ιE d ∈ t₁ ++ ([e] ++ t₂) := by
    rintro (d | d)
    · have := PEmb.braidD_ιE_mem (X := X) (wrd v₀ t₁) (wrd v₀ [e]) t₁ [e] n₂ rfl rfl d
      simp only [List.mem_append] at this ⊢; tauto
    · have := PEmb.idD_ιE_mem (X := X) (wrd v₀ t₂) t₂ nt₂ rfl d
      simp only [List.mem_append] at this ⊢; tauto
  let eS := PEmb.tensor eP eBT (fun z => z.elim) (fun d d' => dP _ (PEmb.idD_ιE_mem _ _ _ _ d) _
    (mBT d'))
  have b₁ : (braidD G (wrd v₀ t₁) (wrd v₀ [e])).cod.map eB.ιE = [e] ++ t₁ :=
    PEmb.braidD_cod _ _ _ _ _ _ _
  have b₂ : (braidD G (wrd v₀ t₁) (wrd v₀ [e])).dom.map eB.ιE = t₁ ++ [e] :=
    PEmb.braidD_dom _ _ _ _ _ _ _
  have i₁ : (idD G (wrd v₀ t₂)).cod.map eT.ιE = t₂ := PEmb.idD_cod _ _ _ _
  have i₂ : (idD G (wrd v₀ t₂)).dom.map eT.ιE = t₂ := PEmb.idD_dom _ _ _ _
  have j₁ : (idD G (wrd v₀ P)).cod.map eP.ιE = P := PEmb.idD_cod _ _ _ _
  have j₂ : (idD G (wrd v₀ P)).dom.map eP.ιE = P := PEmb.idD_dom _ _ _ _
  have kc : ((idD G (wrd v₀ P)).tensor ((braidD G (wrd v₀ t₁) (wrd v₀ [e])).tensor
      (idD G (wrd v₀ t₂)))).cod.map eS.ιE = P ++ e :: (t₁ ++ t₂) := by
    refine (PEmb.tensor_cod _ _ _ _).trans ?_
    have k₁ : ((braidD G (wrd v₀ t₁) (wrd v₀ [e])).tensor (idD G (wrd v₀ t₂))).cod.map eBT.ιE =
        ([e] ++ t₁) ++ t₂ := (PEmb.tensor_cod _ _ _ _).trans (by rw [b₁, i₁])
    rw [j₁, k₁]; simp
  have kd : ((idD G (wrd v₀ P)).tensor ((braidD G (wrd v₀ t₁) (wrd v₀ [e])).tensor
      (idD G (wrd v₀ t₂)))).dom.map eS.ιE = P ++ t₁ ++ e :: t₂ := by
    refine (PEmb.tensor_dom _ _ _ _).trans ?_
    have k₁ : ((braidD G (wrd v₀ t₁) (wrd v₀ [e])).tensor (idD G (wrd v₀ t₂))).dom.map eBT.ιE =
        (t₁ ++ [e]) ++ t₂ := (PEmb.tensor_dom _ _ _ _).trans (by rw [b₂, i₂])
    rw [j₂, k₁]; simp
  have h : ((idD G (wrd v₀ P)).tensor ((braidD G (wrd v₀ t₁) (wrd v₀ [e])).tensor
      (idD G (wrd v₀ t₂)))).codWord = (nf (G := G) v₀ (P ++ e :: (t₁ ++ t₂)) c hd₂ hd₂' hc hc').domWord := by
    simp [wrd, nf, nodeFree, domWord, FreeMonoid.ofList_append, mul_assoc]
  let eY : PEmb (nf (G := G) v₀ (P ++ e :: (t₁ ++ t₂)) c hd₂ hd₂' hc hc') X := nfEmb v₀
  let eG := PEmb.glueS eS eY h (by rw [kc]; exact (List.map_id _).symm) (fun _ z => z.elim)
    (fun _ _ z => z.elim)
  rw [mk_comp _ _ h]
  refine (eG.mk_eq ?_ ?_ ?_ ?_).symm
  · simp
  · have c₁ := card_glue_edges _ (nf (G := G) v₀ (P ++ e :: (t₁ ++ t₂)) c hd₂ hd₂' hc hc') h
    have cE : Nat.card E = (P ++ t₁ ++ e :: t₂).length := card_eq_length_of_full hd hd'
    have cY : (nf (G := G) v₀ (P ++ e :: (t₁ ++ t₂)) c hd₂ hd₂' hc hc').dom.length =
        (P ++ t₁ ++ e :: t₂).length := by simp [nf, nodeFree]; omega
    simp only [Nat.card_sum, Nat.card_fin, wlen_wrd] at c₁ ⊢
    simp only [List.length_append, List.length_cons] at cE cY c₁ ⊢
    omega
  · exact (PEmb.glueS_dom _ _ _ _ _ _).trans kd
  · exact (PEmb.glueS_cod _ _ _ _ _ _).trans (List.map_id _)

theorem mk_nf_congr {d₁ d₂ c₁ c₂ : List E} (hd : d₁ = d₂) (hc : c₁ = c₂) {p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄} :
    mk (nf (G := G) v₀ d₁ c₁ p₁ p₂ p₃ p₄) = mk (nf (G := G) v₀ d₂ c₂ q₁ q₂ q₃ q₄) := by
  subst hd hc; rfl

/-- Every node-free diagram on all of `E` is a composite of identities and symmetries. -/
theorem inIm_nf : ∀ (c' P d' : List E) (hd : (P ++ d').Nodup) (hd' : ∀ e, e ∈ P ++ d')
    (hc : (P ++ c').Nodup) (hc' : ∀ e, e ∈ P ++ c'), d'.Perm c' →
    (mk (nf (G := G) v₀ (P ++ d') (P ++ c') hd hd' hc hc')).InIm := by
  classical
  intro c'
  induction c' with
  | nil =>
    intro P d' hd hd' hc hc' hp
    obtain rfl := List.perm_nil.1 hp
    exact mk_nf_self v₀ (P ++ []) hd hd'
  | cons e c'' ih =>
    intro P d' hd hd' hc hc' hp
    have he : e ∈ d' := hp.symm.subset (List.mem_cons_self ..)
    obtain ⟨t₁, t₂, rfl, ht⟩ := Wires.split_first he
    have l₁ : P ++ (t₁ ++ e :: t₂) = P ++ t₁ ++ e :: t₂ := by simp
    have hd₁ : (P ++ t₁ ++ e :: t₂).Nodup := l₁ ▸ hd
    have hd₁' : ∀ f, f ∈ P ++ t₁ ++ e :: t₂ := fun f => l₁ ▸ hd' f
    have pr : (P ++ (t₁ ++ e :: t₂)).Perm (P ++ e :: (t₁ ++ t₂)) :=
      List.Perm.append_left _ List.perm_middle
    have hd₂ : (P ++ e :: (t₁ ++ t₂)).Nodup := pr.nodup_iff.1 hd
    have hd₂' : ∀ f, f ∈ P ++ e :: (t₁ ++ t₂) := fun f => pr.subset (hd' f)
    rw [mk_nf_congr v₀ l₁ rfl (q₁ := hd₁) (q₂ := hd₁') (q₃ := hc) (q₄ := hc'),
      mk_nf_step v₀ P t₁ t₂ _ e hd₁ hd₁' hc hc' hd₂ hd₂']
    have hs := InIm.tensor (inIm_idD (G := G) (wrd v₀ P)) (InIm.tensor
      (inIm_braidD (G := G) (wrd v₀ t₁) (wrd v₀ [e])) (inIm_idD (G := G) (wrd v₀ t₂)))
    rw [mk_tensor, mk_tensor] at hs
    refine InIm.comp hs ?_ ?_
    · have l₂ : (P ++ [e]) ++ (t₁ ++ t₂) = P ++ e :: (t₁ ++ t₂) := by simp
      have l₃ : (P ++ [e]) ++ c'' = P ++ e :: c'' := by simp
      have k := ih (P ++ [e]) (t₁ ++ t₂) (l₂ ▸ hd₂) (fun f => l₂ ▸ hd₂' f) (l₃ ▸ hc)
        (fun f => l₃ ▸ hc' f) (by simpa using (List.perm_middle.symm.trans hp).cons_inv)
      rwa [mk_nf_congr v₀ l₂ l₃ (q₁ := hd₂) (q₂ := hd₂') (q₃ := hc) (q₄ := hc')] at k
    · rw [cod_mk, dom_mk, tensor_codWord, tensor_codWord, idD_codWord, idD_codWord, braidD_codWord]
      show _ = FreeMonoid.ofList ((P ++ e :: (t₁ ++ t₂)).map v₀)
      simp only [wrd, List.map_append, List.map_cons, List.map_nil, FreeMonoid.ofList_append,
        FreeMonoid.ofList_cons, FreeMonoid.ofList_nil, mul_one, mul_assoc]

end NodeFree

/-- **Node-free diagrams** are composites of identities and symmetries. -/
theorem inIm_nodeFree {N E : Type} [IsEmpty N] [Fintype N] [Finite E] (Γ : Diagram G N E) :
    (mk Γ).InIm := by
  have hs : ∀ e, Γ.src e = none := fun e => by
    cases h : Γ.src e with
    | none => rfl
    | some x => exact isEmptyElim x
  have ht : ∀ e, Γ.tgt e = none := fun e => by
    cases h : Γ.tgt e with
    | none => rfl
    | some x => exact isEmptyElim x
  have hd' : ∀ e, e ∈ Γ.dom := fun e => (Γ.mem_dom e).2 (hs e)
  have hc' : ∀ e, e ∈ Γ.cod := fun e => (Γ.mem_cod e).2 (ht e)
  let e : PEmb (nf (G := G) Γ.val.v₀ Γ.dom Γ.cod Γ.dom_nodup hd' Γ.cod_nodup hc') Γ :=
    { ιN := Empty.elim
      ιE := id
      injN := fun x => x.elim
      injE := Function.injective_id
      ins := fun x => x.elim
      outs := fun x => x.elim
      v₀ := fun _ => rfl
      v₁ := fun x => x.elim }
  rw [← e.mk_eq (by simp) le_rfl (List.map_id _) (List.map_id _)]
  have k := inIm_nf (G := G) Γ.val.v₀ Γ.cod [] Γ.dom Γ.dom_nodup hd' Γ.cod_nodup hc'
    ((List.perm_ext_iff_of_nodup Γ.dom_nodup Γ.cod_nodup).2 fun f => iff_of_true (hd' f) (hc' f))
  exact k

/-! ### Peeling off a minimal node -/

section FirstNode

open Classical in
/-- **Surjectivity of the comparison map** (generation of `F_s(G)`): every class of diagrams
on finite types in `Type` is the image of a formal composite. -/
theorem inIm_of_card : ∀ (n : ℕ) {N E : Type} [Fintype N] [Finite E] (Γ : Diagram G N E),
    Nat.card N = n → (mk Γ).InIm := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N E _ _ Γ hn
  rcases isEmpty_or_nonempty N with hN | hN
  · exact inIm_nodeFree Γ
  -- a minimal node
  have : IsTrans N Γ.Lt := ⟨fun _ _ _ => Γ.lt_trans⟩
  have : Std.Irrefl Γ.Lt := ⟨Γ.lt_irrefl⟩
  obtain ⟨x, -, hmin⟩ := (Finite.wellFounded_of_trans_of_irrefl Γ.Lt).has_min Set.univ
    Set.univ_nonempty
  have hmin' : ∀ z, ¬ Γ.Lt z x := fun z => hmin z (Set.mem_univ z)
  have hIs : ∀ e ∈ Γ.ins x, Γ.src e = none := by
    intro e he
    cases hs : Γ.src e with
    | none => rfl
    | some z => exact absurd (Γ.lt_of_edge hs ((Γ.mem_ins x e).1 he)) (hmin' z)
  -- the pieces
  set R : List E := Γ.dom.filter (fun e => decide (e ∉ Γ.ins x)) with hR
  have hRn : R.Nodup := Γ.dom_nodup.filter _
  have hmR : ∀ e, e ∈ R ↔ Γ.src e = none ∧ e ∉ Γ.ins x := by
    intro e; simp [hR, Γ.mem_dom]
  have hIR : (Γ.ins x ++ R).Nodup := List.nodup_append.2 ⟨Γ.ins_nodup x, hRn,
    fun a ha b hb hab => ((hmR b).1 hb).2 (hab ▸ ha)⟩
  have hOR : (Γ.outs x ++ R).Nodup := List.nodup_append.2 ⟨Γ.outs_nodup x, hRn,
    fun a ha b hb hab => by
      have h₁ := (Γ.mem_outs x a).1 ha
      rw [hab, ((hmR b).1 hb).1] at h₁
      cases h₁⟩
  -- the level `{x}` and the ordering of its cut
  have hL : Γ.IsLevel {x} := fun y z hyz hz => by
    rw [Set.mem_singleton_iff] at hz; subst hz; exact absurd hyz (hmin' y)
  have hcut : ∀ e, e ∈ Γ.outs x ++ R ↔ Γ.Cut {x} e := by
    intro e
    rw [List.mem_append, Γ.mem_outs, hmR]
    unfold PGraph.Cut PGraph.SrcIn PGraph.TgtIn
    constructor
    · rintro (h | ⟨h₁, h₂⟩)
      · refine ⟨fun z hz => ?_, fun y hy hyx => ?_⟩
        · rw [h] at hz; cases hz; rfl
        · rw [Set.mem_singleton_iff] at hyx; subst hyx
          exact Γ.lt_irrefl _ (Γ.lt_of_edge h hy)
      · refine ⟨fun z hz => ?_, fun y hy hyx => ?_⟩
        · rw [h₁] at hz; cases hz
        · rw [Set.mem_singleton_iff] at hyx; subst hyx
          exact h₂ ((Γ.mem_ins _ e).2 hy)
    · rintro ⟨h₁, h₂⟩
      cases hs : Γ.src e with
      | none =>
        right
        exact ⟨rfl, fun he => h₂ x ((Γ.mem_ins x e).1 he) rfl⟩
      | some z =>
        left
        have := h₁ z hs
        rw [Set.mem_singleton_iff] at this
        rw [this]
  let oL : Enumeration (Γ.Cut {x}) := ⟨Γ.outs x ++ R, hOR, hcut⟩
  set U := Γ.upperD hL oL with hU
  -- the node-free piece `P` on the domain edges
  have hmD : ∀ e, e ∈ Γ.ins x ++ R ↔ Γ.IsDom e := by
    intro e
    rw [List.mem_append, hmR]
    constructor
    · rintro (h | h)
      · exact hIs e h
      · exact h.1
    · intro h
      by_cases hi : e ∈ Γ.ins x
      · exact Or.inl hi
      · exact Or.inr ⟨h, hi⟩
  let oD : Enumeration Γ.IsDom := ⟨Γ.ins x ++ R, hIR, hmD⟩
  set P := nf (G := G) (fun e : {e // Γ.IsDom e} => Γ.val.v₀ e.1) Γ.domEnum.sub oD.sub
    (Enumeration.nodup_sub _) (Enumeration.mem_sub _) (Enumeration.nodup_sub _)
    (Enumeration.mem_sub _) with hP
  let eP : PEmb P Γ :=
    { ιN := Empty.elim
      ιE := Subtype.val
      injN := fun z => z.elim
      injE := Subtype.val_injective
      ins := fun z => z.elim
      outs := fun z => z.elim
      v₀ := fun _ => rfl
      v₁ := fun z => z.elim }
  have kP₁ : P.dom.map eP.ιE = Γ.dom := Enumeration.sub_map_val Γ.domEnum
  have kP₂ : P.cod.map eP.ιE = Γ.ins x ++ R := Enumeration.sub_map_val oD
  -- the one-node piece `Q`
  set Q := (oneNode (Γ.val.v₁ x)).tensor (idD G (FreeMonoid.ofList (R.map Γ.val.v₀))) with hQ
  let eO := PEmb.oneNode (X := Γ) x rfl
  let eI := PEmb.idD (X := Γ) (FreeMonoid.ofList (R.map Γ.val.v₀)) R hRn rfl
  have mO : ∀ d, eO.ιE d ∈ Γ.ins x ∨ eO.ιE d ∈ Γ.outs x := by
    rintro (i | j)
    · exact Or.inl (List.getElem_mem _)
    · exact Or.inr (List.getElem_mem _)
  have hEQ : ∀ d d', eO.ιE d ≠ eI.ιE d' := by
    intro d d' hdd
    have hmem : eI.ιE d' ∈ R := PEmb.idD_ιE_mem (X := Γ) _ R hRn rfl d'
    have hR' := (hmR _).1 hmem
    rcases mO d with h | h
    · exact hR'.2 (hdd ▸ h)
    · have := (Γ.mem_outs x _).1 h
      rw [hdd, hR'.1] at this; cases this
  let eQ := PEmb.tensor eO eI (fun _ z => z.elim) hEQ
  have i₁ : (idD G (FreeMonoid.ofList (R.map Γ.val.v₀))).dom.map eI.ιE = R :=
    PEmb.idD_dom _ _ _ _
  have i₂ : (idD G (FreeMonoid.ofList (R.map Γ.val.v₀))).cod.map eI.ιE = R :=
    PEmb.idD_cod _ _ _ _
  have kQ₁ : Q.dom.map eQ.ιE = Γ.ins x ++ R := by
    refine (PEmb.tensor_dom _ _ _ _).trans ?_
    rw [PEmb.oneNode_dom, i₁]
  have kQ₂ : Q.cod.map eQ.ιE = Γ.outs x ++ R := by
    refine (PEmb.tensor_cod _ _ _ _).trans ?_
    rw [PEmb.oneNode_cod, i₂]
  -- gluing `P`, `Q`, `U`
  have h₁ : P.codWord = Q.domWord := by
    rw [hQ, tensor_domWord, oneNode_domWord, idD_domWord, Γ.val.s_v₁]
    show FreeMonoid.ofList (oD.sub.map (Γ.val.v₀ ∘ Subtype.val)) = _
    rw [← List.map_map, Enumeration.sub_map_val]
    show FreeMonoid.ofList ((Γ.ins x ++ R).map Γ.val.v₀) = _
    rw [List.map_append, FreeMonoid.ofList_append]
  let e₁ := PEmb.glueS eP eQ h₁ (kP₂.trans kQ₁.symm) (fun z => z.elim)
    (fun d _ z => by rw [show Γ.src (eP.ιE d) = none from d.2]; simp)
  have h₂ : (P.glue Q h₁).codWord = U.domWord := by
    rw [glue_codWord, hQ, tensor_codWord, oneNode_codWord, idD_codWord, Γ.val.t_v₁, hU,
      Γ.layerD_domWord]
    show _ = FreeMonoid.ofList ((Γ.outs x ++ R).map Γ.val.v₀)
    rw [List.map_append, FreeMonoid.ofList_append]
  let eU : PEmb U Γ :=
    { ιN := Subtype.val
      ιE := Subtype.val
      injN := Subtype.val_injective
      injE := Subtype.val_injective
      ins := fun y => (Γ.ins_map_val_layerD hL Γ.isLevel_univ _ oL Γ.cutUnivEnum y).symm
      outs := fun y => (Γ.outs_map_val_layerD hL Γ.isLevel_univ _ oL Γ.cutUnivEnum y).symm
      v₀ := fun _ => rfl
      v₁ := fun _ => rfl }
  have kU₁ : U.dom.map eU.ιE = Γ.outs x ++ R := Γ.layerD_dom_map_val _ _ _ _ _
  have kU₂ : U.cod.map eU.ιE = Γ.cod := Γ.layerD_cod_map_val _ _ _ _ _
  have k₁ : (P.glue Q h₁).cod.map e₁.ιE = Γ.outs x ++ R :=
    (PEmb.glueS_cod _ _ _ _ _ _).trans kQ₂
  have hN₂ : ∀ z z', e₁.ιN z ≠ eU.ιN z' := by
    rintro (z | (z | z)) z' h
    · exact z.elim
    · exact z'.2.2 (by simpa [e₁, eQ, eO, eU, PEmb.glueS, PEmb.glue, PEmb.tensor,
        PEmb.oneNode] using h.symm)
    · exact z.elim
  have hdom₂ : ∀ d, (P.glue Q h₁).src d = none → ∀ z, Γ.src (e₁.ιE d) ≠ some (eU.ιN z) := by
    rintro (d | d) hd z
    · show Γ.src d.1 ≠ _
      rw [show Γ.src d.1 = none from d.2]; simp
    · exact absurd (by simpa [Diagram.glue, AGraph.glue] using hd) d.2
  let eG := PEmb.glueS e₁ eU h₂ (k₁.trans kU₁.symm) hN₂ hdom₂
  -- counting
  have hNx : Nat.card {y // Γ.LayerNode {x} Set.univ y} + 1 = Nat.card N := by
    have e₁ : {y // Γ.LayerNode {x} Set.univ y} ≃ {y // ¬ y = x} :=
      Equiv.subtypeEquivRight fun y => by simp [PGraph.LayerNode]
    have h1 : Nat.card {y // y = x} = 1 :=
      Nat.card_eq_one_iff_exists.2 ⟨⟨x, rfl⟩, fun ⟨y, hy⟩ => Subtype.ext hy⟩
    rw [Nat.card_congr e₁, ← card_subtype_add_card_not (fun y => y = x), h1]
    omega
  have hUE : Nat.card {e // Γ.LayerEdge {x} Set.univ e} + (Γ.ins x).length = Nat.card E := by
    have e₂ : {e // Γ.LayerEdge {x} Set.univ e} ≃ {e // ¬ e ∈ Γ.ins x} :=
      Equiv.subtypeEquivRight fun e => by
        rw [Γ.mem_ins]
        unfold PGraph.LayerEdge PGraph.SrcIn PGraph.TgtIn
        simp only [Set.mem_univ, implies_true, true_and, Set.mem_compl_iff,
          Set.mem_singleton_iff]
        exact ⟨fun h h' => h x h' rfl, fun h y hy hyx => h (hyx ▸ hy)⟩
    have h1 : Nat.card {e // e ∈ Γ.ins x} = (Γ.ins x).length :=
      Enumeration.card_eq_length ⟨Γ.ins x, Γ.ins_nodup x, fun _ => Iff.rfl⟩
    rw [Nat.card_congr e₂, ← card_subtype_add_card_not (fun e => e ∈ Γ.ins x), h1]
    omega
  have hdl : Γ.dom.length = (Γ.ins x).length + R.length := by
    have := (Γ.domEnum.card_eq_length).symm.trans oD.card_eq_length
    exact this.trans (List.length_append ..)
  have hPE : Nat.card {e // Γ.IsDom e} = Γ.dom.length := Γ.domEnum.card_eq_length
  have hQd : Q.dom.length = (Γ.ins x).length + R.length := by
    rw [← List.length_map (f := eQ.ιE), kQ₁, List.length_append]
  have hUd : U.dom.length = (Γ.outs x).length + R.length := by
    rw [← List.length_map (f := eU.ιE), kU₁, List.length_append]
  have hs : wlen (G.s (Γ.val.v₁ x)) = (Γ.ins x).length := by rw [Γ.val.s_v₁]; simp [wlen]
  have ht : wlen (G.t (Γ.val.v₁ x)) = (Γ.outs x).length := by rw [Γ.val.t_v₁]; simp [wlen]
  have hr : wlen (FreeMonoid.ofList (R.map Γ.val.v₀)) = R.length := by simp [wlen]
  have cG₁ := card_glue_edges P Q h₁
  have cG₂ := card_glue_edges (P.glue Q h₁) U h₂
  have hmk : mk Γ = ((mk P).comp (mk Q)).comp (mk U) := by
    rw [mk_comp _ _ h₁, mk_comp _ _ h₂]
    refine (eG.mk_eq ?_ ?_ ?_ ?_).symm
    · simp only [Nat.card_sum, Nat.card_unique]; omega
    · simp only [Nat.card_sum, Nat.card_fin] at cG₁ cG₂ ⊢
      show Nat.card E ≤ Nat.card {e // Γ.IsDom e} + Nat.card Q.InnerSrc + Nat.card U.InnerSrc
      omega
    · exact (PEmb.glueS_dom _ _ _ _ _ _).trans ((PEmb.glueS_dom _ _ _ _ _ _).trans kP₁)
    · exact (PEmb.glueS_cod _ _ _ _ _ _).trans kU₂
  have hQ' : (mk Q).InIm := by
    rw [hQ, ← mk_tensor]; exact InIm.tensor (inIm_gen _) (inIm_idD _)
  rw [hmk]
  refine InIm.comp (InIm.comp (inIm_nodeFree P) hQ' (by rw [cod_mk, dom_mk]; exact h₁))
    (ih _ (by omega) U rfl) ?_
  rw [mk_comp _ _ h₁, cod_mk, dom_mk]; exact h₂

end FirstNode

end DClass

namespace FsC

variable {S : Type w} {G : FreeGraphMonoid.{w, v} S}

/-- The comparison map `Syn_s(G)(a, b) → {[Γ, v] : dom = a, cod = b}` is surjective. -/
theorem toDHom_surjective {a b : FreeMonoid S} :
    Function.Surjective (toDHom (G := G) (a := a) (b := b)) := by
  intro f
  obtain ⟨n, m, Γ, hΓ⟩ := DClass.exists_eq_mk f.1
  obtain ⟨a', b', g, hg⟩ := DClass.inIm_of_card _ Γ rfl
  rw [← hΓ] at hg
  have ha : a' = a := (toDHom g).2.1.symm.trans ((congrArg DClass.dom hg).trans f.2.1)
  have hb : b' = b := (toDHom g).2.2.symm.trans ((congrArg DClass.cod hg).trans f.2.2)
  subst ha hb
  exact ⟨g, Subtype.ext hg⟩

end FsC

end FreeMarkov
