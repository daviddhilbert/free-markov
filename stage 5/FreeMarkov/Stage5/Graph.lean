/-
Free Markov categories, Stage 5: finite directed acyclic graphs with identity loops (`FinDAG`), the
directed graph associated with a family `K = (S_i, κ_i)`, the subgraphs `G_{S → T}`, and the graph
theory of Lemma 5.5.

* `FinDAG`: finite directed graphs with exactly one loop at each vertex (the identity loop) and no
  cycle (a cycle does not contain loops), with graph homomorphisms as morphisms; `FinDAG.terminal`,
  the one-vertex graph, is terminal (`FinDAG.isTerminal`).
* `EffSig n`: the sets `S_i ⊆ {1, …, n}` with `i ∉ S_i`, whose associated directed graph (an arrow
  `j → i` iff `j ∈ S_i`) is acyclic; `EffSig.toFinDAG` is that graph with identity loops added.
* `EffSig.R S T`: the vertices of `G_{S → T}` outside `S`, i.e. the vertices not in `S` from which a
  directed path through vertices outside `S` ends in `T`; `EffSig.InD S T = S ∪ R S T` is the vertex
  set of `G_{S → T}`, and `EffSig.DArr S T` its arrows.
* Lemma 5.5, graph part: for `i ∈ R S T`, the ancestors `A` of `i` in `G_{S → T}`, the set `T_i`,
  `i ∈ T_i`, no child of `i` in `G_{S → T}` is a vertex of `G_{S → T_i}`, and
  `R S T_i = A ∖ S`, `R T_i T = R S T ∖ A`, so that `R S T` is the disjoint union of the two.

No cited result is used in this file.
-/
module

public import FreeMarkov.Stage5.Remarks

@[expose] public section

namespace FreeMarkov

open CategoryTheory Limits Relation

/-! ### `FinDAG` -/

/-- *Section 5.* An object of **`FinDAG`**: a finite directed graph `(V, A, s, t)` with exactly one
loop at each vertex, the **identity loop** `1_v`, which is acyclic: "a cycle in `G` does not contain
loops by definition", so the cycles are those of the arrows whose source and target differ. -/
structure FinDAG where
  /-- The vertices. -/
  V : Type
  /-- The arrows. -/
  A : Type
  [finV : Fintype V]
  [finA : Fintype A]
  /-- The source of an arrow. -/
  s : A → V
  /-- The target of an arrow. -/
  t : A → V
  /-- The identity loop on a vertex. -/
  loop : V → A
  s_loop (v : V) : s (loop v) = v
  t_loop (v : V) : t (loop v) = v
  /-- The identity loop is the only loop at its vertex. -/
  eq_loop (a : A) : s a = t a → a = loop (s a)
  /-- No cycle. -/
  acyclic (v : V) : ¬ TransGen (fun x y => ∃ a, s a = x ∧ t a = y ∧ x ≠ y) v v

namespace FinDAG

/-- A morphism of `FinDAG`: a graph homomorphism. -/
@[ext]
structure Hom (G H : FinDAG) where
  /-- The map on vertices. -/
  onV : G.V → H.V
  /-- The map on arrows. -/
  onA : G.A → H.A
  s_onA (a : G.A) : H.s (onA a) = onV (G.s a)
  t_onA (a : G.A) : H.t (onA a) = onV (G.t a)

/-- *Section 5.* "The category `FinDAG` has finite directed acyclic graphs with identity loops as
objects and graph homomorphisms between them as morphisms." -/
instance : Category FinDAG where
  Hom := Hom
  id G := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  comp f g := ⟨g.onV ∘ f.onV, g.onA ∘ f.onA, fun a => by simp [g.s_onA, f.s_onA],
    fun a => by simp [g.t_onA, f.t_onA]⟩

/-- A graph homomorphism sends identity loops to identity loops. -/
theorem Hom.onA_loop {G H : FinDAG} (f : G ⟶ H) (v : G.V) : f.onA (G.loop v) = H.loop (f.onV v) := by
  have h := H.eq_loop (f.onA (G.loop v)) (by rw [f.s_onA, f.t_onA, G.s_loop, G.t_loop])
  rw [h, f.s_onA, G.s_loop]

/-- The graph with one vertex and its identity loop. -/
def terminal : FinDAG where
  V := Unit
  A := Unit
  s _ := ()
  t _ := ()
  loop _ := ()
  s_loop _ := rfl
  t_loop _ := rfl
  eq_loop _ _ := rfl
  acyclic v h := by
    obtain ⟨a, -, -, hne⟩ : ∃ a : Unit, () = v ∧ () = v ∧ v ≠ v := by
      induction h with
      | single h => obtain ⟨a, h₁, h₂, h₃⟩ := h; exact ⟨a, rfl, rfl, fun _ => h₃ rfl⟩
      | tail _ _ ih => exact ih
    exact hne rfl

/-- *Section 5.* "The one-vertex graph is the terminal object in `FinDAG`, that is, every object in
`FinDAG` comes with exactly one morphism to it." -/
def isTerminal : IsTerminal terminal :=
  IsTerminal.ofUniqueHom (fun _ => ⟨fun _ => (), fun _ => (), fun _ => rfl, fun _ => rfl⟩)
    fun _ _ => Hom.ext rfl rfl

end FinDAG

/-! ### The directed graph of a family `K = (S_i, κ_i)` -/

/-- *Definition 5.4.* The sets `S_i ⊆ {1, …, n}` with `i ∉ S_i` of a family `K = (S_i, κ_i)`; the
associated directed graph has an arrow `j → i` iff `j ∈ S_i`, and it is assumed acyclic ("after
adding identity loops, we do assume `G ∈ FinDAG`"). -/
structure EffSig (n : ℕ) where
  /-- The set `S_i`. -/
  pa : Fin n → Finset (Fin n)
  not_mem_pa (i : Fin n) : i ∉ pa i
  /-- The associated directed graph is acyclic. -/
  acyclic (i : Fin n) : ¬ TransGen (fun j k => j ∈ pa k) i i

namespace EffSig

variable {n : ℕ} (K : EffSig n)

/-- The associated directed graph, with identity loops added, as an object of `FinDAG`. -/
def toFinDAG : FinDAG where
  V := Fin n
  A := Fin n ⊕ {p : Fin n × Fin n // p.1 ∈ K.pa p.2}
  s
    | .inl v => v
    | .inr p => p.1.1
  t
    | .inl v => v
    | .inr p => p.1.2
  loop v := .inl v
  s_loop _ := rfl
  t_loop _ := rfl
  eq_loop
    | .inl _, _ => rfl
    | .inr p, h => by
      change p.1.1 = p.1.2 at h
      exact absurd (h ▸ p.2) (K.not_mem_pa _)
  acyclic v h := K.acyclic v (by
    refine TransGen.mono (fun x y hxy => ?_) _ _ h
    obtain ⟨a, rfl, rfl, hne⟩ := hxy
    rcases a with a | p
    · exact absurd rfl hne
    · exact p.2)

theorem wellFounded : WellFounded fun j k : Fin n => j ∈ K.pa k := by
  have : IsTrans (Fin n) (TransGen fun j k => j ∈ K.pa k) := ⟨fun _ _ _ => TransGen.trans⟩
  have : Std.Irrefl (TransGen fun j k : Fin n => j ∈ K.pa k) := ⟨K.acyclic⟩
  exact Subrelation.wf (r := TransGen fun j k : Fin n => j ∈ K.pa k) (fun {_ _} h => TransGen.single h)
    (Finite.wellFounded_of_trans_of_irrefl _)

/-! ### `G_{S → T}` -/

variable (S T : Finset (Fin n))

/-- An arrow `j → k` whose target is outside `S`. -/
def Avoid (j k : Fin n) : Prop := j ∈ K.pa k ∧ k ∉ S

/-- *Definition 5.4.* The vertices of `G_{S → T}` outside `S`: "all the directed paths that end in
`T` but do not travel toward `S`, that is, do not pass through or end in `S` (starting in `S` is
allowed)"; a vertex outside `S` lies on such a path iff a directed path from it through vertices
outside `S` ends in `T`. -/
def R (i : Fin n) : Prop := i ∉ S ∧ ∃ t ∈ T, ReflTransGen (K.Avoid S) i t

/-- *Definition 5.4.* The vertices of `G_{S → T}`: those in `S ∪ T` and those on the directed paths
that end in `T` and do not travel toward `S`. -/
def InD (i : Fin n) : Prop := i ∈ S ∨ K.R S T i

/-- *Definition 5.4.* The arrows of `G_{S → T}` (identity loops disregarded): the arrows `j → k` of
the associated graph with `k` a vertex of `G_{S → T}` outside `S`.  The children of `j` in
`G_{S → T}` are "those `k ∈ V(G_{S → T}) ∖ S` with `j ∈ S_k`". -/
def DArr (j k : Fin n) : Prop := j ∈ K.pa k ∧ K.R S T k

variable {K S T}

theorem mem_T_inD {t : Fin n} (ht : t ∈ T) : K.InD S T t := by
  by_cases hS : t ∈ S
  · exact Or.inl hS
  · exact Or.inr ⟨hS, t, ht, ReflTransGen.refl⟩

/-- "For every `i ∈ V(G_{S → T})`, if `i ∉ S` then its parents in `G` are all in `G_{S → T}` as
well." -/
theorem inD_of_mem_pa {i j : Fin n} (hi : K.R S T i) (hj : j ∈ K.pa i) : K.InD S T j := by
  by_cases hS : j ∈ S
  · exact Or.inl hS
  · obtain ⟨hiS, t, ht, h⟩ := hi
    exact Or.inr ⟨hS, t, ht, ReflTransGen.head ⟨hj, hiS⟩ h⟩

/-- "If `i ∈ S` then it has no parents in `G_{S → T}`." -/
theorem not_dArr_of_mem {i j : Fin n} (hi : i ∈ S) : ¬ K.DArr S T j i := fun h => h.2.1 hi

theorem R_of_inD {i : Fin n} (h : K.InD S T i) (hS : i ∉ S) : K.R S T i := h.resolve_left hS

theorem dArr_avoid {j k : Fin n} (h : K.DArr S T j k) : K.Avoid S j k := ⟨h.1, h.2.1⟩

/-! ### Lemma 5.5: the graph part -/

variable (K S T) in
/-- *Lemma 5.5.* The ancestors of `i` in `D = G_{S → T}` ("vertices are ancestors of themselves"). -/
def Anc (i j : Fin n) : Prop := K.InD S T j ∧ ReflTransGen (K.DArr S T) j i

open Classical in
variable (K S T) in
/-- *Lemma 5.5.* `T_i = (A ∩ T) ∪ {j ∈ A : j has a child in G_{S → T} outside A} ∪ (S ∖ A)`. -/
noncomputable def Ti (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => (K.Anc S T i j ∧ j ∈ T) ∨
    (K.Anc S T i j ∧ ∃ k, K.DArr S T j k ∧ ¬ K.Anc S T i k) ∨ (j ∈ S ∧ ¬ K.Anc S T i j)

theorem mem_Ti {i j : Fin n} : j ∈ K.Ti S T i ↔ (K.Anc S T i j ∧ j ∈ T) ∨
    (K.Anc S T i j ∧ ∃ k, K.DArr S T j k ∧ ¬ K.Anc S T i k) ∨ (j ∈ S ∧ ¬ K.Anc S T i j) := by
  classical
  simp [Ti]

theorem not_dArrStar_of_dArr {i k : Fin n} (h : K.DArr S T i k) (h' : ReflTransGen (K.DArr S T) k i) :
    False := by
  have : TransGen (fun j k => j ∈ K.pa k) i i := by
    have h₁ : ReflTransGen (fun j k => j ∈ K.pa k) k i := ReflTransGen.mono (fun _ _ h => h.1) _ _ h'
    exact TransGen.head' h.1 h₁
  exact K.acyclic i this

theorem anc_of_avoid {i j k : Fin n} (hjk : K.Avoid S j k) (hk : K.Anc S T i k) : K.Anc S T i j := by
  have hRk : K.R S T k := R_of_inD hk.1 hjk.2
  exact ⟨inD_of_mem_pa hRk hjk.1, ReflTransGen.head ⟨hjk.1, hRk⟩ hk.2⟩

/-- *Lemma 5.5, first item:* `i ∈ T_i`. -/
theorem mem_Ti_self {i : Fin n} (hi : K.R S T i) : i ∈ K.Ti S T i := by
  rw [mem_Ti]
  have hA : K.Anc S T i i := ⟨Or.inr hi, ReflTransGen.refl⟩
  by_cases hT : i ∈ T
  · exact Or.inl ⟨hA, hT⟩
  · right; left
    refine ⟨hA, ?_⟩
    obtain ⟨hiS, t, ht, h⟩ := hi
    rcases h.cases_head with rfl | ⟨k, hik, hkt⟩
    · exact absurd ht hT
    · have hRk : K.R S T k := ⟨hik.2, t, ht, hkt⟩
      exact ⟨k, ⟨hik.1, hRk⟩, fun hk => not_dArrStar_of_dArr ⟨hik.1, hRk⟩ hk.2⟩

/-- `V(G_{S → T_i}) ∖ S = A ∖ S`. -/
theorem R_Ti_iff {i : Fin n} (hi : K.R S T i) (j : Fin n) :
    K.R S (K.Ti S T i) j ↔ K.Anc S T i j ∧ j ∉ S := by
  constructor
  · rintro ⟨hjS, t, ht, h⟩
    refine ⟨?_, hjS⟩
    -- the end of the path is in `A`
    have htS : t ∉ S := by
      rcases h.cases_tail with rfl | ⟨_, _, h'⟩
      · exact hjS
      · exact h'.2
    have htA : K.Anc S T i t := by
      rcases mem_Ti.1 ht with h₁ | h₁ | h₁
      · exact h₁.1
      · exact h₁.1
      · exact absurd h₁.1 htS
    clear ht hjS
    induction h using ReflTransGen.head_induction_on with
    | refl => exact htA
    | head hst _ ih => exact anc_of_avoid hst ih
  · rintro ⟨hA, hjS⟩
    refine ⟨hjS, i, mem_Ti_self hi, ?_⟩
    exact ReflTransGen.mono (fun _ _ h => dArr_avoid h) _ _ hA.2

/-- *Lemma 5.5, first item:* "`V(G_{S → T_i})` does not contain any child of `i` in `G_{S → T}`". -/
theorem not_inD_Ti_of_child {i k : Fin n} (hi : K.R S T i) (hk : K.DArr S T i k) :
    ¬ K.InD S (K.Ti S T i) k := by
  rintro (hkS | hR)
  · exact hk.2.1 hkS
  · exact not_dArrStar_of_dArr hk ((R_Ti_iff hi k).1 hR).1.2

/-- `V(G_{T_i → T}) ∖ T_i = B = V(G_{S → T}) ∖ (A ∪ S)`. -/
theorem R_Ti_T_iff {i : Fin n} (_hi : K.R S T i) (j : Fin n) :
    K.R (K.Ti S T i) T j ↔ K.R S T j ∧ ¬ K.Anc S T i j := by
  -- every vertex of `T_i` is in `A` or in `S`
  have hTi : ∀ y, y ∈ K.Ti S T i → K.Anc S T i y ∨ y ∈ S := fun y hy => by
    rcases mem_Ti.1 hy with h | h | h
    · exact Or.inl h.1
    · exact Or.inl h.1
    · exact Or.inr h.1
  constructor
  · rintro ⟨hjT, t, ht, h⟩
    -- every vertex of the path is in `B` or in `T_i`
    have key : ∀ y, ReflTransGen (K.Avoid (K.Ti S T i)) y t →
        (K.R S T y ∧ ¬ K.Anc S T i y) ∨ y ∈ K.Ti S T i := by
      intro y hy
      induction hy using ReflTransGen.head_induction_on with
      | refl =>
        by_cases htA : K.Anc S T i t
        · exact Or.inr (mem_Ti.2 (Or.inl ⟨htA, ht⟩))
        · by_cases htS : t ∈ S
          · exact Or.inr (mem_Ti.2 (Or.inr (Or.inr ⟨htS, htA⟩)))
          · exact Or.inl ⟨⟨htS, t, ht, ReflTransGen.refl⟩, htA⟩
      | @head y y' hyy' _ ih =>
        have hy'B : K.R S T y' ∧ ¬ K.Anc S T i y' := ih.resolve_right hyy'.2
        have hyD : K.InD S T y := inD_of_mem_pa hy'B.1 hyy'.1
        by_cases hyA : K.Anc S T i y
        · exact Or.inr (mem_Ti.2 (Or.inr (Or.inl ⟨hyA, y', ⟨hyy'.1, hy'B.1⟩, hy'B.2⟩)))
        · by_cases hyS : y ∈ S
          · exact Or.inr (mem_Ti.2 (Or.inr (Or.inr ⟨hyS, hyA⟩)))
          · exact Or.inl ⟨R_of_inD hyD hyS, hyA⟩
    exact (key j h).resolve_right hjT
  · rintro ⟨⟨hjS, t, ht, h⟩, hjA⟩
    refine ⟨fun hj => (hTi j hj).elim hjA hjS, t, ht, ?_⟩
    -- the path avoids `T_i`
    have key : ∀ y, ReflTransGen (K.Avoid S) y t → y ∉ S → ¬ K.Anc S T i y →
        ReflTransGen (K.Avoid (K.Ti S T i)) y t := by
      intro y hy
      induction hy using ReflTransGen.head_induction_on with
      | refl => exact fun _ _ => ReflTransGen.refl
      | @head y y' hyy' hrest ih =>
        intro hyS hyA
        have hRy' : K.R S T y' := ⟨hyy'.2, t, ht, hrest⟩
        have hy'A : ¬ K.Anc S T i y' := fun h' => hyA (anc_of_avoid hyy' h')
        refine ReflTransGen.head ⟨hyy'.1, fun h' => (hTi y' h').elim hy'A hyy'.2⟩ ?_
        exact ih hyy'.2 hy'A
    exact key j h hjS hjA

/-- *Lemma 5.5, proof:* "the set `V(D) ∖ S` is the disjoint union of `A ∖ S` and `B`", i.e. of the
vertices of `G_{S → T_i}` outside `S` and those of `G_{T_i → T}` outside `T_i`. -/
theorem R_iff_R_Ti_or {i : Fin n} (hi : K.R S T i) (j : Fin n) :
    K.R S T j ↔ K.R S (K.Ti S T i) j ∨ K.R (K.Ti S T i) T j := by
  rw [R_Ti_iff hi, R_Ti_T_iff hi]
  constructor
  · intro h
    by_cases hA : K.Anc S T i j
    · exact Or.inl ⟨hA, h.1⟩
    · exact Or.inr ⟨h, hA⟩
  · rintro (⟨hA, hS⟩ | ⟨h, -⟩)
    · exact R_of_inD hA.1 hS
    · exact h

theorem not_R_Ti_and {i : Fin n} (hi : K.R S T i) (j : Fin n) :
    ¬ (K.R S (K.Ti S T i) j ∧ K.R (K.Ti S T i) T j) := by
  rw [R_Ti_iff hi, R_Ti_T_iff hi]
  exact fun ⟨⟨hA, _⟩, _, hA'⟩ => hA' hA

end EffSig

end FreeMarkov
