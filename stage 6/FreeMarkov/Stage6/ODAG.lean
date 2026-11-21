/-
Free Markov categories, Stage 6: ordered finite directed acyclic graphs (`FinODAG`), their
morphisms and fibers, the parents of a vertex, and the free `DD`-graph monoid `W(G)` of
Definition 6.2.

* `FinODAG`: a finite directed graph with exactly one loop at each vertex (the identity loop) whose
  vertices are `0, …, n-1` (PLAN.md, Stage 6, default: vertices `Fin n`), such that every arrow goes
  weakly up (`s a ≤ t a`).  So the total order of `Fin n` extends the partial order given by the
  directed paths, and the graph is acyclic.  This is "an ordered directed acyclic graph with identity
  loops, where the total ordering is expressed by the bijection `σ : V → {1, …, n}`".
* `FinODAG.Hom`: graph homomorphisms that preserve the order in the weak sense; the category
  `FinODAG`; the forgetful functor to `FinDAG` (Section 5).
* Fibers: `fiber φ y`; "the fiber `φ⁻¹(y)` is an interval" (`fiber_interval`) and "if `y < y'` then
  every vertex in `φ⁻¹(y)` comes before every vertex in `φ⁻¹(y')`" (`lt_of_fiber_lt`).
* `pa G i` (`S_i` of Definition 6.2: the `j ≠ i` with an arrow `v_j → v_i`), and the family
  `G.K : EffSig n` of Definition 6.3, whose associated graph is acyclic since `j ∈ S_i → j < i`.
  `W(G)` is the free `DD`-graph monoid `G.K.sig.G` of Stage 5, and `Cau(G)` is `J.FsM` for
  `J : G.JS` (C1 for `W(G)`).

No cited result is used in this file.
-/
module

public import FreeMarkov.Stage5

@[expose] public section

namespace FreeMarkov

open CategoryTheory Relation

/-- *Section 6.* An object of **`FinODAG`**: an ordered finite directed acyclic graph with identity
loops.  The vertices are `0, …, n-1`, in their natural order (the bijection `σ : V → {1, …, n}`);
the arrows form a finite type with source and target maps; each vertex carries exactly one loop, the
identity loop; and every arrow goes weakly up, so that the total ordering extends the partial
ordering induced by the directed paths (which makes the graph acyclic). -/
structure FinODAG where
  /-- The number of vertices. -/
  n : ℕ
  /-- The arrows. -/
  A : Type
  [finA : Fintype A]
  /-- The source of an arrow. -/
  s : A → Fin n
  /-- The target of an arrow. -/
  t : A → Fin n
  /-- The identity loop on a vertex. -/
  loop : Fin n → A
  s_loop (v : Fin n) : s (loop v) = v
  t_loop (v : Fin n) : t (loop v) = v
  /-- The identity loop is the only loop at its vertex. -/
  eq_loop (a : A) : s a = t a → a = loop (s a)
  /-- The total ordering extends the partial ordering of the directed paths. -/
  s_le_t (a : A) : s a ≤ t a

attribute [instance] FinODAG.finA

namespace FinODAG

/-- *Section 6.* A morphism of `FinODAG`: a graph homomorphism `φ` that preserves the total
orderings in the weak sense, `x ≤ y → φ(x) ≤ φ(y)`. -/
@[ext]
structure Hom (G H : FinODAG) where
  /-- The map on vertices. -/
  onV : Fin G.n → Fin H.n
  /-- The map on arrows. -/
  onA : G.A → H.A
  s_onA (a : G.A) : H.s (onA a) = onV (G.s a)
  t_onA (a : G.A) : H.t (onA a) = onV (G.t a)
  monotone : Monotone onV

/-- *Section 6.* The category **`FinODAG`**. -/
instance : Category FinODAG where
  Hom := Hom
  id G := ⟨id, id, fun _ => rfl, fun _ => rfl, monotone_id⟩
  comp f g := ⟨g.onV ∘ f.onV, g.onA ∘ f.onA, fun a => by simp [g.s_onA, f.s_onA],
    fun a => by simp [g.t_onA, f.t_onA], g.monotone.comp f.monotone⟩

@[simp] theorem id_onV (G : FinODAG) (x : Fin G.n) : Hom.onV (𝟙 G) x = x := rfl

@[simp] theorem comp_onV {G H L : FinODAG} (f : G ⟶ H) (g : H ⟶ L) (x : Fin G.n) :
    Hom.onV (f ≫ g) x = g.onV (f.onV x) := rfl

@[ext] theorem hom_ext {G H : FinODAG} {f g : G ⟶ H} (h₁ : f.onV = g.onV) (h₂ : f.onA = g.onA) :
    f = g := Hom.ext h₁ h₂

/-- An arrow that is not a loop goes strictly up. -/
theorem s_lt_t (G : FinODAG) {a : G.A} (h : G.s a ≠ G.t a) : G.s a < G.t a :=
  lt_of_le_of_ne (G.s_le_t a) h

/-- The underlying object of `FinDAG` (Section 5). -/
def toFinDAG (G : FinODAG) : FinDAG where
  V := Fin G.n
  A := G.A
  s := G.s
  t := G.t
  loop := G.loop
  s_loop := G.s_loop
  t_loop := G.t_loop
  eq_loop := G.eq_loop
  acyclic v h := by
    have : ∀ x y, TransGen (fun x y => ∃ a, G.s a = x ∧ G.t a = y ∧ x ≠ y) x y → x < y := by
      intro x y hxy
      induction hxy with
      | single h => obtain ⟨a, rfl, rfl, hne⟩ := h; exact G.s_lt_t hne
      | tail _ h ih => obtain ⟨a, rfl, rfl, hne⟩ := h; exact ih.trans (G.s_lt_t hne)
    exact lt_irrefl v (this v v h)

/-- The forgetful functor `FinODAG → FinDAG`. -/
def forget : FinODAG ⥤ FinDAG where
  obj := toFinDAG
  map f := ⟨f.onV, f.onA, f.s_onA, f.t_onA⟩

/-- A graph homomorphism sends identity loops to identity loops. -/
theorem Hom.onA_loop {G H : FinODAG} (f : G ⟶ H) (v : Fin G.n) :
    f.onA (G.loop v) = H.loop (f.onV v) := by
  have h := H.eq_loop (f.onA (G.loop v)) (by rw [f.s_onA, f.t_onA, G.s_loop, G.t_loop])
  rw [h, f.s_onA, G.s_loop]

/-! ### Fibers -/

section Fibers

variable {H G : FinODAG} (φ : H ⟶ G)

/-- The fiber `φ⁻¹(y)`. -/
def fiber (y : Fin G.n) : Finset (Fin H.n) := Finset.univ.filter fun x => φ.onV x = y

@[simp] theorem mem_fiber {y : Fin G.n} {x : Fin H.n} : x ∈ fiber φ y ↔ φ.onV x = y := by
  simp [fiber]

/-- *Section 6.* "If `y < y'` then every vertex in `φ⁻¹(y)` comes before every vertex in
`φ⁻¹(y')`." -/
theorem lt_of_fiber_lt {x x' : Fin H.n} (h : φ.onV x < φ.onV x') : x < x' := by
  by_contra h'
  exact absurd (φ.monotone (le_of_not_gt h')) (not_le.2 h)

/-- *Section 6.* "For each vertex `y` of the target, the fiber `φ⁻¹(y)` is an interval of the total
ordering, possibly empty." -/
theorem fiber_interval {y : Fin G.n} {x z x' : Fin H.n} (hx : x ∈ fiber φ y) (hx' : x' ∈ fiber φ y)
    (h₁ : x ≤ z) (h₂ : z ≤ x') : z ∈ fiber φ y := by
  rw [mem_fiber] at *
  exact le_antisymm (hx' ▸ φ.monotone h₂) (hx ▸ φ.monotone h₁)

/-- Distinct vertices have disjoint fibers. -/
theorem fiber_disjoint {y y' : Fin G.n} (h : y ≠ y') : Disjoint (fiber φ y) (fiber φ y') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_fiber] at hx hx'
  exact h (hx.symm.trans hx')

/-- The preimage `φ⁻¹(S)` of a set of vertices. -/
def preimS (S : Finset (Fin G.n)) : Finset (Fin H.n) := Finset.univ.filter fun x => φ.onV x ∈ S

@[simp] theorem mem_preimS {S : Finset (Fin G.n)} {x : Fin H.n} : x ∈ preimS φ S ↔ φ.onV x ∈ S := by
  simp [preimS]

theorem preimS_singleton (y : Fin G.n) : preimS φ {y} = fiber φ y := by
  ext x; simp

end Fibers

/-! ### Parents -/

variable (G : FinODAG)

open Classical in
/-- *Definition 6.2.* The parents `S_i` of `v_i`: "the set of those `j ≠ i` such that there is an
arrow from `v_j` to `v_i` in `G`" (the identity loop is disregarded). -/
noncomputable def pa (i : Fin G.n) : Finset (Fin G.n) :=
  Finset.univ.filter fun j => j ≠ i ∧ ∃ a, G.s a = j ∧ G.t a = i

theorem mem_pa {i j : Fin G.n} : j ∈ G.pa i ↔ j ≠ i ∧ ∃ a, G.s a = j ∧ G.t a = i := by
  classical
  unfold pa
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem lt_of_mem_pa {i j : Fin G.n} (h : j ∈ G.pa i) : j < i := by
  obtain ⟨hne, a, rfl, rfl⟩ := (G.mem_pa).1 h
  exact G.s_lt_t hne

/-- *Definition 6.3.* The family `K_G` of the pairs `(S_i, κ_{v_i})`, as the sets `S_i`: "the
directed graph associated with `K` is acyclic, since `j ∈ S_i` implies `j < i`". -/
@[reducible] noncomputable def K : EffSig G.n where
  pa := G.pa
  not_mem_pa i h := lt_irrefl i (G.lt_of_mem_pa h)
  acyclic i h := by
    have : ∀ x y, TransGen (fun j k => j ∈ G.pa k) x y → x < y := by
      intro x y hxy
      induction hxy with
      | single h => exact G.lt_of_mem_pa h
      | tail _ h ih => exact ih.trans (G.lt_of_mem_pa h)
    exact lt_irrefl i (this i i h)

/-- *Definition 6.2.* The free `DD`-graph monoid **`W(G)`**: words over the vertices, with
`ε_v : v → ∅`, `δ_v : v → vv` and the causal mechanism `κ_v : pa(v) → v` for each vertex, where
`pa(v_i) = v_{S_i}` lists the parents in the order of `V`. -/
noncomputable abbrev W : FreeDDGraphMonoid.{0, 0} (Fin G.n) := G.K.sig.G

/-- The cited result C1 for `W(G)`; for `J : G.JS`, `J.FsM` is **`Cau(G)`**, the free Markov
category over `W(G)` (Theorem 4.1). -/
noncomputable abbrev JS : Type := JoyalStreet G.W.toFreeGraphMonoid

/-- `pa(v_i) = v_{S_i}` is the source of the causal mechanism `κ_{v_i}`. -/
theorem src_mech (i : Fin G.n) : G.K.sig.src i = finWord (G.pa i) := rfl

/-- *Section 6.* A graph homomorphism `φ : H → G` sends a parent of `x` to `φ(x)` or to a parent of
`φ(x)` ("since `φ` sends a parent of a vertex in `φ⁻¹(v)` either to `v` or to a parent of `v`"). -/
theorem Hom.map_pa {H G : FinODAG} (φ : H ⟶ G) {x p : Fin H.n} (h : p ∈ H.pa x) :
    φ.onV p = φ.onV x ∨ φ.onV p ∈ G.pa (φ.onV x) := by
  obtain ⟨-, a, rfl, rfl⟩ := (H.mem_pa).1 h
  by_cases he : φ.onV (H.s a) = φ.onV (H.t a)
  · exact Or.inl he
  · right
    rw [G.mem_pa]
    exact ⟨he, φ.onA a, φ.s_onA a, φ.t_onA a⟩

end FinODAG

end FreeMarkov
