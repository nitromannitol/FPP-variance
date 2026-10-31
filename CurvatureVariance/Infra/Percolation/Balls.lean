/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Percolation.Connections
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Balls and the one-arm event in bond percolation

In a connected, locally finite graph `G` with a root `o`, closed balls for the graph distance are
finite (`finite_setOf_dist_le`).

* `innerBall hG o n` is the finset of vertices at distance `< n` from `o`, and `innerEdges G o n`
  the set of edges with an endpoint there (`finite_innerEdges`).
* `armEvent G o n` is the **one-arm event**: `o` is joined by an open path to a vertex at distance
  at least `n`. In finite volume (`armEvent_eq`) it is joined inside `innerEdges G o n` to the
  sphere of radius `n`, so it depends on finitely many edges (`dependsOn_armEvent`); it is
  measurable, increasing and decreasing in `n`.
* `setOf_infinite_eq_iInter_armEvent`: the cluster of `o` is infinite iff all arm events occur.
-/

@[expose] public section

namespace CurvatureVariance.Infra.Percolation

variable {V : Type*} {G : SimpleGraph V}

section Balls

/-- A neighbour of a vertex at distance `< n` is at distance `≤ n`. -/
theorem dist_le_of_adj_of_dist_lt (hG : G.Connected) {o x y : V} {n : ℕ} (hxy : G.Adj x y)
    (hx : G.dist o x < n) : G.dist o y ≤ n := by
  have h1 : G.dist x y ≤ 1 := by simpa using SimpleGraph.dist_le hxy.toWalk
  have := hG.dist_triangle (u := o) (v := x) (w := y)
  omega

/-- Distances from two vertices differ by at most their distance. -/
theorem le_dist_of_le_dist (hG : G.Connected) {o y w : V} {n L : ℕ} (hy : G.dist o y ≤ L)
    (hw : n + L ≤ G.dist o w) : n ≤ G.dist y w := by
  have := hG.dist_triangle (u := o) (v := y) (w := w)
  omega

/-- In a connected, locally finite graph, closed balls are finite. -/
theorem finite_setOf_dist_le [G.LocallyFinite] (hG : G.Connected) (o : V) (n : ℕ) :
    {v | G.dist o v ≤ n}.Finite := by
  induction n with
  | zero =>
    refine (Set.finite_singleton o).subset fun v hv => ?_
    have : G.dist o v = 0 := Nat.le_zero.1 hv
    exact ((hG.dist_eq_zero_iff).1 this).symm
  | succ n ih =>
    have hfin : (⋃ u ∈ {v | G.dist o v ≤ n}, G.neighborSet u).Finite :=
      ih.biUnion fun u _ => (G.neighborSet u).toFinite
    refine (ih.union hfin).subset fun v hv => ?_
    by_cases hvn : G.dist o v ≤ n
    · exact Or.inl hvn
    · right
      have hv' : G.dist o v = n + 1 := by
        have : G.dist o v ≤ n + 1 := hv
        omega
      obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist o v
      have hne : v ≠ o := by
        rintro rfl; simp at hv'
      obtain ⟨u, h, q, hq⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne p.reverse
      have hl : q.length = n := by
        have := congrArg SimpleGraph.Walk.length hq
        simp at this; omega
      have hu : G.dist o u ≤ n := by
        have := SimpleGraph.dist_le q.reverse
        simpa [hl] using this
      exact Set.mem_biUnion hu h.symm

/-- The vertices at distance `< n` from `o`, as a finset. -/
noncomputable def innerBall [G.LocallyFinite] (hG : G.Connected) (o : V) (n : ℕ) : Finset V :=
  ((finite_setOf_dist_le hG o n).subset
    (fun _ hv => (Nat.le_of_lt hv : _ ≤ n) :
      {v | G.dist o v < n} ⊆ {v | G.dist o v ≤ n})).toFinset

theorem mem_innerBall [G.LocallyFinite] (hG : G.Connected) {o v : V} {n : ℕ} :
    v ∈ innerBall hG o n ↔ G.dist o v < n := by
  simp [innerBall]

variable (G) in
/-- The edges with an endpoint at distance `< n` from `o`. -/
def innerEdges (o : V) (n : ℕ) : Set (Sym2 V) := {e | ∃ x ∈ e, G.dist o x < n}

/-- Finitely many edges have an endpoint at distance `< n`. -/
theorem finite_innerEdges [G.LocallyFinite] (hG : G.Connected) (o : V) (n : ℕ) :
    {e : G.edgeSet | e.1 ∈ innerEdges G o n}.Finite := by
  have hS : (⋃ x ∈ {v | G.dist o v < n}, G.incidenceSet x).Finite := by
    refine ((finite_setOf_dist_le hG o n).subset
      (fun _ hv => (Nat.le_of_lt hv : _ ≤ n))).biUnion fun x _ => ?_
    classical
    exact (G.incidenceSet x).toFinite
  refine (hS.preimage Subtype.val_injective.injOn).subset fun e he => ?_
  obtain ⟨x, hx, hxn⟩ := he
  exact Set.mem_biUnion hxn ⟨e.2, hx⟩

end Balls

section Arm

variable (G) in
/-- **The one-arm event**: `o` is joined by an open path to a vertex at distance at least `n`. -/
def armEvent (o : V) (n : ℕ) : Set (G.edgeSet → Bool) :=
  {ω | ∃ w, n ≤ G.dist o w ∧ OpenConnected G ω Set.univ o w}

/-- The first vertex of an open walk at distance `≥ n` is reached at distance exactly `n`, through
edges with an endpoint at distance `< n`. -/
theorem exists_dist_eq_openConnected (hG : G.Connected) (ω : G.edgeSet → Bool) (o : V) (n : ℕ)
    {u w : V} (p : G.Walk u w) (hp : IsOpenIn ω Set.univ p) (hu : G.dist o u < n)
    (hw : n ≤ G.dist o w) :
    ∃ w', G.dist o w' = n ∧ OpenConnected G ω (innerEdges G o n) u w' := by
  induction p with
  | nil => omega
  | @cons a b c h q ih =>
    rw [isOpenIn_cons] at hp
    have hmem : s(a, b) ∈ innerEdges G o n := ⟨a, by simp, hu⟩
    by_cases hb : G.dist o b < n
    · obtain ⟨w', hw', hc⟩ := ih hp.2 hb hw
      exact ⟨w', hw', (OpenConnected.of_adj h hmem hp.1.2).trans hc⟩
    · exact ⟨b, le_antisymm (dist_le_of_adj_of_dist_lt hG h hu) (not_lt.1 hb),
        OpenConnected.of_adj h hmem hp.1.2⟩

/-- The arm event in finite volume: it suffices to reach the sphere of radius `n` with edges having
an endpoint inside the ball of radius `n - 1`. -/
theorem armEvent_eq (hG : G.Connected) (o : V) (n : ℕ) :
    armEvent G o n = {ω | ∃ w, G.dist o w = n ∧ OpenConnected G ω (innerEdges G o n) o w} := by
  ext ω
  constructor
  · rintro ⟨w, hw, p, hp⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨o, by simp, OpenConnected.refl _ _ _⟩
    · exact exists_dist_eq_openConnected hG ω o n p hp (by simpa using hn) hw
  · rintro ⟨w, hw, hc⟩
    exact ⟨w, hw.ge, hc.mono_edges (Set.subset_univ _)⟩

theorem dependsOn_armEvent (hG : G.Connected) (o : V) (n : ℕ) :
    DependsOn (· ∈ armEvent G o n) {e : G.edgeSet | e.1 ∈ innerEdges G o n} := by
  rw [show (· ∈ armEvent G o n) = fun ω : G.edgeSet → Bool =>
      ∃ w ∈ {w | G.dist o w = n}, OpenConnected G ω (innerEdges G o n) o w by
    ext ω; rw [armEvent_eq hG]; rfl]
  exact dependsOn_exists_openConnected _ _ _

theorem measurableSet_armEvent [Countable V] (o : V) (n : ℕ) : MeasurableSet (armEvent G o n) :=
  measurableSet_exists_openConnected (W := {w | n ≤ G.dist o w}) Set.univ o

theorem isUpperSet_armEvent (o : V) (n : ℕ) : IsUpperSet (armEvent G o n) :=
  isUpperSet_exists_openConnected (W := {w | n ≤ G.dist o w}) Set.univ o

theorem armEvent_antitone (o : V) : Antitone (armEvent G o) :=
  fun _ _ hnm _ ⟨w, hw, h⟩ => ⟨w, hnm.trans hw, h⟩

@[simp] theorem armEvent_zero (o : V) : armEvent G o 0 = Set.univ :=
  Set.eq_univ_of_forall fun _ => ⟨o, by simp, OpenConnected.refl _ _ _⟩

/-- **The cluster of `o` is infinite iff `o` is joined to every distance.** -/
theorem setOf_infinite_eq_iInter_armEvent [G.LocallyFinite] (hG : G.Connected) (o : V) :
    {ω : G.edgeSet → Bool | {x | OpenConnected G ω Set.univ o x}.Infinite} =
      ⋂ n, armEvent G o n := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · intro hinf n
    by_contra hn
    refine hinf ((finite_setOf_dist_le hG o n).subset fun x hx => ?_)
    by_contra hxn
    have hxn' : ¬ G.dist o x ≤ n := hxn
    exact hn ⟨x, by omega, hx⟩
  · intro h hfin
    obtain ⟨B, hB⟩ := (hfin.image (G.dist o)).bddAbove
    obtain ⟨w, hw, hc⟩ := h (B + 1)
    have := hB ⟨w, hc, rfl⟩
    omega

end Arm

end CurvatureVariance.Infra.Percolation
