/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Lattice.Edge
public import CurvatureVariance.Statements.Lattice.LatticeGraph
public import CurvatureVariance.Statements.Space.Point
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Logic.Equiv.List
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.Linarith

/-!
# The nearest-neighbour graph of `ℤ^d`

Basic facts about the lattice graph `latticeGraph m` on `Vertex m = ℤ × ℤ^m`: adjacency
in both orientations, decidability, local finiteness, connectedness and countability (of vertices,
edges and walks); and the embedding `point` of vertices into `ℝ^d`, which is additive and moves
adjacent vertices by exactly one. The translations of `ℤ^d` are in
`CurvatureVariance.Infra.FPP.Translation`.
-/

@[expose] public section

open scoped NNReal

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### Adjacency -/

/-- Adjacency in the lattice graph: `y` is one of the `2d` neighbours `x ± (1, 0)`,
`x ± (0, e_j)` of `x`. -/
theorem latticeGraph_adj {x y : Vertex m} :
    (latticeGraph m).Adj x y ↔
      y = x + (1, 0) ∨ y = x - (1, 0) ∨
        ∃ j : Fin m, y = x + (0, Pi.single j 1) ∨ y = x - (0, Pi.single j 1) := by
  simp only [latticeGraph, SimpleGraph.fromRel_adj, ne_eq]
  constructor
  · rintro ⟨-, (h | ⟨j, h⟩) | (h | ⟨j, h⟩)⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨j, Or.inl h⟩)
    · exact Or.inr (Or.inl (by rw [h]; simp))
    · exact Or.inr (Or.inr ⟨j, Or.inr (by rw [h]; simp)⟩)
  · rintro (rfl | rfl | ⟨j, rfl | rfl⟩)
    · exact ⟨fun h => by simp [Prod.ext_iff] at h, Or.inl (Or.inl rfl)⟩
    · exact ⟨fun h => by simpa [Prod.ext_iff] using sub_eq_self.mp h.symm,
        Or.inr (Or.inl (by simp))⟩
    · exact ⟨fun h => by simp [Prod.ext_iff] at h, Or.inl (Or.inr ⟨j, rfl⟩)⟩
    · exact ⟨fun h => by simpa [Prod.ext_iff] using sub_eq_self.mp h.symm,
        Or.inr (Or.inr ⟨j, by simp⟩)⟩

/-- Adjacency in the lattice graph in terms of the difference of the endpoints. -/
theorem latticeGraph_adj_iff_sub {x y : Vertex m} :
    (latticeGraph m).Adj x y ↔
      y - x = (1, 0) ∨ y - x = -(1, 0) ∨
        ∃ j : Fin m, y - x = (0, Pi.single j 1) ∨ y - x = -(0, Pi.single j 1) := by
  rw [latticeGraph_adj]
  simp only [sub_eq_iff_eq_add', ← sub_eq_add_neg]

/-- Each vertex is adjacent to its longitudinal successor. -/
theorem latticeGraph_adj_add_longitudinal (x : Vertex m) : (latticeGraph m).Adj x (x + (1, 0)) :=
  latticeGraph_adj.mpr (Or.inl rfl)

/-- Each vertex is adjacent to its transverse successor in direction `j`. -/
theorem latticeGraph_adj_add_transverse (x : Vertex m) (j : Fin m) :
    (latticeGraph m).Adj x (x + (0, Pi.single j 1)) :=
  latticeGraph_adj.mpr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩))

/-- Each vertex is adjacent to its transverse predecessor in direction `j`. -/
theorem latticeGraph_adj_sub_transverse (x : Vertex m) (j : Fin m) :
    (latticeGraph m).Adj x (x - (0, Pi.single j 1)) :=
  latticeGraph_adj.mpr (Or.inr (Or.inr ⟨j, Or.inr rfl⟩))

/-- Adjacency in the lattice graph is decidable. -/
instance (m : ℕ) : DecidableRel (latticeGraph m).Adj := fun _ _ =>
  decidable_of_iff _ latticeGraph_adj.symm

/-! ### Local finiteness, connectedness, countability -/

/-- The `2d` neighbours of a vertex, as a finset. -/
def latticeNeighbors (x : Vertex m) : Finset (Vertex m) :=
  {x + (1, 0), x - (1, 0)} ∪ (Finset.univ.image fun j : Fin m => x + (0, Pi.single j 1)) ∪
    Finset.univ.image fun j : Fin m => x - (0, Pi.single j 1)

/-- The finset `latticeNeighbors x` consists of the neighbours of `x`. -/
theorem mem_latticeNeighbors {x y : Vertex m} :
    y ∈ latticeNeighbors x ↔ (latticeGraph m).Adj x y := by
  rw [latticeGraph_adj, latticeNeighbors]
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro (((h | h) | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨j, Or.inl rfl⟩)
    · exact Or.inr (Or.inr ⟨j, Or.inr rfl⟩)
  · rintro (h | h | ⟨j, h | h⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr ⟨j, h.symm⟩)
    · exact Or.inr ⟨j, h.symm⟩

/-- The lattice graph is locally finite. -/
instance (m : ℕ) : (latticeGraph m).LocallyFinite := fun x =>
  Fintype.ofFinset (latticeNeighbors x) fun _ => mem_latticeNeighbors

/-- Every vertex of `ℤ^d` is an integer combination of the unit vectors. -/
private theorem eq_sum_units (a : Vertex m) :
    a = a.1 • ((1, 0) : Vertex m) + ∑ j, a.2 j • ((0, Pi.single j 1) : Vertex m) := by
  ext
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

/-- The lattice graph is connected: every vertex is reachable from every other. -/
theorem latticeGraph_reachable (x y : Vertex m) : (latticeGraph m).Reachable x y := by
  let S : AddSubgroup (Vertex m) :=
    { carrier := {a | ∀ z, (latticeGraph m).Reachable z (z + a)}
      zero_mem' := fun z => by simp
      add_mem' := fun {a b} ha hb z => by
        simpa only [add_assoc] using (ha z).trans (hb (z + a))
      neg_mem' := fun {a} ha z => by
        have h := (ha (z + -a)).symm
        simpa only [neg_add_cancel_right] using h }
  have hl : ((1, 0) : Vertex m) ∈ S := fun z => (latticeGraph_adj_add_longitudinal z).reachable
  have ht : ∀ j : Fin m, ((0, Pi.single j 1) : Vertex m) ∈ S := fun j z =>
    (latticeGraph_adj_add_transverse z j).reachable
  have hall : y - x ∈ S := by
    rw [eq_sum_units (y - x)]
    exact S.add_mem (S.zsmul_mem hl _) (S.sum_mem fun j _ => S.zsmul_mem (ht j) _)
  simpa using hall x

/-- There is a walk between any two vertices. -/
theorem nonempty_walk (x y : Vertex m) : Nonempty ((latticeGraph m).Walk x y) :=
  latticeGraph_reachable x y

/-- Walks on a countable vertex set are countable, by their vertex lists. -/
instance countableWalk {V : Type*} [Countable V] {G : SimpleGraph V} {u v : V} :
    Countable (G.Walk u v) :=
  SimpleGraph.Walk.support_injective.countable

/-! ### The embedding of `ℤ^d` into `ℝ^d` -/

@[simp] theorem transversePoint_apply (y : Fin m → ℤ) (j : Fin m) :
    transversePoint y j = (y j : ℝ) := rfl

@[simp] theorem transversePoint_zero : transversePoint (0 : Fin m → ℤ) = 0 := by
  ext j; simp

@[simp] theorem transversePoint_add (y z : Fin m → ℤ) :
    transversePoint (y + z) = transversePoint y + transversePoint z := by
  ext j; simp

@[simp] theorem transversePoint_neg (y : Fin m → ℤ) :
    transversePoint (-y) = -transversePoint y := by
  ext j; simp

@[simp] theorem transversePoint_sub (y z : Fin m → ℤ) :
    transversePoint (y - z) = transversePoint y - transversePoint z := by
  ext j; simp

/-- The transverse unit vector `e_j` of `ℤ^m` is the unit vector of `ℝ^m`. -/
theorem transversePoint_single (j : Fin m) :
    transversePoint (Pi.single j (1 : ℤ)) = PiLp.single 2 j (1 : ℝ) := by
  ext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- Two points of `ℝ^d` with the same longitudinal and transverse parts are equal. -/
theorem pt_ext {z w : Pt m} (h₁ : z.fst = w.fst) (h₂ : z.snd = w.snd) : z = w := by
  rw [← WithLp.toLp_ofLp 2 z, ← WithLp.toLp_ofLp 2 w]
  exact congrArg (WithLp.toLp 2) (Prod.ext h₁ h₂)

@[simp] theorem point_fst (x : Vertex m) : (point x).fst = (x.1 : ℝ) := rfl

@[simp] theorem point_snd (x : Vertex m) : (point x).snd = transversePoint x.2 := rfl

@[simp] theorem point_zero : point (0 : Vertex m) = 0 := by
  exact pt_ext (by simp) (by simp)

@[simp] theorem point_add (x y : Vertex m) : point (x + y) = point x + point y := by
  exact pt_ext (by simp) (by simp)

@[simp] theorem point_neg (x : Vertex m) : point (-x) = -point x := by
  exact pt_ext (by simp) (by simp)

@[simp] theorem point_sub (x y : Vertex m) : point (x - y) = point x - point y := by
  exact pt_ext (by simp) (by simp)

/-- The Euclidean norm of a point, in longitudinal and transverse parts. -/
theorem norm_point_sq (x : Vertex m) :
    ‖point x‖ ^ 2 = (x.1 : ℝ) ^ 2 + ‖transversePoint x.2‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, point_fst, point_snd, Real.norm_eq_abs, sq_abs]

/-- The unit vectors of `ℤ^d` have norm one. -/
theorem norm_point_longitudinal : ‖point ((1, 0) : Vertex m)‖ = 1 := by
  have h := norm_point_sq ((1, 0) : Vertex m)
  simp only [Int.cast_one, one_pow, transversePoint_zero, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  nlinarith [norm_nonneg (point ((1, 0) : Vertex m))]

/-- The transverse unit vectors of `ℤ^d` have norm one. -/
theorem norm_point_transverse (j : Fin m) : ‖point ((0, Pi.single j 1) : Vertex m)‖ = 1 := by
  have h := norm_point_sq ((0, Pi.single j 1) : Vertex m)
  rw [transversePoint_single, PiLp.norm_single, norm_one] at h
  simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_pow,
    zero_add] at h
  nlinarith [norm_nonneg (point ((0, Pi.single j 1) : Vertex m))]

/-- Adjacent vertices are at Euclidean distance one. -/
theorem norm_point_sub_point_of_adj {x y : Vertex m} (h : (latticeGraph m).Adj x y) :
    ‖point x - point y‖ = 1 := by
  rw [← norm_neg, neg_sub, ← point_sub]
  rcases latticeGraph_adj_iff_sub.mp h with h | h | ⟨j, h | h⟩ <;> rw [h]
  · exact norm_point_longitudinal
  · rw [point_neg, norm_neg]; exact norm_point_longitudinal
  · exact norm_point_transverse j
  · rw [point_neg, norm_neg]; exact norm_point_transverse j

end CurvatureVariance.Infra.FPP
