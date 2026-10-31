/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.SlabsEvents
public import CurvatureVariance.Paper.Proofs.Geometry.SlabsPair

/-!
# Walks stay near their starting point

`inBox_of_mem_support`: the vertices of a walk from `u` lie within its number of edges of `u`,
coordinatewise. With the bound on the number of edges on the good event (`IsGood.length_le`, the
proof of Lemma `lem:cone`), a nearly optimal path from the box stays in a slightly larger box, where
the passage time concentrates.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- The vertices of a walk from `u` lie within its number of edges of `u`, coordinatewise. -/
theorem inBox_of_mem_support {u v : Vertex m} (p : (latticeGraph m).Walk u v) {R₀ : ℝ}
    (hu : InBox R₀ u) {z : Vertex m} (hz : z ∈ p.support) : InBox (R₀ + p.length) z := by
  classical
  have hl : (l1Dist u z : ℝ) ≤ p.length := by
    have h1 := l1Dist_le_length (p.takeUntil z hz)
    have h2 := SimpleGraph.Walk.length_takeUntil_le_length p hz
    exact_mod_cast h1.trans h2
  have h1 : |(z.1 : ℝ) - u.1| ≤ l1Dist u z := by
    have : ((u.1 - z.1).natAbs : ℝ) ≤ l1Dist u z := by
      simp only [l1Dist]; push_cast; linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
        (Nat.cast_nonneg (α := ℝ) (u.2 j - z.2 j).natAbs)]
    rw [Nat.cast_natAbs, Int.cast_abs] at this
    push_cast at this
    rwa [abs_sub_comm] at this
  have h2 : ∀ j, |(z.2 j : ℝ) - u.2 j| ≤ l1Dist u z := by
    intro j
    have hj : ((u.2 j - z.2 j).natAbs : ℝ) ≤ ∑ i, ((u.2 i - z.2 i).natAbs : ℝ) :=
      Finset.single_le_sum (f := fun i => ((u.2 i - z.2 i).natAbs : ℝ))
        (fun i _ => Nat.cast_nonneg _) (Finset.mem_univ j)
    have : ((u.2 j - z.2 j).natAbs : ℝ) ≤ l1Dist u z := by
      simp only [l1Dist]; push_cast
      have := Nat.cast_nonneg (α := ℝ) (u.1 - z.1).natAbs
      linarith
    rw [Nat.cast_natAbs, Int.cast_abs] at this
    push_cast at this
    rwa [abs_sub_comm] at this
  refine ⟨?_, fun j => ?_⟩
  · have := abs_sub_abs_le_abs_sub (z.1 : ℝ) u.1
    linarith [hu.1]
  · have := abs_sub_abs_le_abs_sub (z.2 j : ℝ) (u.2 j)
    linarith [hu.2 j, h2 j]

end CurvatureVariance.Paper.Proofs.Geometry
