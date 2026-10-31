/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.UnitGrid
public import IsotropicVariance.Infra.WhiteNoise.Partition

/-! # Diameter and influence bounds for grid neighborhoods

The sum-of-coordinate norm estimate is adapted from
`IsotropicVariance.Infra.WhiteNoise.Partition`, avoiding its smooth bump dependencies.
-/

@[expose] public section
open Set Metric
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.WhiteNoise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Any two points in one enlarged cell have uniformly bounded distance. -/
theorem dist_le_of_mem_gridNeighborhood {z : Coord E → ℤ} {x y : E}
    (hx : x ∈ gridNeighborhood z) (hy : y ∈ gridNeighborhood z) :
    dist x y ≤ 5 * (Module.finrank ℝ E : ℝ) := by
  rw [dist_eq_norm]
  refine (Infra.WhiteNoise.norm_le_sum_abs_coord (x - y)).trans ?_
  have hC (i : Coord E) : |coord (x - y) i| ≤ 5 := by
    have hx' := hx i
    have hy' := hy i
    have hsub : coord (x - y) i = coord x i - coord y i := by
      simpa only [coordCLM_apply, Pi.sub_apply] using congrFun ((coordCLM E).map_sub x y) i
    rw [hsub, abs_le]
    constructor <;> linarith only [hx'.1, hx'.2, hy'.1, hy'.2]
  calc
    ∑ i, |coord (x - y) i| ≤ ∑ _i : Coord E, (5 : ℝ) := Finset.sum_le_sum fun i _ => hC i
    _ = _ := by simp [Coord, mul_comm]

/-- A unit ball about a point outside the enlarged cell misses its closed core. -/
theorem closedBall_subset_core_compl_of_notMem_gridNeighborhood
    {z : Coord E → ℤ} {x : E} (hx : x ∉ gridNeighborhood z) :
    closedBall x 1 ⊆ {y : E | ∀ i, (z i : ℝ) ≤ coord y i ∧ coord y i ≤ (z i : ℝ) + 1}ᶜ := by
  intro y hy hcore
  apply hx
  intro i
  have habs : |coord (x - y) i| ≤ 1 :=
    (abs_coord_le (x - y) i).trans (by
      rw [← dist_eq_norm, dist_comm]
      exact hy)
  have hsub : coord (x - y) i = coord x i - coord y i := by
    simpa only [coordCLM_apply, Pi.sub_apply] using congrFun ((coordCLM E).map_sub x y) i
  rw [hsub, abs_le] at habs
  have hc := hcore i
  constructor <;> linarith only [habs.1, habs.2, hc.1, hc.2]

end IsotropicVariance.Paper.Proofs.Classical
