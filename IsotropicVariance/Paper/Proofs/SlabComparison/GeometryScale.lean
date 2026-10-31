/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.CurveDirections

/-! # A fixed multiple of the random scale squared for all geometric arguments -/

@[expose] public section
namespace IsotropicVariance.Paper.Proofs.SlabComparison

/-- This deliberately generous constant gives cone error `1/24` after dyadic summation. -/
def geometryScale (A : ℝ) : ℝ :=
  noReturnScale A + (192 : ℝ) ^ 4 * (6 * (3 * A + 1)) ^ 2 + 9

lemma geometryScale_ge_eight {A : ℝ} (hA : 0 ≤ A) : 8 ≤ geometryScale A := by
  have hNR : 0 ≤ noReturnScale A := by unfold noReturnScale; positivity
  unfold geometryScale
  nlinarith [sq_nonneg (6 * (3 * A + 1))]

/-- The geometric radius meets the no-return, directional and fixed-distance thresholds. -/
theorem geometryScale_properties {A S : ℝ} (hA : 0 ≤ A) (hS : 1 ≤ S) :
    8 ≤ geometryScale A * S ^ 2 ∧ S ^ 2 ≤ geometryScale A * S ^ 2 ∧
      noReturnScale A * S ^ 2 < geometryScale A * S ^ 2 ∧
      (6 * (3 * A + 1)) ^ 2 * S ^ 2 ≤
        (1 / 192 : ℝ) ^ 4 * (geometryScale A * S ^ 2) := by
  have hK := geometryScale_ge_eight hA
  have hSsq : 1 ≤ S ^ 2 := by nlinarith
  have hNR : 0 ≤ noReturnScale A := by unfold noReturnScale; positivity
  have hNRK : noReturnScale A + 1 ≤ geometryScale A := by
    unfold geometryScale
    nlinarith [sq_nonneg (6 * (3 * A + 1))]
  have hsmall : (6 * (3 * A + 1)) ^ 2 ≤ (1 / 192 : ℝ) ^ 4 * geometryScale A := by
    unfold geometryScale
    norm_num
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hSsq (by linarith : 0 ≤ geometryScale A)]
  · nlinarith [mul_le_mul_of_nonneg_right hK (sq_nonneg S)]
  · nlinarith [mul_le_mul_of_nonneg_right hNRK (sq_nonneg S)]
  · have hh := mul_le_mul_of_nonneg_right hsmall (sq_nonneg S)
    nlinarith

end IsotropicVariance.Paper.Proofs.SlabComparison
