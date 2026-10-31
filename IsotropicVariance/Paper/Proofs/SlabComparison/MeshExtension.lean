/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.TimeConstant.SettingBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

/-! # Extending the uniform metric estimate from a unit mesh

This is the Lipschitz extension step of the proof of Lemma `lem:straight`, from the integer points
to the whole ball. The finite maximum used to construct the random scale only needs to control
pairs of mesh points.
-/

@[expose] public section
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper

/-- A bounded perturbation of a distance has a bounded perturbation of its square root. -/
lemma sqrt_le_sqrt_add_two {d d' : ℝ} (hd : 0 ≤ d) (hdd : d' ≤ d + 2) :
    Real.sqrt d' ≤ Real.sqrt d + 2 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt hd, Real.sqrt_nonneg d]

/-- Endpoint Lipschitz continuity extends a unit-mesh estimate to every nearby pair. -/
theorem metric_error_of_nearby_pair {m : ℕ} (X : Setting m) (ω : X.Ω)
    {A S b : ℝ} (hA : 0 ≤ A) (hS : 1 ≤ S) (hb : 0 ≤ b)
    (hLip : ∀ u v u' v',
      |X.passTime ω u v - X.passTime ω u' v'| ≤ b * (dist u u' + dist v v'))
    {u v u' v' : Pt m} (hu : dist u u' ≤ 1) (hv : dist v v' ≤ 1)
    (hgrid : |X.passTime ω u' v' - dist u' v'| ≤
      A * (S * Real.sqrt (dist u' v') + S ^ 2)) :
    |X.passTime ω u v - dist u v| ≤
      (3 * A + 2 * b + 2) * (S * Real.sqrt (dist u v) + S ^ 2) := by
  have hd : |dist u' v' - dist u v| ≤ 2 := by
    rw [abs_le]
    constructor
    · have h1 := dist_triangle u u' v'
      have h2 := dist_triangle u v' v
      rw [dist_comm v' v] at h2
      linarith
    · have h1 := dist_triangle u' u v
      have h2 := dist_triangle u' v v'
      rw [dist_comm u' u] at h1
      linarith
  have hd' : dist u' v' ≤ dist u v + 2 := by linarith [(abs_le.mp hd).2]
  have hsqrt := sqrt_le_sqrt_add_two dist_nonneg hd'
  have hlip := hLip u v u' v'
  have hlip' : |X.passTime ω u v - X.passTime ω u' v'| ≤ 2 * b :=
    hlip.trans (by nlinarith)
  have hsum : |X.passTime ω u v - dist u v| ≤
      |X.passTime ω u v - X.passTime ω u' v'| +
      |X.passTime ω u' v' - dist u' v'| + |dist u' v' - dist u v| := by
    calc
      _ = |(X.passTime ω u v - X.passTime ω u' v') +
          (X.passTime ω u' v' - dist u' v') + (dist u' v' - dist u v)| := by congr 1; ring
      _ ≤ _ := abs_add_three _ _ _
  have hS0 : 0 ≤ S := by linarith
  have hSsq : 1 ≤ S ^ 2 := by nlinarith
  have hSmul : S * Real.sqrt (dist u' v') ≤ S * Real.sqrt (dist u v) + 2 * S := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hS0]
  have hbase : 1 ≤ S * Real.sqrt (dist u v) + S ^ 2 := by nlinarith [mul_nonneg hS0 (Real.sqrt_nonneg (dist u v))]
  have hAgrid : A * (S * Real.sqrt (dist u' v') + S ^ 2) ≤
      3 * A * (S * Real.sqrt (dist u v) + S ^ 2) := by
    have hinner : S * Real.sqrt (dist u' v') + S ^ 2 ≤
        3 * (S * Real.sqrt (dist u v) + S ^ 2) := by
      nlinarith [mul_nonneg hS0 (Real.sqrt_nonneg (dist u v))]
    nlinarith [mul_le_mul_of_nonneg_left hinner hA]
  have hbbase := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 2 * b + 2 by positivity)
  linarith

end IsotropicVariance.Paper.Proofs.SlabComparison
