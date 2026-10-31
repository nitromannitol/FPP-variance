/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.Logarithms
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The common metric scale grows at most logarithmically with the cube size -/

@[expose] public section
namespace IsotropicVariance.Paper.Proofs.SlabComparison

/-- Polynomial cardinality and diameter bounds give the requested logarithmic stochastic
scale. Constants are chosen before the size and the finite family. -/
theorem exists_logarithmic_scale_bound {BN BD Cb Cz : ℝ} {qN qD : ℕ}
    (hBN : 1 ≤ BN) (hBD : 1 ≤ BD) (hCb : 0 < Cb) (hCz : 0 < Cz) :
    ∃ C : ℝ, 0 < C ∧ ∀ R N D : ℝ, 1 ≤ R → 1 ≤ N → 1 ≤ 2 + D →
      N ≤ BN * (2 + R) ^ qN → 2 + D ≤ BD * (2 + R) ^ qD →
      (Real.log N / Real.log 2) ^ (1 / (2 : ℝ)) * Cz +
        (3 + Real.log (2 + R) + Cb * Real.sqrt (Real.log (2 + D))) /
          Real.sqrt (Real.log 2) ≤ C * Real.log (2 + R) := by
  let a := Real.log BN / Real.log 2 + qN
  let d := Real.log BD / Real.log 2 + qD + 1 / Real.log 2
  let K := (a / Real.log 2 + 1 / Real.log 2) * Cz +
    (3 / Real.log 2 + 1 + Cb * d) / Real.sqrt (Real.log 2)
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hs : 0 < Real.sqrt (Real.log (2 : ℝ)) := Real.sqrt_pos.mpr hl
  have ha : 0 ≤ a := by
    dsimp [a]
    exact add_nonneg (div_nonneg (Real.log_nonneg hBN) hl.le) (Nat.cast_nonneg _)
  have hd : 0 ≤ d := by
    dsimp [d]
    exact add_nonneg (add_nonneg (div_nonneg (Real.log_nonneg hBD) hl.le) (Nat.cast_nonneg _)) (by positivity)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 1, by linarith, fun R N D hR hN hD hpolyN hpolyD => ?_⟩
  have hL : Real.log 2 ≤ Real.log (2 + R) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hL0 : 0 ≤ Real.log (2 + R) := hl.le.trans hL
  have hone : 1 ≤ (1 / Real.log 2) * Real.log (2 + R) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hl, one_mul]
    exact hL
  have hlogN := log_le_of_polynomial_bound hBN hR (by linarith : 0 < N) hpolyN
  change Real.log N ≤ a * Real.log (2 + R) at hlogN
  have hratio : Real.log N / Real.log 2 ≤ (a / Real.log 2) * Real.log (2 + R) := by
    have hh := div_le_div_of_nonneg_right hlogN hl.le
    convert hh using 1; ring
  have hr0 : 0 ≤ Real.log N / Real.log 2 := div_nonneg (Real.log_nonneg hN) hl.le
  have hroot : (Real.log N / Real.log 2) ^ (1 / (2 : ℝ)) ≤
      (a / Real.log 2 + 1 / Real.log 2) * Real.log (2 + R) := by
    rw [← Real.sqrt_eq_rpow]
    have hh := sqrt_le_add_one (Real.log N / Real.log 2)
    rw [max_eq_left hr0] at hh
    nlinarith
  have hrootD := sqrt_log_le_of_polynomial_bound hBD hR hD hpolyD
  change Real.sqrt (Real.log (2 + D)) ≤ d * Real.log (2 + R) at hrootD
  have hnum : 3 + Real.log (2 + R) + Cb * Real.sqrt (Real.log (2 + D)) ≤
      (3 / Real.log 2 + 1 + Cb * d) * Real.log (2 + R) := by
    have hthree : 3 ≤ (3 / Real.log 2) * Real.log (2 + R) := by
      have heq : 3 / Real.log 2 = 3 * (1 / Real.log 2) := by ring
      rw [heq]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hrootD hCb.le]
  have hfrac := div_le_div_of_nonneg_right hnum hs.le
  have hmul := mul_le_mul_of_nonneg_right hroot hCz.le
  calc
    _ ≤ (a / Real.log 2 + 1 / Real.log 2) * Real.log (2 + R) * Cz +
        (3 / Real.log 2 + 1 + Cb * d) * Real.log (2 + R) / Real.sqrt (Real.log 2) :=
      add_le_add hmul hfrac
    _ = K * Real.log (2 + R) := by dsimp [K]; ring
    _ ≤ (K + 1) * Real.log (2 + R) := by nlinarith

end IsotropicVariance.Paper.Proofs.SlabComparison
