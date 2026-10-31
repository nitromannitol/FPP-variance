/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-! # The deterministic error scale in the classical mean estimate

The scale `g(t) = sqrt(t log(2+t))` of the second bound of Lemma `lem:classical` is sublinear, and
`g(2t) ≤ ψ g(t)` with `ψ = 7/4 < 2`, as [HN, Lemma 4.2] requires.
-/

@[expose] public section
open Real
namespace IsotropicVariance.Paper.Proofs.Classical

/-- The classical nonrandom fluctuation scale. -/
noncomputable def errorScale (t : ℝ) : ℝ := sqrt (t * log (2 + t))

/-- The error scale is nonnegative. -/
theorem errorScale_nonneg (t : ℝ) : 0 ≤ errorScale t := sqrt_nonneg _

/-- The error scale is increasing on the nonnegative half-line. -/
theorem errorScale_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : errorScale s ≤ errorScale t := by
  apply sqrt_le_sqrt
  exact mul_le_mul hst
    (log_le_log (by linarith only [hs] : 0 < 2 + s) (by linarith only [hst] : 2 + s ≤ 2 + t))
    (log_nonneg (by linarith only [hs] : 1 ≤ 2 + s)) (hs.trans hst)

/-- The error scale is strictly positive at every positive parameter. -/
theorem errorScale_pos {t : ℝ} (ht : 0 < t) : 0 < errorScale t :=
  sqrt_pos.mpr (mul_pos ht (log_pos (by linarith only [ht] : 1 < 2 + t)))

/-- Its square has the expected value for nonnegative parameters. -/
theorem errorScale_sq {t : ℝ} (ht : 0 ≤ t) : errorScale t ^ 2 = t * log (2 + t) :=
  sq_sqrt (mul_nonneg ht (log_nonneg (by linarith only [ht])))

/-- Its dyadic growth is bounded by `7/4 < 2` from scale two onward. -/
theorem errorScale_two_mul_le {t : ℝ} (ht : 2 ≤ t) :
    errorScale (2 * t) ≤ (7 / 4 : ℝ) * errorScale t := by
  have ht0 : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ 2).trans ht
  have hLog : log (2 + 2 * t) ≤ (3 / 2 : ℝ) * log (2 + t) := by
    have h1 := log_le_log (by linarith only [ht] : 0 < 2 + 2 * t)
      (by linarith only [ht] : 2 + 2 * t ≤ 2 * (2 + t))
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith only [ht] : 2 + t ≠ 0)] at h1
    have h2 := log_le_log (by norm_num : (0 : ℝ) < 2 * 2)
      (by linarith only [ht] : 2 * 2 ≤ 2 + t)
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at h2
    linarith only [h1, h2]
  apply (sq_le_sq₀ (errorScale_nonneg _) (mul_nonneg (by norm_num) (errorScale_nonneg _))).mp
  have h1 := errorScale_sq ht0
  have h2 := errorScale_sq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht0)
  have hh := mul_le_mul_of_nonneg_left hLog (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht0)
  have hPos := mul_nonneg ht0 (log_nonneg (by linarith only [ht] : 1 ≤ 2 + t))
  nlinarith only [h1, h2, hh, hPos]

end IsotropicVariance.Paper.Proofs.Classical
