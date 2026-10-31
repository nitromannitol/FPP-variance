/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scale comparisons for Lemma `lem:smallmean`

The lower growth bound for `Q_s`, harmless integer rounding of `W_s`, and the curvature error
estimate used in the proof of Lemma `lem:smallmean`. All constants are uniform in `K ≥ 10⁴` and
`A ≥ 1`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper

/-- The exponent of `Q` lies above `49/100` for every allowed `K`. -/
theorem mean_Q_exponent_lower {m : ℕ} {M : Model m} (hM : M.Standing)
    {K : ℕ} (hK : 10 ^ 4 ≤ K) :
    (49 : ℝ) / 100 ≤ (1 : ℝ) / 2 - M.δ / K := by
  have hKR : (10000 : ℝ) ≤ K := by exact_mod_cast hK
  have hq : M.δ / K ≤ (1 : ℝ) / 10000 := by
    exact div_le_div₀ (by positivity) hM.delta_le_one (by norm_num) hKR
  linarith only [hq]

/-- The fluctuation scale grows at least as `s^{49/100}`. -/
theorem mean_Q_lower {m : ℕ} {M : Model m} (hM : M.Standing)
    {K : ℕ} (hK : 10 ^ 4 ≤ K) {A s : ℝ} (hA : 1 ≤ A) (hs : 1 ≤ s) :
    s ^ ((49 : ℝ) / 100) ≤ Q M K A s := by
  exact (Real.rpow_le_rpow_of_exponent_le hs (mean_Q_exponent_lower hM hK)).trans
    (le_mul_of_one_le_left (Real.rpow_nonneg (by linarith only [hs]) _) hA)

/-- At positive integer scales the rounded width is at most twice the real width. -/
theorem mean_wInt_le_two_W {m : ℕ} {M : Model m} (hM : M.Standing)
    {K : ℕ} (hK : 10 ^ 4 ≤ K) {A s : ℝ} (hA : 1 ≤ A) (hs : 1 ≤ s) :
    (wInt M K A s : ℝ) ≤ 2 * W M K A s := by
  have hQ1 : 1 ≤ Q M K A s :=
    (Real.one_le_rpow hs (by norm_num : (0 : ℝ) ≤ 49 / 100)).trans (mean_Q_lower hM hK hA hs)
  have hW1 : 1 ≤ W M K A s := by
    rw [W, Real.one_le_sqrt]
    exact one_le_mul_of_one_le_of_one_le hs hQ1
  have hw := Nat.ceil_lt_add_one (show 0 ≤ W M K A s from (zero_lt_one.trans_le hW1).le)
  change (wInt M K A s : ℝ) < W M K A s + 1 at hw
  linarith only [hW1, hw]

end CurvatureVariance.Paper.Mean
