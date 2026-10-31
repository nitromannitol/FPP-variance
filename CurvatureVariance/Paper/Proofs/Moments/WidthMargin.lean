/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The width margin, the first bound of equation `eq:scales`

Under the range of the amplitude `Q_N ≤ C_* √(N log(2 + N))` (equation `eq:regime`),
`W_s / s^{3/4+δ/100} → 0` as `N → ∞`, uniformly in `s ≥ √N/16` (`W_s/s^{3/4+δ/100} =
√A s^{−δ/(2K)−δ/100} ≤ C N^{δ/(2K)−δ/200} log^{1/4}(2 + N)`, and `K > 100`).

* `eventually_log_two_add_le_rpow`: `log(2 + N) ≤ c N^r` for `N` large, for all `c, r > 0`.
* `W_le_of_le`: the deterministic comparison `W_s ≤ η s^{3/4+δ/100}` from `A ≤ η² s^{δ/50+δ/K}`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper

variable {m : ℕ}

/-- For `r, c > 0`, eventually `log (2 + N) ≤ c N^r`. -/
theorem eventually_log_two_add_le_rpow {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Real.log (2 + N) ≤ c * (N : ℝ) ^ r := by
  have h1 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ c / 2 * x ^ r := by
    have h := (isLittleO_log_rpow_atTop hr).bound (half_pos hc)
    filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (by positivity)] at hx
  have h2 : ∀ᶠ x : ℝ in atTop, Real.log 3 ≤ c / 2 * x ^ r :=
    ((tendsto_rpow_atTop hr).const_mul_atTop (half_pos hc)).eventually_ge_atTop _
  have h : ∀ᶠ x : ℝ in atTop, Real.log (2 + x) ≤ c * x ^ r := by
    filter_upwards [h1, h2, eventually_ge_atTop 1] with x h1 h2 hx
    have h3 : Real.log (2 + x) ≤ Real.log 3 + Real.log x := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by linarith) (by linarith)
    linarith
  exact tendsto_natCast_atTop_atTop.eventually h

/-- The deterministic comparison behind the first bound of equation `eq:scales`: if
`A ≤ η² s^{δ/50 + δ/K}` then `W_s ≤ η s^{3/4 + δ/100}`. -/
theorem W_le_of_le (M : Model m) (K : ℕ) {A s η : ℝ} (hs : 0 < s) (hη : 0 ≤ η)
    (h : A ≤ η ^ 2 * s ^ (M.δ / 50 + M.δ / K)) :
    W M K A s ≤ η * s ^ ((3 : ℝ) / 4 + M.δ / 100) := by
  unfold W Q
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hs1 : s * (A * s ^ ((1 : ℝ) / 2 - M.δ / K)) = A * s ^ ((1 : ℝ) + (1 / 2 - M.δ / K)) := by
    rw [Real.rpow_add hs, Real.rpow_one]; ring
  have hs2 : (η * s ^ ((3 : ℝ) / 4 + M.δ / 100)) ^ 2 =
      η ^ 2 * s ^ ((M.δ / 50 + M.δ / K) + (1 + (1 / 2 - M.δ / K))) := by
    rw [mul_pow, sq (s ^ _), ← Real.rpow_add hs]
    congr 2
    ring
  rw [hs1, hs2, Real.rpow_add hs (M.δ / 50 + M.δ / K), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h (by positivity)

end CurvatureVariance.Paper.Moments
