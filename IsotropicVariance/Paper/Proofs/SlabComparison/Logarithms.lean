/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Logarithmic bounds for polynomially many mesh pairs -/

@[expose] public section
namespace IsotropicVariance.Paper.Proofs.SlabComparison

/-- A fixed polynomial upper bound gives a uniform multiple of `log(2+R)` after taking logs. -/
lemma log_le_of_polynomial_bound {B R N : ℝ} {q : ℕ}
    (hB : 1 ≤ B) (hR : 1 ≤ R) (hN : 0 < N) (hpoly : N ≤ B * (2 + R) ^ q) :
    Real.log N ≤ (Real.log B / Real.log 2 + q) * Real.log (2 + R) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ Real.log (2 + R) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hLB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hconst : Real.log B ≤ (Real.log B / Real.log 2) * Real.log (2 + R) := by
    have hh := mul_le_mul_of_nonneg_left hL (div_nonneg hLB hlog2.le)
    rw [div_mul_cancel₀ _ hlog2.ne'] at hh
    exact hh
  calc
    Real.log N ≤ Real.log (B * (2 + R) ^ q) := Real.log_le_log hN hpoly
    _ = Real.log B + (q : ℝ) * Real.log (2 + R) := by
      rw [Real.log_mul (by linarith : B ≠ 0) (by positivity), Real.log_pow]
    _ ≤ _ := by nlinarith

/-- A deliberately coarse square-root estimate suffices for the desired logarithmic scale. -/
lemma sqrt_le_add_one (x : ℝ) : Real.sqrt x ≤ max x 0 + 1 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]
  · simp [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx), max_eq_right (le_of_not_ge hx)]

/-- Square roots of polynomial logarithms are bounded by a fixed multiple of `log(2+R)`.
Using the coarser logarithmic bound avoids unnecessary fractional-power algebra. -/
lemma sqrt_log_le_of_polynomial_bound {B R N : ℝ} {q : ℕ}
    (hB : 1 ≤ B) (hR : 1 ≤ R) (hN : 1 ≤ N) (hpoly : N ≤ B * (2 + R) ^ q) :
    Real.sqrt (Real.log N) ≤
      (Real.log B / Real.log 2 + q + 1 / Real.log 2) * Real.log (2 + R) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ Real.log (2 + R) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogN := log_le_of_polynomial_bound hB hR (by linarith : 0 < N) hpoly
  have hs := sqrt_le_add_one (Real.log N)
  rw [max_eq_left (Real.log_nonneg hN)] at hs
  have hone : 1 ≤ (1 / Real.log 2) * Real.log (2 + R) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hlog2, one_mul]
    exact hL
  nlinarith

end IsotropicVariance.Paper.Proofs.SlabComparison
