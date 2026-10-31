/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The log-sum inequality for series, and the final algebra of a variance inequality

We prove the log-sum inequality `A log (A / B) ≤ ∑ aₙ log (aₙ / bₙ)` for nonnegative series,
and the elementary algebra turning `V log (V / B) ≤ L A` into a bound on `V`.
-/

@[expose] public section

open Real

namespace CurvatureVariance.Infra.Entropy

/-- Pointwise form of the log-sum inequality. -/
theorem mul_log_add_sub_le_mul_log_div {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b = 0 → a = 0) (hc : 0 < c) :
    a * log c + a - c * b ≤ a * log (a / b) := by
  rcases hb.eq_or_lt with h | h
  · subst h
    simp [hab rfl.symm]
  rcases ha.eq_or_lt with h' | h'
  · subst h'
    simp only [zero_mul, zero_add, zero_sub, zero_div, log_zero, mul_zero]
    nlinarith [mul_pos hc h]
  · have hcb : 0 < c * b := mul_pos hc h
    have h1 : log (a / b) = log (a / (c * b)) + log c := by
      rw [← log_mul (by positivity) hc.ne']
      congr 1
      field_simp
    have h2 : log (c * b / a) ≤ c * b / a - 1 := log_le_sub_one_of_pos (by positivity)
    have h3 : log (c * b / a) = - log (a / (c * b)) := by
      rw [← log_inv, inv_div]
    rw [h3] at h2
    have h4 : a * (-log (a / (c * b))) ≤ a * (c * b / a - 1) :=
      mul_le_mul_of_nonneg_left h2 ha
    have h5 : a * (c * b / a - 1) = c * b - a := by field_simp
    rw [h1]
    nlinarith

/-- The log-sum inequality for series: with `A = ∑ aₙ` and `B = ∑ bₙ`,
`A log (A / B) ≤ ∑ aₙ log (aₙ / bₙ)`. -/
theorem mul_log_div_le_tsum {a b : ℕ → ℝ} {A B : ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hab : ∀ n, b n = 0 → a n = 0) (hA : HasSum a A) (hB : HasSum b B)
    (hs : Summable fun n => a n * log (a n / b n)) :
    A * log (A / B) ≤ ∑' n, a n * log (a n / b n) := by
  have hA0 : 0 ≤ A := hA.nonneg ha
  have hB0 : 0 ≤ B := hB.nonneg hb
  rcases hA0.eq_or_lt with h | hApos
  · have hz : ∀ n, a n = 0 := fun n =>
      le_antisymm (h ▸ le_hasSum hA n fun m _ => ha m) (ha n)
    simp [← h, hz]
  have hBpos : 0 < B := by
    rcases hB0.eq_or_lt with h | h
    · exfalso
      have hz : ∀ n, a n = 0 := fun n =>
        hab n (le_antisymm (h ▸ le_hasSum hB n fun m _ => hb m) (hb n))
      have h0 : a = fun _ => 0 := funext hz
      have : A = 0 := hA.unique (h0 ▸ hasSum_zero)
      linarith
    · exact h
  set c := A / B with hc
  have hcpos : 0 < c := div_pos hApos hBpos
  have hcB : c * B = A := by rw [hc]; field_simp
  have hf : HasSum (fun n => a n * log c + a n - c * b n) (A * log c + A - c * B) :=
    ((hA.mul_right (log c)).add hA).sub (hB.mul_left c)
  have := hasSum_le (fun n => mul_log_add_sub_le_mul_log_div (ha n) (hb n) (hab n) hcpos)
    hf hs.hasSum
  rw [hs.hasSum.tsum_eq] at *
  rw [hcB] at this
  linarith [hs.hasSum.tsum_eq]

end CurvatureVariance.Infra.Entropy
