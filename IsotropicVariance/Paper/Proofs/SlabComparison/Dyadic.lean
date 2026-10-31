/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.Directions
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Summing the direction errors on dyadic radii

A fourth-power bound proportional to the inverse radius is summed using the rational ratio
`7/8`. Since `2 * (7/8)^4 ≥ 1`, this dominates the quarter-power dyadic decay without real-power
identities. The total directional error is at most eight times the initial error scale.
-/

@[expose] public section
open Finset
namespace IsotropicVariance.Paper.Proofs.SlabComparison

lemma fourth_power_dyadic_le {δ ε R K : ℝ} (hε : 0 ≤ ε) (hR : 0 < R) (j : ℕ)
    (hδ : δ ^ 4 * (R * 2 ^ j) ≤ K) (hK : K ≤ ε ^ 4 * R) :
    δ ≤ ε * (7 / 8 : ℝ) ^ j := by
  have hpow : (1 : ℝ) ≤ (2 * (7 / 8 : ℝ) ^ 4) ^ j := one_le_pow₀ (by norm_num)
  have hnonneg : 0 ≤ ε ^ 4 * R := by positivity
  have hbound := mul_le_mul_of_nonneg_left hpow hnonneg
  have heq : (ε ^ 4 * R) * (2 * (7 / 8 : ℝ) ^ 4) ^ j =
      (ε * (7 / 8 : ℝ) ^ j) ^ 4 * (R * 2 ^ j) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    ring
  rw [heq, mul_one] at hbound
  have hδpow : δ ^ 4 ≤ (ε * (7 / 8 : ℝ) ^ j) ^ 4 :=
    (mul_le_mul_iff_of_pos_right (show 0 < R * (2 : ℝ) ^ j by positivity)).mp
      (hδ.trans (hK.trans hbound))
  exact le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity) hδpow

lemma sum_seven_eighths (n : ℕ) :
    ∑ j ∈ range n, (7 / 8 : ℝ) ^ j = 8 * (1 - (7 / 8 : ℝ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

/-- A dyadic chain of fourth-power direction bounds has uniformly bounded total variation. -/
theorem dyadic_chain_direction_bound {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (n : ℕ) {ε R K : ℝ} (hε : 0 ≤ ε) (hR : 0 < R)
    (hstep : ∀ j < n, ‖x (j + 1) - x j‖ ^ 4 * (R * 2 ^ j) ≤ K)
    (hK : K ≤ ε ^ 4 * R) : ‖x n - x 0‖ ≤ 8 * ε := by
  have hdist := dist_le_range_sum_dist x n
  rw [dist_eq_norm'] at hdist
  calc
    _ ≤ ∑ j ∈ range n, dist (x j) (x (j + 1)) := hdist
    _ ≤ ∑ j ∈ range n, ε * (7 / 8 : ℝ) ^ j := by
      apply sum_le_sum
      intro j hj
      rw [dist_eq_norm']
      exact fourth_power_dyadic_le hε hR j (hstep j (mem_range.mp hj)) hK
    _ = ε * (8 * (1 - (7 / 8 : ℝ) ^ n)) := by rw [← mul_sum, sum_seven_eighths]
    _ ≤ 8 * ε := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 8) n]

end IsotropicVariance.Paper.Proofs.SlabComparison
