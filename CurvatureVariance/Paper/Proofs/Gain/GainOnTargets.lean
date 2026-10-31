/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Proofs.Gain.Basic
import CurvatureVariance.Infra.FPP.Walks

/-!
# Proposition `prop:gain` on the targets of Section `sec:gain`: arithmetic

Two estimates for the last sentence of the proof of Proposition `prop:gain`:
`rpow_two_delta_div_le_two` (`K^{2δ/K} ≤ 2`) and `K_mul_Q_sq_le`
(`K Q_n² = K^{2δ/K} Q_ℓ² ≤ 2 Q_ℓ²`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

/-- `K^{2δ/K} ≤ 2` for `K ≥ 10⁴` and `δ ≤ 1`. -/
theorem rpow_two_delta_div_le_two {K : ℕ} (hK : 10 ^ 4 ≤ K) {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (K : ℝ) ^ (2 * δ / K) ≤ 2 := by
  have hK1 : (10 : ℝ) ^ 4 ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  rw [Real.rpow_def_of_pos hKpos]
  have hlog : Real.log K ≤ (K : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2) :=
    Real.log_le_rpow_div hKpos.le (by norm_num)
  have hsqrt : (K : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt K := (Real.sqrt_eq_rpow K).symm
  rw [hsqrt] at hlog
  have hs100 : (100 : ℝ) ≤ Real.sqrt K := by
    rw [Real.le_sqrt' (by norm_num)]
    norm_num at hK1 ⊢
    linarith
  have hsK : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hKpos.le
  have hexp : Real.log K * (2 * δ / K) ≤ Real.log 2 := by
    have hl0 : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
    have h1 : Real.log K * (2 * δ / K) ≤ Real.log K * (2 / K) := by
      refine mul_le_mul_of_nonneg_left ?_ hl0
      exact div_le_div_of_nonneg_right (by linarith) hKpos.le
    have h2 : Real.log K * (2 / K) ≤ 4 / Real.sqrt K := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
      have : Real.log K * 2 ≤ 4 * Real.sqrt K := by linarith
      calc Real.log K * 2 * (K : ℝ)⁻¹ ≤ 4 * Real.sqrt K * (K : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = 4 * (Real.sqrt K)⁻¹ := by
            have hs0 : 0 < Real.sqrt K := by linarith
            have hinv : (K : ℝ)⁻¹ = (Real.sqrt K)⁻¹ * (Real.sqrt K)⁻¹ := by
              rw [← mul_inv, hsK]
            rw [hinv]
            field_simp
    have h3 : 4 / Real.sqrt K ≤ 1 / 25 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have h4 : (1 : ℝ) / 25 ≤ Real.log 2 := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at this ⊢
      linarith
    linarith
  calc Real.exp (Real.log K * (2 * δ / K)) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 hexp
    _ = 2 := Real.exp_log (by norm_num)

/-- **`K Q_n² = K^{2δ/K} Q_ℓ² ≤ 2 Q_ℓ²`** for `ℓ = Kn` (the last sentence of the proof of
Proposition `prop:gain`). -/
theorem K_mul_Q_sq_le {m : ℕ} (M : Model m) (hMs : M.Standing) {K n ℓ : ℕ} (hK : 10 ^ 4 ≤ K)
    (hℓ : ℓ = K * n) (A : ℝ) :
    (K : ℝ) * Q M K A n ^ 2 ≤ 2 * Q M K A ℓ ^ 2 := by
  have hKpos : (0 : ℝ) < K := by
    have : (10 : ℝ) ^ 4 ≤ K := by exact_mod_cast hK
    linarith
  set e : ℝ := (1 : ℝ) / 2 - M.δ / K with he
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hQℓ : Q M K A ℓ = (K : ℝ) ^ e * Q M K A n := by
    simp only [Q, hℓ, Nat.cast_mul, ← he]
    rw [Real.mul_rpow hKpos.le hn0]; ring
  have hsplit : (K : ℝ) = (K : ℝ) ^ (2 * M.δ / K) * ((K : ℝ) ^ e) ^ 2 := by
    rw [← Real.rpow_natCast ((K : ℝ) ^ e) 2, ← Real.rpow_mul hKpos.le,
      ← Real.rpow_add hKpos, he]
    conv_lhs => rw [← Real.rpow_one (K : ℝ)]
    congr 1
    push_cast
    ring
  rw [hQℓ, mul_pow]
  have hb := rpow_two_delta_div_le_two hK hMs.delta_pos.le hMs.delta_le_one
  have hQ2 : 0 ≤ ((K : ℝ) ^ e) ^ 2 * Q M K A n ^ 2 := by positivity
  calc (K : ℝ) * Q M K A n ^ 2
      = (K : ℝ) ^ (2 * M.δ / K) * (((K : ℝ) ^ e) ^ 2 * Q M K A n ^ 2) := by
        rw [← mul_assoc, ← hsplit]
    _ ≤ 2 * (((K : ℝ) ^ e) ^ 2 * Q M K A n ^ 2) := mul_le_mul_of_nonneg_right hb hQ2

end CurvatureVariance.Paper.Gain
