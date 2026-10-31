/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Os.Power
public import CurvatureVariance.Infra.Os.Tail
import CurvatureVariance.Statements.Inputs.IsOsOfMeasureGeLe
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.FieldSimp

/-!
# `O₁` bounds from exponential tails with a prefactor

[AKM, Lemma A.1] turns a tail `P(X ≥ θx) ≤ e^{-x}` into `X ≤ O₁(2θ)`. The tails of Section
`sec:prelim` come with a prefactor `K ≥ 1`; shifting `X` by `θ log K` removes it, and the shift
costs the factor `e^{log K / 2}` in the exponential moment at scale `2θ`, which the concave-power
step absorbs (`isOs_one_of_measure_ge_le_mul_exp`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Infra.Os

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **`O₁` from a tail with a prefactor**: if `P(X ≥ θx) ≤ K e^{-x}` for `x ≥ 0`, with `K ≥ 1`,
then `X ≤ O₁((1 + log K / (2 log 2)) 2θ)`. -/
theorem isOs_one_of_measure_ge_le_mul_exp [IsProbabilityMeasure P] {θ K : ℝ} {X : Ω → ℝ}
    (hθ : 0 < θ) (hK : 1 ≤ K) (hX : AEMeasurable X P)
    (htail : ∀ x : ℝ, 0 ≤ x → P {ω | θ * x ≤ X ω} ≤ ENNReal.ofReal (K * Real.exp (-x))) :
    IsOs P 1 ((1 + Real.log K / (2 * Real.log 2)) * (2 * θ)) X := by
  have hK0 : 0 < K := by linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- the shifted variable has a tail without prefactor
  have hX' : IsOs P 1 (2 * θ) (fun ω => X ω - θ * Real.log K) := by
    have h := CurvatureVariance.isOs_of_measure_ge_le (s := 1) one_pos hθ (hX.sub_const _) fun x hx => by
      have hset : {ω | θ * x ≤ X ω - θ * Real.log K} = {ω | θ * (x + Real.log K) ≤ X ω} := by
        ext ω
        simp only [Set.mem_ofPred_eq]
        constructor <;> intro h <;> linarith
      rw [hset]
      refine (htail _ (by positivity)).trans (le_of_eq ?_)
      congr 1
      rw [Real.rpow_one, neg_add, Real.exp_add, Real.exp_neg (Real.log K),
        Real.exp_log hK0]
      field_simp
    have h2 : (2 : ℝ) ^ (1 / (1 : ℝ)) * θ = 2 * θ := by norm_num
    rwa [h2] at h
  have bound : (∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / (2 * θ)) ^ (1 : ℝ))) ∂P) ≤
      (2 : ℝ≥0∞) ^ (1 + Real.log K / (2 * Real.log 2)) := by
    calc (∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / (2 * θ)) ^ (1 : ℝ))) ∂P)
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (Real.log K / 2)) *
            ENNReal.ofReal (Real.exp ((max (X ω - θ * Real.log K) 0 / (2 * θ)) ^ (1 : ℝ))) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          simp only [Real.rpow_one]
          have h1 : max (X ω) 0 ≤ max (X ω - θ * Real.log K) 0 + θ * Real.log K := by
            have : 0 ≤ θ * Real.log K := by positivity
            rcases le_total (X ω) 0 with h | h
            · rw [max_eq_right h]; exact add_nonneg (le_max_right _ _) this
            · rw [max_eq_left h]; linarith [le_max_left (X ω - θ * Real.log K) 0]
          have h2 : θ * Real.log K / (2 * θ) = Real.log K / 2 := by field_simp
          calc max (X ω) 0 / (2 * θ)
              ≤ (max (X ω - θ * Real.log K) 0 + θ * Real.log K) / (2 * θ) :=
                div_le_div_of_nonneg_right h1 (by positivity)
            _ = _ := by rw [add_div, h2, add_comm]
      _ = ENNReal.ofReal (Real.exp (Real.log K / 2)) *
            ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω - θ * Real.log K) 0 / (2 * θ)) ^ (1 : ℝ)))
              ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (Real.log K / 2)) * 2 := mul_le_mul_right hX'.2 _
      _ = (2 : ℝ≥0∞) ^ (1 + Real.log K / (2 * Real.log 2)) := by
          rw [← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2),
            ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
            Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
          have : Real.log 2 * (Real.log K / (2 * Real.log 2)) = Real.log K / 2 := by
            field_simp
          rw [this]
          ring

  have key : IsOs P 1 ((1 + Real.log K / (2 * Real.log 2)) ^ (1 / (1 : ℝ)) * (2 * θ)) X :=
    isOs_of_exp_moment_le one_pos (by positivity) (le_add_of_nonneg_right (by positivity)) hX
      bound
  rwa [div_one, Real.rpow_one] at key

end CurvatureVariance.Paper.Proofs.Geometry
