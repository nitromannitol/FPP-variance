/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoiseProps.Covariance
public import IsotropicVariance.Infra.WhiteNoiseProps.AEInfo
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Passing spatial L² approximations through white noise

The prescribed second moments turn spatial L² errors into mean-square errors of evaluations,
hence convergence in probability and measurable representatives for regional information.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Filter
open scoped Distributions ENNReal Topology

namespace IsotropicVariance.Infra.WhiteNoiseProps

open Example

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [MeasurableSpace Ω]
  {W : Ω → WhiteNoiseConfig E} {P : Measure Ω}

/-- The mean-square evaluation error is exactly the spatial square error. -/
theorem integral_sq_sub_eval (h : IsWhiteNoise W P) (φ ψ : 𝓓((⊤ : Opens E), ℝ)) :
    (∫ ω, (W ω φ - W ω ψ) ^ 2 ∂P) = ∫ x, (φ x - ψ x) ^ 2 := by
  have hv := variance_eval_eq_integral h (φ - ψ)
  rw [variance_eq_integral (measurable_eval h (φ - ψ)).aemeasurable,
    integral_eval h (φ - ψ)] at hv
  simpa only [sub_zero, map_sub, FunLike.coe_sub, Pi.sub_apply] using hv

/-- Spatial L² convergence of test functions gives convergence in probability of evaluations. -/
theorem tendstoInMeasure_eval (h : IsWhiteNoise W P) (ψ : ℕ → 𝓓((⊤ : Opens E), ℝ))
    (φ : 𝓓((⊤ : Opens E), ℝ))
    (hsq : Tendsto (fun n => ∫ x, (ψ n x - φ x) ^ 2) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => W ω (ψ n)) atTop (fun ω => W ω φ) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
  have heq (n) : eLpNorm ((fun ω => W ω (ψ n)) - (fun ω => W ω φ)) 2 P =
      ENNReal.ofReal ((∫ x, (ψ n x - φ x) ^ 2) ^ (1 / 2 : ℝ)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      ((memLp_eval h (ψ n)).sub (memLp_eval h φ))]
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Pi.sub_apply, Real.rpow_two, sq_abs]
    rw [integral_sq_sub_eval h (ψ n) φ]
    norm_num
  simp_rw [heq]
  have hroot : Tendsto (fun n => (∫ x, (ψ n x - φ x) ^ 2) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa using hsq.rpow_const (p := (1 / 2 : ℝ)) (Or.inr (by norm_num))
  have hh := (ENNReal.continuous_ofReal.tendsto 0).comp hroot
  simpa only [Function.comp_def, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), ENNReal.ofReal_zero] using hh

end IsotropicVariance.Infra.WhiteNoiseProps
