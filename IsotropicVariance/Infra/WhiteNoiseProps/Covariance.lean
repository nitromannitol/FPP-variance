/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoiseProps.Gaussian
public import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The white-noise covariance identity

Polarization of the prescribed variances identifies the covariance with the spatial L² pairing.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Distributions ENNReal

namespace IsotropicVariance.Infra.WhiteNoiseProps

open Example

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)] [MeasurableSpace Ω]
  {W : Ω → WhiteNoiseConfig E} {P : Measure Ω}

/-- Products of test functions are spatially integrable. -/
theorem integrable_test_mul (φ ψ : 𝓓((⊤ : Opens E), ℝ)) :
    Integrable (fun x => φ x * ψ x) :=
  (φ.continuous.mul ψ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right

omit [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)] in
/-- Spatial square integrals are finite and nonnegative, so no truncation occurs in the variance. -/
theorem variance_eval_eq_integral (h : IsWhiteNoise W P) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    Var[fun ω => W ω φ; P] = ∫ x, φ x ^ 2 := by
  rw [variance_eval h φ, Real.coe_toNNReal']
  exact max_eq_left (integral_nonneg (fun x => sq_nonneg (φ x)))

/-- The covariance of two test-function evaluations is their spatial L² inner product. -/
theorem covariance_eval (h : IsWhiteNoise W P) (φ ψ : 𝓓((⊤ : Opens E), ℝ)) :
    cov[fun ω => W ω φ, fun ω => W ω ψ; P] = ∫ x, φ x * ψ x := by
  have := isProbabilityMeasure h
  have heq : (fun ω => W ω φ) + (fun ω => W ω ψ) = (fun ω => W ω (φ + ψ)) := by
    funext ω
    exact ((W ω).map_add φ ψ).symm
  have hv := variance_add (memLp_eval h φ) (memLp_eval h ψ)
  rw [heq, variance_eval_eq_integral h (φ + ψ), variance_eval_eq_integral h φ,
    variance_eval_eq_integral h ψ] at hv
  have hφ : Integrable (fun x => φ x ^ 2) := by
    simpa only [pow_two] using integrable_test_mul φ φ
  have hψ : Integrable (fun x => ψ x ^ 2) := by
    simpa only [pow_two] using integrable_test_mul ψ ψ
  have hi : (∫ x, (φ + ψ) x ^ 2) =
      (∫ x, φ x ^ 2) + 2 * (∫ x, φ x * ψ x) + (∫ x, ψ x ^ 2) := by
    have hp : (fun x => (φ + ψ) x ^ 2) =
        (fun x => φ x ^ 2 + 2 * (φ x * ψ x) + ψ x ^ 2) := by
      funext x
      change (φ x + ψ x) ^ 2 = _
      ring
    have hsum : Integrable (fun x => φ x ^ 2 + 2 * (φ x * ψ x)) :=
      hφ.add ((integrable_test_mul φ ψ).const_mul 2)
    rw [hp, integral_add hsum hψ,
      integral_add hφ ((integrable_test_mul φ ψ).const_mul 2), integral_const_mul]
  linarith only [hv, hi]

end IsotropicVariance.Infra.WhiteNoiseProps
