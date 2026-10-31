/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Example.LocalDensity
public import IsotropicVariance.Infra.Curves.Main
public import IsotropicVariance.Statements.Curves.PassageTime
public import IsotropicVariance.Statements.Noise.IsWhiteNoise
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Evaluation laws of the white-noise predicate

These consequences use only the definitions of the model, imported through `Infra.Example`; no
construction or additional independence hypothesis is imposed on white noise.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Distributions ENNReal

namespace IsotropicVariance.Infra.WhiteNoiseProps

open Example

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [MeasurableSpace Ω] {W : Ω → WhiteNoiseConfig E} {P : Measure Ω}

/-- White noise is carried by a probability measure, as follows already from its zero marginal. -/
theorem isProbabilityMeasure (h : IsWhiteNoise W P) : IsProbabilityMeasure P :=
  (h.2 0).isProbabilityMeasure

/-- Every test-function evaluation is measurable. -/
theorem measurable_eval (h : IsWhiteNoise W P) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    Measurable (fun ω => W ω φ) :=
  (Example.measurable_whiteNoise_eval φ).comp h.1

/-- Every marginal of the white noise is Gaussian. -/
theorem hasGaussianLaw_eval (h : IsWhiteNoise W P) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    HasGaussianLaw (fun ω => W ω φ) P := (h.2 φ).hasGaussianLaw

/-- Every evaluation has mean zero. -/
theorem integral_eval (h : IsWhiteNoise W P) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    (∫ ω, W ω φ ∂P) = 0 := by
  have hh := (h.2 φ).integral_comp (show AEStronglyMeasurable (fun x : ℝ => x)
    (gaussianReal 0 (∫ x, φ x ^ 2).toNNReal) from measurable_id.aestronglyMeasurable)
  simpa only [Function.comp_def, integral_id_gaussianReal] using hh

/-- The evaluation variance is its prescribed spatial quadratic integral. -/
theorem variance_eval (h : IsWhiteNoise W P) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    Var[fun ω => W ω φ; P] = (∫ x, φ x ^ 2).toNNReal := by
  rw [← variance_id_map (measurable_eval h φ).aemeasurable, (h.2 φ).map_eq,
    variance_id_gaussianReal]

/-- Gaussian evaluations are square-integrable. -/
theorem memLp_eval (h : IsWhiteNoise W P) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    MemLp (fun ω => W ω φ) 2 P := (hasGaussianLaw_eval h φ).memLp_two

end IsotropicVariance.Infra.WhiteNoiseProps
