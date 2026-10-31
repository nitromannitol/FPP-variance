/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance
import CurvatureVariance.Infra.EfronStein.FiniteExtended

/-!
# Provider of `CurvatureVariance.blm_proposition1`

Proves `CurvatureVariance.Providers.blm_proposition1`, [BLM03, Proposition 1, p. 1584], the
Efron–Stein inequality, with exactly the type of the statement
`CurvatureVariance.Statements.Inputs.BlmProposition1`, from
`Infra.EfronStein.evariance_le_half_sum_refresh_energy_fin`, as the continuum library proves
`IsotropicVariance.Providers.Cited.blm_proposition1`. The statement is proved by `by exact` of this
theorem applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CurvatureVariance.Providers

/-- [BLM03, Proposition 1, p. 1584], in `[0, ∞]`, with no moment hypothesis. -/
theorem blm_proposition1 (n : ℕ) {𝒳 : Fin n → Type*} [∀ i, MeasurableSpace (𝒳 i)]
    (μ : ∀ i, Measure (𝒳 i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, 𝒳 i) → ℝ) (hf : Measurable f) :
    evariance f (Measure.pi μ) ≤
      (1 / 2 : ℝ≥0∞) * ∑ i, ∫⁻ x, ∫⁻ y, ‖f x - f (Function.update x i y)‖ₑ ^ 2 ∂μ i
        ∂Measure.pi μ :=
  Infra.EfronStein.evariance_le_half_sum_refresh_energy_fin μ f hf

end CurvatureVariance.Providers
