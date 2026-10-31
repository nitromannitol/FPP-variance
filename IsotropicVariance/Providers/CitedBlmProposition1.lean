/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance
import IsotropicVariance.Infra.EfronStein.FiniteExtended

/-!
# Proof of `IsotropicVariance.Cited.blm_proposition1`

Proves `IsotropicVariance.Providers.Cited.blm_proposition1`, [BLM03, Proposition 1, p. 1584],
the Efron–Stein inequality, with exactly the type of the theorem
`IsotropicVariance.Cited.blm_proposition1` stated in
`IsotropicVariance.Statements.Cited.BlmProposition1`. The statement module proves its theorem from
this one and is not imported here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IsotropicVariance.Providers

/-- [BLM03, Proposition 1, p. 1584], in `[0, ∞]`, with no moment hypothesis. -/
theorem Cited.blm_proposition1 (n : ℕ) {𝒳 : Fin n → Type*} [∀ i, MeasurableSpace (𝒳 i)]
    (μ : ∀ i, Measure (𝒳 i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, 𝒳 i) → ℝ) (hf : Measurable f) :
    evariance f (Measure.pi μ) ≤
      (1 / 2 : ℝ≥0∞) * ∑ i, ∫⁻ x, ∫⁻ y, ‖f x - f (Function.update x i y)‖ₑ ^ 2 ∂μ i
        ∂Measure.pi μ :=
  Infra.EfronStein.evariance_le_half_sum_refresh_energy_fin μ f hf

end IsotropicVariance.Providers
