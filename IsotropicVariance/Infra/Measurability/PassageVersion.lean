/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.PassageBounds
public import IsotropicVariance.Infra.Measurability.ContinuousVersion

/-! # One jointly Borel passage-time version for all endpoints -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace IsotropicVariance.Infra.Measurability
variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- A jointly Borel passage-time version agrees with the literal rectifiable infimum at every
endpoint pair simultaneously, on one full-measure event. The values are real since a bounded
density gives finite passage times. The construction uses a countable dense set of endpoint
pairs and the uniform endpoint Lipschitz bound. -/
theorem exists_jointlyMeasurable_passageTime_version
    (μ : Measure Ω) [SFinite μ] {ρ : Ω × E → ℝ≥0∞} (hρ : Measurable ρ)
    {b : ℝ≥0} (hb : ∀ ω x, ρ (ω, x) ≤ b) :
    ∃ T : Ω → E × E → ℝ, Measurable (Function.uncurry T) ∧
      (∀ ω, Continuous (T ω)) ∧
      ∀ᵐ ω ∂μ, ∀ p : E × E, T ω p = (passageTime (fun x => ρ (ω, x)) p.1 p.2).toReal := by
  apply exists_jointlyMeasurable_version
  · intro ω
    exact (lipschitzWith_passageTime (hρ.comp (measurable_const.prodMk measurable_id))
      (hb ω)).continuous
  · intro p
    exact (nullMeasurable_passageTime μ hρ p.1 p.2).aemeasurable.ennreal_toReal

end IsotropicVariance.Infra.Measurability
