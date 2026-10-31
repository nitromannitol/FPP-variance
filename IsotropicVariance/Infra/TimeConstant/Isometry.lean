/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.TimeConstant.Bounds

/-! # Isometric transport of literal rectifiable passage times

Transport the curve, its variation, and its arc-length measure together. This
justifies translation of endpoints in the stationarity argument.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace IsotropicVariance.Infra.TimeConstant
open Curves
variable {E : Type*} [MetricSpace E] [MeasurableSpace E]

omit [MeasurableSpace E] in
/-- An isometry preserves variation on every parameter set. -/
theorem eVariationOn_isometry {F : Type*} [MetricSpace F] {g : E → F} (hg : Isometry g)
    (f : ℝ → E) (s : Set ℝ) : eVariationOn (g ∘ f) s = eVariationOn f s := by
  simp only [eVariationOn, Function.comp_apply, hg.edist_eq]

/-- Transport a rectifiable curve by an isometry. -/
def mapCurve (g : E ≃ᵢ E) (γ : RectifiableCurve E) : RectifiableCurve E where
  toFun := g ∘ γ.toFun
  continuousOn := g.continuous.comp_continuousOn γ.continuousOn
  boundedVariationOn := by
    simpa only [BoundedVariationOn, eVariationOn_isometry g.isometry] using γ.boundedVariationOn

omit [MeasurableSpace E] in
/-- Isometric transport preserves the cumulative length function. -/
theorem cumulativeLength_mapCurve (g : E ≃ᵢ E) (γ : RectifiableCurve E) :
    (mapCurve g γ).cumulativeLength = γ.cumulativeLength := by
  funext t
  simp only [RectifiableCurve.cumulativeLength, variationOnFromTo, mapCurve,
    eVariationOn_isometry g.isometry]

omit [MeasurableSpace E] in
/-- Isometric transport preserves the parameter-line arc-length measure. -/
theorem arcLengthMeasure_mapCurve (g : E ≃ᵢ E) (γ : RectifiableCurve E) :
    (mapCurve g γ).arcLengthMeasure = γ.arcLengthMeasure := by
  have heq : (mapCurve g γ).lengthFunction = γ.lengthFunction :=
    StieltjesFunction.ext (congrFun (cumulativeLength_mapCurve g γ))
  change (mapCurve g γ).lengthFunction.measure = γ.lengthFunction.measure
  rw [heq]

omit [MeasurableSpace E] in
/-- Moving a curve is equivalent to pulling the density back along the isometry. -/
theorem cost_mapCurve (g : E ≃ᵢ E) (γ : RectifiableCurve E) (ρ : E → ℝ≥0∞) :
    (mapCurve g γ).cost ρ = γ.cost (ρ ∘ g) := by
  unfold RectifiableCurve.cost
  rw [arcLengthMeasure_mapCurve]
  rfl

omit [MeasurableSpace E] in
/-- Isometric covariance of the literal extended passage time. -/
theorem passageTime_comp_isometry (g : E ≃ᵢ E) (ρ : E → ℝ≥0∞) (u v : E) :
    Measurability.passageTime ρ (g u) (g v) = Measurability.passageTime (ρ ∘ g) u v := by
  have h (g : E ≃ᵢ E) (ρ : E → ℝ≥0∞) (u v : E) :
      Measurability.passageTime ρ (g u) (g v) ≤ Measurability.passageTime (ρ ∘ g) u v := by
    refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => ?_
    exact (iInf_le_of_le (mapCurve g γ) (iInf_le_of_le (congrArg g h0)
      (iInf_le _ (congrArg g h1)))).trans_eq (cost_mapCurve g γ ρ)
  refine le_antisymm (h g ρ u v) ?_
  have hh := h g.symm (ρ ∘ g) (g u) (g v)
  simpa only [IsometryEquiv.symm_apply_apply, Function.comp_def,
    IsometryEquiv.apply_symm_apply] using hh

/-- Isometric covariance for real densities and real passage times. -/
theorem passage_comp_isometry (g : E ≃ᵢ E) (σ : E → ℝ) (u v : E) :
    passage σ (g u) (g v) = passage (σ ∘ g) u v := by
  unfold passage
  rw [passageTime_comp_isometry]
  rfl

end IsotropicVariance.Infra.TimeConstant
