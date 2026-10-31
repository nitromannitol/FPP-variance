/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Reparam
public import IsotropicVariance.Infra.Curves.LipschitzBounds

/-! # Agreement of curves on the parameter interval and the Lipschitz carrier bridge -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal NNReal

namespace IsotropicVariance.Infra.Curves

lemma boundedVariationOn_of_lipschitzOn {E : Type*} [PseudoMetricSpace E] {f : ℝ → E}
    {K : ℝ≥0} (h : LipschitzOnWith K f (Icc 0 1)) : BoundedVariationOn f (Icc 0 1) := by
  have hv := h.locallyBoundedVariationOn 0 1 (by simp) (by simp)
  simpa using hv

end IsotropicVariance.Infra.Curves

namespace IsotropicVariance.RectifiableCurve
open IsotropicVariance.Infra.Curves
variable {E : Type*} [PseudoMetricSpace E]

/-- A Lipschitz curve on the unit interval is rectifiable. -/
def ofLipschitzOn (f : ℝ → E) {K : ℝ≥0} (h : LipschitzOnWith K f (Icc 0 1)) :
    RectifiableCurve E := ⟨f, h.continuousOn, boundedVariationOn_of_lipschitzOn h⟩

lemma cumulativeLength_congr {γ δ : RectifiableCurve E}
    (h : EqOn γ.toFun δ.toFun (Icc 0 1)) : γ.cumulativeLength = δ.cumulativeLength := by
  funext t
  unfold cumulativeLength variationOnFromTo
  split_ifs <;> rw [eVariationOn.congr (h.mono inter_subset_left)]

lemma arcLengthMeasure_congr {γ δ : RectifiableCurve E}
    (h : EqOn γ.toFun δ.toFun (Icc 0 1)) : γ.arcLengthMeasure = δ.arcLengthMeasure := by
  have hv : γ.lengthFunction = δ.lengthFunction := by
    apply StieltjesFunction.ext
    exact congrFun (cumulativeLength_congr h)
  change γ.lengthFunction.measure = δ.lengthFunction.measure
  rw [hv]

lemma cost_congr_curve {γ δ : RectifiableCurve E} (h : EqOn γ.toFun δ.toFun (Icc 0 1))
    (ρ : E → ℝ≥0∞) : γ.cost ρ = δ.cost ρ := by
  unfold cost
  rw [arcLengthMeasure_congr h]
  apply lintegral_congr_ae
  filter_upwards [δ.ae_mem_Icc] with t ht
  rw [h ht]

end IsotropicVariance.RectifiableCurve

namespace IsotropicVariance.Infra.Curves

namespace LipCurve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u v : E}

/-- Regard the derivative-integral working carrier as a continuous rectifiable curve.
Equality of the two cost notions is a separate theorem, not part of this definition. -/
noncomputable def toRectifiable (γ : LipCurve E u v) : RectifiableCurve E :=
  RectifiableCurve.ofLipschitzOn γ.toFun γ.lipschitzOnWith.choose_spec

end LipCurve
end IsotropicVariance.Infra.Curves
