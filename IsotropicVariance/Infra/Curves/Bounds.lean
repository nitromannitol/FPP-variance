/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.SpeedMeasure

/-! # Endpoint and segment bounds for the literal rectifiable cost -/

@[expose] public section
open Set MeasureTheory
open scoped NNReal ENNReal

namespace IsotropicVariance.Infra.Curves

lemma _root_.IsotropicVariance.RectifiableCurve.edist_endpoints_le_length {E : Type*}
    [PseudoMetricSpace E] (γ : RectifiableCurve E) : edist (γ.toFun 0) (γ.toFun 1) ≤ γ.length :=
  eVariationOn.edist_le γ.toFun (by simp) (by simp)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma LipCurve.toRectifiable_length {u v : E} (γ : LipCurve E u v) :
    γ.toRectifiable.length = γ.length := by
  borelize E
  have h := γ.toRectifiable_cost (ρ := fun _ => 1) measurable_const
  simp only [ENNReal.coe_one] at h
  rw [γ.toRectifiable.cost_const 1, one_mul] at h
  simpa [LipCurve.cost, LipCurve.arcCost, LipCurve.length, LipCurve.arcLength,
    LipCurve.arcIntegral] using h

/-- A straight segment has its Euclidean endpoint distance as rectifiable length. -/
theorem rectifiable_length_segment (u v : E) :
    (segment u v).toRectifiable.length = ‖v - u‖ₑ := by
  rw [LipCurve.toRectifiable_length, length_segment]

/-- The literal rectifiable and derivative-integral formulations of passage cost have the same
infimum, with fixed endpoints. -/
theorem iInf_cost_rectifiable_eq_derivative [MeasurableSpace E] [BorelSpace E]
    {ρ : E → ℝ≥0} (hρ : Measurable ρ) (u v : E) :
    (⨅ γ : RectifiableCurve E, ⨅ (_ : γ.toFun 0 = u), ⨅ (_ : γ.toFun 1 = v),
      γ.cost (fun x => (ρ x : ℝ≥0∞))) = ⨅ γ : LipCurve E u v, γ.cost ρ := by
  have hmeas : Measurable (fun x => (ρ x : ℝ≥0∞)) := by fun_prop
  rw [iInf_cost_rectifiable_eq_lipschitz hmeas]
  exact iInf_congr fun γ => γ.toRectifiable_cost hρ

end IsotropicVariance.Infra.Curves
