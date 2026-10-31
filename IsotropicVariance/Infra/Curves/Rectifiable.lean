/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.Order.ProjIcc
public import IsotropicVariance.Statements.Curves.RectifiableCurveCost
public import IsotropicVariance.Statements.Curves.RectifiableCurveLength
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Continuous rectifiable curves and their arc-length measures

Curves are continuous on the parameter interval `[0,1]` and have finite metric variation there.
Values outside the parameter interval play no role. The cumulative variation is extended
constantly at both ends, and its Stieltjes measure is the arc-length measure. Thus the cost
of a Borel density is defined without taking a derivative of a merely rectifiable curve.

The curves, their length, cumulative length, arc-length measure and cost are the
declarations `IsotropicVariance.RectifiableCurve` and friends (`IsotropicVariance.Statements.Curves`);
this file adds their basic properties, in the namespace of the structure so that dot notation
applies.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace IsotropicVariance.RectifiableCurve

variable {E : Type*} [PseudoMetricSpace E]

lemma length_ne_top (γ : RectifiableCurve E) : γ.length ≠ ⊤ := γ.boundedVariationOn

lemma cumulativeLength_eq (γ : RectifiableCurve E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    γ.cumulativeLength t = variationOnFromTo γ.toFun (Icc 0 1) 0 t := by
  simp [cumulativeLength, projIcc_of_mem zero_le_one ht]

lemma cumulativeLength_of_nonpos (γ : RectifiableCurve E) {t : ℝ} (ht : t ≤ 0) :
    γ.cumulativeLength t = 0 := by
  simp [cumulativeLength, projIcc_of_le_left zero_le_one ht, variationOnFromTo.self]

lemma cumulativeLength_of_one_le (γ : RectifiableCurve E) {t : ℝ} (ht : 1 ≤ t) :
    γ.cumulativeLength t = γ.length.toReal := by
  simp [cumulativeLength, projIcc_of_right_le zero_le_one ht,
    variationOnFromTo.eq_of_le _ _ zero_le_one, length]

lemma cumulativeLength_tendsto_atBot (γ : RectifiableCurve E) :
    Tendsto γ.cumulativeLength atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
  exact (γ.cumulativeLength_of_nonpos ht).symm

lemma cumulativeLength_tendsto_atTop (γ : RectifiableCurve E) :
    Tendsto γ.cumulativeLength atTop (𝓝 γ.length.toReal) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  exact (γ.cumulativeLength_of_one_le ht).symm

lemma arcLengthMeasure_univ (γ : RectifiableCurve E) : γ.arcLengthMeasure univ = γ.length := by
  rw [arcLengthMeasure, StieltjesFunction.measure_univ γ.lengthFunction
    γ.cumulativeLength_tendsto_atBot γ.cumulativeLength_tendsto_atTop, sub_zero,
    ENNReal.ofReal_toReal γ.length_ne_top]

instance (γ : RectifiableCurve E) : IsFiniteMeasure γ.arcLengthMeasure :=
  ⟨γ.arcLengthMeasure_univ ▸ γ.length_ne_top.lt_top⟩

lemma cost_const (γ : RectifiableCurve E) (c : ℝ≥0∞) : γ.cost (fun _ => c) = c * γ.length := by
  simp [cost, γ.arcLengthMeasure_univ]

lemma cost_mono (γ : RectifiableCurve E) {ρ σ : E → ℝ≥0∞} (h : ∀ x, ρ x ≤ σ x) :
    γ.cost ρ ≤ γ.cost σ := lintegral_mono fun _ => h _

lemma mul_length_le_cost (γ : RectifiableCurve E) {ρ : E → ℝ≥0∞} {a : ℝ≥0∞}
    (h : ∀ x, a ≤ ρ x) : a * γ.length ≤ γ.cost ρ := by
  rw [← γ.cost_const a]
  exact γ.cost_mono h

lemma cost_le_mul_length (γ : RectifiableCurve E) {ρ : E → ℝ≥0∞} {b : ℝ≥0∞}
    (h : ∀ x, ρ x ≤ b) : γ.cost ρ ≤ b * γ.length := by
  rw [← γ.cost_const b]
  exact γ.cost_mono h

end IsotropicVariance.RectifiableCurve
