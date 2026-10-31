/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Rectifiable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Arc-length measure on the parameter interval

The arc-length measure has no atoms and is supported on `[0,1]`. Consequently costs depend
only on the density along the curve on this interval. Finite bounded densities also have a
real-valued cost, defined by taking the real value of their nonnegative integral.
-/

@[expose] public section
open Set MeasureTheory Filter Function
open scoped ENNReal NNReal Topology

namespace IsotropicVariance.RectifiableCurve
variable {E : Type*} [PseudoMetricSpace E]

lemma arcLengthMeasure_Iic (γ : RectifiableCurve E) (t : ℝ) :
    γ.arcLengthMeasure (Iic t) = ENNReal.ofReal (γ.cumulativeLength t) := by
  simpa [arcLengthMeasure, lengthFunction] using γ.lengthFunction.measure_Iic γ.cumulativeLength_tendsto_atBot t

lemma arcLengthMeasure_singleton (γ : RectifiableCurve E) (t : ℝ) :
    γ.arcLengthMeasure {t} = 0 := by
  rw [arcLengthMeasure, StieltjesFunction.measure_singleton]
  have h : leftLim γ.lengthFunction t = γ.lengthFunction t :=
    γ.continuous_cumulativeLength.continuousAt.continuousWithinAt.leftLim_eq
  rw [h, sub_self, ENNReal.ofReal_zero]

instance (γ : RectifiableCurve E) : NullSingletonClass γ.arcLengthMeasure :=
  ⟨γ.arcLengthMeasure_singleton⟩

lemma arcLengthMeasure_compl_Icc (γ : RectifiableCurve E) :
    γ.arcLengthMeasure (Icc 0 1)ᶜ = 0 := by
  have hleft : γ.arcLengthMeasure (Iio 0) = 0 := by
    apply measure_mono_null Iio_subset_Iic_self
    rw [γ.arcLengthMeasure_Iic, γ.cumulativeLength_of_nonpos le_rfl, ENNReal.ofReal_zero]
  have hright : γ.arcLengthMeasure (Ioi 1) = 0 := by
    simpa [arcLengthMeasure, lengthFunction, cumulativeLength_of_one_le γ le_rfl] using
      γ.lengthFunction.measure_Ioi γ.cumulativeLength_tendsto_atTop 1
  have heq : (Icc (0 : ℝ) 1)ᶜ = Iio 0 ∪ Ioi 1 := by
    ext t
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
  rw [heq]
  exact measure_union_null hleft hright

lemma ae_mem_Icc (γ : RectifiableCurve E) : ∀ᵐ t ∂γ.arcLengthMeasure, t ∈ Icc (0 : ℝ) 1 :=
  ae_iff.mpr γ.arcLengthMeasure_compl_Icc

lemma restrict_arcLengthMeasure_Icc (γ : RectifiableCurve E) :
    γ.arcLengthMeasure.restrict (Icc 0 1) = γ.arcLengthMeasure :=
  Measure.restrict_eq_self_of_ae_mem γ.ae_mem_Icc

lemma cost_congr (γ : RectifiableCurve E) {ρ σ : E → ℝ≥0∞}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ρ (γ.toFun t) = σ (γ.toFun t)) : γ.cost ρ = γ.cost σ := by
  apply lintegral_congr_ae
  filter_upwards [γ.ae_mem_Icc] with t ht
  exact h t ht

lemma cost_ne_top (γ : RectifiableCurve E) {ρ : E → ℝ≥0∞} {b : ℝ≥0∞}
    (hb : b ≠ ⊤) (h : ∀ x, ρ x ≤ b) : γ.cost ρ ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top hb γ.length_ne_top) (γ.cost_le_mul_length h)

end IsotropicVariance.RectifiableCurve
