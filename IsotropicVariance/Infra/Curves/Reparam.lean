/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.ReparamMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic.FunProp

/-!
# Monotone reparametrization of rectifiable curves

Continuous nondecreasing changes of parameter fixing zero and one preserve both length and
cost. The proof pushes the arc-length measure forward, including when the parameter map has
flat intervals. No differentiability of the original curve or the parameter map is used.
-/

@[expose] public section
open Set MeasureTheory Function
open scoped ENNReal Topology

namespace IsotropicVariance.RectifiableCurve
open IsotropicVariance.Infra.Curves
variable {E : Type*} [PseudoMetricSpace E]

/-- Extend a curve constantly outside `[0,1]`. -/
noncomputable def clamped (γ : RectifiableCurve E) (t : ℝ) : E :=
  γ.toFun (projIcc 0 1 zero_le_one t)

lemma continuous_clamped (γ : RectifiableCurve E) : Continuous γ.clamped :=
  γ.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun t => (projIcc 0 1 zero_le_one t).property)

lemma clamped_eq (γ : RectifiableCurve E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    γ.clamped t = γ.toFun t := by simp [clamped, projIcc_of_mem zero_le_one ht]

/-- Reparametrize by a continuous monotone map of the interval onto itself. -/
def reparam (γ : RectifiableCurve E) (φ : ℝ → ℝ) (hc : Continuous φ)
    (hm : MonotoneOn φ (Icc 0 1)) (h0 : φ 0 = 0) (h1 : φ 1 = 1) : RectifiableCurve E where
  toFun := γ.toFun ∘ φ
  continuousOn := γ.continuousOn.comp hc.continuousOn
    (mapsTo_Icc_of_monotoneOn_endpoints hm h0 h1)
  boundedVariationOn := ne_top_of_le_ne_top γ.boundedVariationOn
    (eVariationOn.comp_le_of_monotoneOn γ.toFun φ hm
      (mapsTo_Icc_of_monotoneOn_endpoints hm h0 h1))

lemma cumulativeLength_reparam (γ : RectifiableCurve E) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hm : MonotoneOn φ (Icc 0 1)) (h0 : φ 0 = 0) (h1 : φ 1 = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (γ.reparam φ hc hm h0 h1).cumulativeLength t = γ.cumulativeLength (φ t) := by
  have himage : φ '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    simpa [h0, h1] using hc.continuousOn.image_Icc_of_monotoneOn zero_le_one hm
  have hφt := mapsTo_Icc_of_monotoneOn_endpoints hm h0 h1 ht
  simp only [cumulativeLength, projIcc_of_mem zero_le_one ht,
    projIcc_of_mem zero_le_one hφt, Subtype.coe_mk, reparam]
  rw [variationOnFromTo.comp_eq_of_monotoneOn γ.toFun φ hm (by simp) ht, himage, h0]

lemma length_reparam (γ : RectifiableCurve E) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hm : MonotoneOn φ (Icc 0 1)) (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    (γ.reparam φ hc hm h0 h1).length = γ.length := by
  have h := γ.cumulativeLength_reparam hc hm h0 h1 (t := 1) (by simp)
  rw [h1, cumulativeLength_of_one_le _ le_rfl, cumulativeLength_of_one_le _ le_rfl] at h
  calc
    _ = ENNReal.ofReal (γ.reparam φ hc hm h0 h1).length.toReal :=
      (ENNReal.ofReal_toReal (length_ne_top _)).symm
    _ = ENNReal.ofReal γ.length.toReal := congrArg ENNReal.ofReal h
    _ = _ := ENNReal.ofReal_toReal γ.length_ne_top

lemma map_arcLengthMeasure_reparam (γ : RectifiableCurve E) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hm : MonotoneOn φ (Icc 0 1)) (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    (γ.reparam φ hc hm h0 h1).arcLengthMeasure.map φ = γ.arcLengthMeasure := by
  apply map_eq_of_cumulative_Icc _ _ (ae_mem_Icc _) γ.ae_mem_Icc hc hm h0 h1
  · rw [arcLengthMeasure_univ, arcLengthMeasure_univ, γ.length_reparam hc hm h0 h1]
  · intro t ht
    rw [arcLengthMeasure_Iic, arcLengthMeasure_Iic, γ.cumulativeLength_reparam hc hm h0 h1 ht]

lemma cost_eq_lintegral_clamped (γ : RectifiableCurve E) (ρ : E → ℝ≥0∞) :
    γ.cost ρ = ∫⁻ t, ρ (γ.clamped t) ∂γ.arcLengthMeasure := by
  apply lintegral_congr_ae
  filter_upwards [γ.ae_mem_Icc] with t ht
  rw [γ.clamped_eq ht]

/-- Monotone continuous endpoint-preserving reparametrization preserves every Borel cost. -/
theorem cost_reparam [MeasurableSpace E] [BorelSpace E] (γ : RectifiableCurve E)
    {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hm : MonotoneOn φ (Icc 0 1)) (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    (γ.reparam φ hc hm h0 h1).cost ρ = γ.cost ρ := by
  rw [γ.cost_eq_lintegral_clamped ρ, ← γ.map_arcLengthMeasure_reparam hc hm h0 h1]
  change _ = ∫⁻ t, (ρ ∘ γ.clamped) t ∂Measure.map φ _
  rw [lintegral_map (hρ.comp γ.continuous_clamped.measurable) hc.measurable]
  apply lintegral_congr_ae
  filter_upwards [(γ.reparam φ hc hm h0 h1).ae_mem_Icc] with t ht
  exact congrArg ρ (γ.clamped_eq
    (mapsTo_Icc_of_monotoneOn_endpoints hm h0 h1 ht)).symm

end IsotropicVariance.RectifiableCurve
