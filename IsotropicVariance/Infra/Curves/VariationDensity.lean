/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Calculus
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Variation of a Lipschitz curve as an integral of its speed

The vector Stieltjes measure of a continuous BV curve agrees, on each bounded interval,
with the vector measure with density its derivative, by the Lipschitz FTC. Taking total
variation then identifies arc length with the integral of the norm of the derivative.
-/

@[expose] public section
open Set MeasureTheory Function
open scoped ENNReal NNReal Topology

namespace IsotropicVariance.Infra.Curves
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma vectorMeasure_Ioc_eq_integral_deriv {f : ℝ → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hv : BoundedVariationOn f univ) (a b : ℝ) :
    hv.vectorMeasure (Ioc a b) = ∫ t in Ioc a b, deriv f t := by
  rcases le_or_gt a b with hab | hab
  · rw [hv.vectorMeasure_Ioc hab]
    have hr : rightLim f = f := funext fun t =>
      hf.continuous.continuousAt.continuousWithinAt.rightLim_eq
    rw [hr, ← intervalIntegral.integral_of_le hab, integral_deriv_eq_sub_of_lipschitz hf]
  · simp [Ioc_eq_empty_of_le hab.le]

lemma vectorMeasure_restrict_eq_withDensity_deriv {f : ℝ → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hv : BoundedVariationOn f univ) (a b : ℝ) :
    hv.vectorMeasure.restrict (Ioc a b) =
      (volume.restrict (Ioc a b)).withDensityᵥ (deriv f) := by
  have hint : Integrable (deriv f) (volume.restrict (Ioc a b)) :=
    (integrableOn_deriv_of_lipschitz hf a b).mono_set Ioc_subset_Icc_self
  apply VectorMeasure.ext_of_generateFrom {s : Set ℝ | ∃ c d, c < d ∧ Ioc c d = s}
  · rintro s ⟨c, d, hcd, rfl⟩
    rw [VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Ioc,
      withDensityᵥ_apply hint measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
    rw [Ioc_inter_Ioc, vectorMeasure_Ioc_eq_integral_deriv hf hv]
  · exact (borel_eq_generateFrom_Ioc ℝ)
  · exact isPiSystem_Ioc id id
  · rw [VectorMeasure.restrict_apply_univ, withDensityᵥ_apply hint MeasurableSet.univ,
      setIntegral_univ, vectorMeasure_Ioc_eq_integral_deriv hf hv]

/-- Total variation equals the lower integral of the speed on a bounded interval. -/
theorem eVariationOn_Icc_eq_lintegral_speed {f : ℝ → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hv : BoundedVariationOn f univ) (a b : ℝ) :
    eVariationOn f (Icc a b) = ∫⁻ t in Icc a b, ‖deriv f t‖ₑ := by
  have h := congrArg (fun v : VectorMeasure ℝ E => v.variation univ)
    (vectorMeasure_restrict_eq_withDensity_deriv hf hv a b)
  have hint : Integrable (deriv f) (volume.restrict (Ioc a b)) :=
    (integrableOn_deriv_of_lipschitz hf a b).mono_set Ioc_subset_Icc_self
  rw [VectorMeasure.variation_restrict measurableSet_Ioc, Measure.restrict_apply_univ,
    hv.variation_vectorMeasure_Ioc, Measure.variation_withDensityᵥ hint,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  have hr : rightLim f = f := funext fun t =>
    hf.continuous.continuousAt.continuousWithinAt.rightLim_eq
  rw [hr, eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt
    hf.continuous.continuousAt.continuousWithinAt, restrict_Ioc_eq_restrict_Icc] at h
  exact h

end IsotropicVariance.Infra.Curves
