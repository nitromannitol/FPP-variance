/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.Approximation

/-! # Local perturbations of literal curve cost

If the densities agree away from a region, the cost increase is paid only
between the first and last visits to that region. All estimates use the
literal arc-length measure, including curves that stop or retrace.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.Classical

/-- If every affected point on a curve occurs in one parameter interval, the
cost increase is bounded by the upper density times that interval's arc length. -/
theorem cost_perturb_le_interval {E : Type*} [MetricSpace E] (γ : RectifiableCurve E)
    (ρ ρ' : E → ℝ≥0∞) {K : Set E} {B : ℝ≥0∞} (hB : ∀ x, ρ' x ≤ B)
    (hAgree : ∀ x ∉ K, ρ' x = ρ x) {a b : ℝ}
    (hVisits : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ K → t ∈ Icc a b) :
    γ.cost ρ' ≤ γ.cost ρ + B * γ.arcLengthMeasure (Icc a b) := by
  let I : ℝ → ℝ≥0∞ := (Icc a b).indicator (fun _ => B)
  have hI : Measurable I := measurable_const.indicator measurableSet_Icc
  calc
    _ ≤ ∫⁻ t, ρ (γ.toFun t) + I t ∂γ.arcLengthMeasure := by
      apply lintegral_mono_ae
      filter_upwards [γ.ae_mem_Icc] with t ht
      by_cases htab : t ∈ Icc a b
      · rw [show I t = B from indicator_of_mem htab _]
        exact (hB _).trans (le_add_left le_rfl)
      · have hNot : γ.toFun t ∉ K := fun h => htab (hVisits t ht h)
        rw [hAgree _ hNot, show I t = 0 from indicator_of_notMem htab _, add_zero]
    _ = γ.cost ρ + ∫⁻ t, I t ∂γ.arcLengthMeasure := lintegral_add_right _ hI
    _ = _ := by rw [lintegral_indicator_const measurableSet_Icc B]

/-- If the curve avoids the perturbation region, its cost is unchanged. -/
theorem cost_eq_of_avoids {E : Type*} [MetricSpace E] (γ : RectifiableCurve E)
    (ρ ρ' : E → ℝ≥0∞) {K : Set E} (hAgree : ∀ x ∉ K, ρ' x = ρ x)
    (hAvoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∉ K) : γ.cost ρ' = γ.cost ρ := by
  apply lintegral_congr_ae
  filter_upwards [γ.ae_mem_Icc] with t ht
  exact hAgree _ (hAvoid t ht)

end IsotropicVariance.Paper.Proofs.Classical
