/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.VariationDensity
public import IsotropicVariance.Infra.Curves.Clamped
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.Linarith

/-! # Arc-length measure of a Lipschitz curve -/

@[expose] public section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace IsotropicVariance.RectifiableCurve
open IsotropicVariance.Infra.Curves
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma deriv_clamped_ae (γ : RectifiableCurve E) :
    deriv γ.clamped =ᵐ[volume.restrict (Icc 0 1)] deriv γ.toFun := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  exact (show EqOn γ.clamped γ.toFun (Ioo 0 1) from
    fun t ht => γ.clamped_eq ⟨ht.1.le, ht.2.le⟩).deriv isOpen_Ioo

lemma arcLengthMeasure_eq_withDensity_clamped (γ : RectifiableCurve E) {K : ℝ≥0}
    (hγ : LipschitzOnWith K γ.toFun (Icc 0 1)) :
    γ.arcLengthMeasure = (volume.restrict (Icc 0 1)).withDensity
      (fun t => ‖deriv γ.clamped t‖ₑ) := by
  let ν := (volume.restrict (Icc (0 : ℝ) 1)).withDensity (fun t => ‖deriv γ.clamped t‖ₑ)
  have hν : ∀ᵐ t ∂ν, t ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    change ((volume.restrict (Icc (0 : ℝ) 1)).withDensity
      (fun t => ‖deriv γ.clamped t‖ₑ)) (Icc (0 : ℝ) 1)ᶜ = 0
    rw [withDensity_apply _ (measurableSet_Icc (a := (0 : ℝ)) (b := 1)).compl, Measure.restrict_restrict measurableSet_Icc.compl]
    simp
  have hv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      γ.arcLengthMeasure (Iic t) = ν (Iic t) := by
    rw [γ.arcLengthMeasure_Iic]
    dsimp [ν]
    rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have heq : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
      ext x
      constructor
      · intro h; exact ⟨h.2.1, h.1⟩
      · intro h; exact ⟨h.2, h.1, h.2.trans ht.2⟩
    rw [heq, ← eVariationOn_Icc_eq_lintegral_speed (γ.lipschitzWith_clamped hγ)
      γ.boundedVariationOn_clamped]
    rw [γ.cumulativeLength_eq ht, variationOnFromTo.eq_of_le _ _ ht.1]
    have heq' : Icc (0 : ℝ) 1 ∩ Icc 0 t = Icc 0 t := by
      exact inter_eq_right.mpr (Icc_subset_Icc le_rfl ht.2)
    rw [heq', ENNReal.ofReal_toReal]
    · exact (eVariationOn.congr (fun x hx => γ.clamped_eq (Icc_subset_Icc le_rfl ht.2 hx))).symm
    · exact ne_top_of_le_ne_top γ.boundedVariationOn
        (eVariationOn.mono _ (Icc_subset_Icc le_rfl ht.2))
  have hmass : γ.arcLengthMeasure univ = ν univ := by
    rw [γ.arcLengthMeasure_univ]
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← eVariationOn_Icc_eq_lintegral_speed (γ.lipschitzWith_clamped hγ) γ.boundedVariationOn_clamped]
    exact (eVariationOn.congr (fun x hx => γ.clamped_eq hx)).symm
  have h := map_eq_of_cumulative_Icc γ.arcLengthMeasure ν γ.ae_mem_Icc hν
    continuous_id (monotone_id.monotoneOn _) rfl rfl hmass hv
  simpa only [Measure.map_id] using h

/-- The Stieltjes arc-length measure of a Lipschitz curve has density equal to its speed. -/
theorem arcLengthMeasure_eq_withDensity (γ : RectifiableCurve E) {K : ℝ≥0}
    (hγ : LipschitzOnWith K γ.toFun (Icc 0 1)) :
    γ.arcLengthMeasure = (volume.restrict (Icc 0 1)).withDensity
      (fun t => ‖deriv γ.toFun t‖ₑ) := by
  rw [γ.arcLengthMeasure_eq_withDensity_clamped hγ]
  apply withDensity_congr_ae
  exact γ.deriv_clamped_ae.fun_comp (fun x : E => ‖x‖ₑ)

/-- Arc-length cost agrees with the derivative integral for a Lipschitz curve. -/
theorem cost_eq_lintegral_speed [MeasurableSpace E] [BorelSpace E]
    (γ : RectifiableCurve E) {K : ℝ≥0} (hγ : LipschitzOnWith K γ.toFun (Icc 0 1))
    {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) :
    γ.cost ρ = ∫⁻ t in Icc 0 1, ρ (γ.toFun t) * ‖deriv γ.toFun t‖ₑ := by
  rw [γ.cost_eq_lintegral_clamped, γ.arcLengthMeasure_eq_withDensity hγ]
  change (∫⁻ t, (ρ ∘ γ.clamped) t ∂(volume.restrict (Icc 0 1)).withDensity
    (fun t => ‖deriv γ.toFun t‖ₑ)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_deriv γ.toFun).enorm
      (hρ.comp γ.continuous_clamped.measurable)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change ‖deriv γ.toFun t‖ₑ * ρ (γ.clamped t) = _
  rw [γ.clamped_eq ht, mul_comm]

end IsotropicVariance.RectifiableCurve

namespace IsotropicVariance.Infra.Curves.LipCurve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {u v : E}

/-- The working derivative cost and the literal rectifiable cost agree. -/
theorem toRectifiable_cost (γ : LipCurve E u v) {ρ : E → ℝ≥0} (hρ : Measurable ρ) :
    γ.toRectifiable.cost (fun x => (ρ x : ℝ≥0∞)) = γ.cost ρ := by
  have hmeas : Measurable (fun x => (ρ x : ℝ≥0∞)) := by fun_prop
  rw [γ.toRectifiable.cost_eq_lintegral_speed γ.lipschitzOnWith.choose_spec hmeas]
  rfl

end IsotropicVariance.Infra.Curves.LipCurve
