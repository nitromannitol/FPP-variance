/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Reparam
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Rectifiable subarcs and their costs -/

@[expose] public section
open Set MeasureTheory Filter Function
open scoped ENNReal Topology

namespace IsotropicVariance.Infra.Curves

def subParam (a b t : ℝ) : ℝ := a + t * (b - a)

lemma subParam_mono {a b : ℝ} (hab : a ≤ b) : Monotone (subParam a b) := by
  intro s t hst
  dsimp [subParam]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hst (sub_nonneg.mpr hab))

lemma subParam_mapsTo {a b : ℝ} (hab : a ≤ b) :
    MapsTo (subParam a b) (Icc 0 1) (Icc a b) := by
  intro t ht
  constructor
  · simpa [subParam] using subParam_mono hab ht.1
  · simpa [subParam] using subParam_mono hab ht.2

end IsotropicVariance.Infra.Curves

namespace IsotropicVariance.RectifiableCurve
open IsotropicVariance.Infra.Curves
variable {E : Type*} [PseudoMetricSpace E]

lemma arcLengthMeasure_Icc (γ : RectifiableCurve E) (a b : ℝ) :
    γ.arcLengthMeasure (Icc a b) =
      ENNReal.ofReal (γ.cumulativeLength b - γ.cumulativeLength a) := by
  have hl : leftLim γ.lengthFunction a = γ.cumulativeLength a :=
    γ.continuous_cumulativeLength.continuousAt.continuousWithinAt.leftLim_eq
  change γ.lengthFunction.measure (Icc a b) = _
  rw [StieltjesFunction.measure_Icc, hl]
  rfl

/-- The subarc from parameter `a` to parameter `b`, linearly parametrized on `[0,1]`. -/
def subcurve (γ : RectifiableCurve E) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    RectifiableCurve E where
  toFun := γ.toFun ∘ subParam a b
  continuousOn := γ.continuousOn.comp (by fun_prop [subParam])
    ((subParam_mapsTo hab).mono_right (Icc_subset_Icc ha hb))
  boundedVariationOn := ne_top_of_le_ne_top γ.boundedVariationOn
    (eVariationOn.comp_le_of_monotoneOn γ.toFun (subParam a b) ((subParam_mono hab).monotoneOn _)
      ((subParam_mapsTo hab).mono_right (Icc_subset_Icc ha hb)))

lemma cumulativeLength_subcurve (γ : RectifiableCurve E) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (γ.subcurve a b ha hab hb).cumulativeLength t =
      γ.cumulativeLength (subParam a b t) - γ.cumulativeLength a := by
  have hpt := subParam_mapsTo hab ht
  have hpa : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hp := Icc_subset_Icc ha hb hpt
  have himage : subParam a b '' Icc (0 : ℝ) 1 = Icc a b := by
    simpa [subParam] using
      (show Continuous (subParam a b) by fun_prop [subParam]).continuousOn.image_Icc_of_monotoneOn
        zero_le_one ((subParam_mono hab).monotoneOn _)
  rw [(γ.subcurve a b ha hab hb).cumulativeLength_eq ht]
  change variationOnFromTo (γ.toFun ∘ subParam a b) (Icc 0 1) 0 t = _
  rw [variationOnFromTo.comp_eq_of_monotoneOn γ.toFun (subParam a b)
    ((subParam_mono hab).monotoneOn _) (by simp) ht, himage]
  have hstart : subParam a b 0 = a := by simp [subParam]
  rw [hstart, γ.cumulativeLength_eq hp, γ.cumulativeLength_eq hpa,
    variationOnFromTo.sub_right γ.boundedVariationOn.locallyBoundedVariationOn
      (by simp) hp hpa]
  rw [variationOnFromTo.eq_of_le _ _ hpt.1, variationOnFromTo.eq_of_le _ _ hpt.1]
  congr 1
  congr 1
  rw [inter_eq_right.mpr (Icc_subset_Icc le_rfl hpt.2),
    inter_eq_right.mpr (Icc_subset_Icc ha hp.2)]

lemma length_subcurve (γ : RectifiableCurve E) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (γ.subcurve a b ha hab hb).length = γ.arcLengthMeasure (Icc a b) := by
  have h := γ.cumulativeLength_subcurve ha hab hb (t := 1) (by simp)
  rw [cumulativeLength_of_one_le _ le_rfl] at h
  have heq : subParam a b 1 = b := by dsimp [subParam]; ring
  rw [heq] at h
  rw [γ.arcLengthMeasure_Icc, ← h, ENNReal.ofReal_toReal (length_ne_top _)]

lemma map_arcLengthMeasure_subcurve (γ : RectifiableCurve E) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (γ.subcurve a b ha hab hb).arcLengthMeasure.map (subParam a b) =
      γ.arcLengthMeasure.restrict (Icc a b) := by
  apply map_eq_of_cumulative_Icc _ _ (ae_mem_Icc _) (ae_restrict_mem measurableSet_Icc)
    (by fun_prop [subParam]) ((subParam_mono hab).monotoneOn _)
    (by simp [subParam]) (by dsimp [subParam]; ring)
  · rw [arcLengthMeasure_univ, Measure.restrict_apply_univ, γ.length_subcurve ha hab hb]
  · intro t ht
    rw [arcLengthMeasure_Iic, γ.cumulativeLength_subcurve ha hab hb ht,
      Measure.restrict_apply measurableSet_Iic]
    have hpt := subParam_mapsTo hab ht
    have heq : Iic (subParam a b t) ∩ Icc a b = Icc a (subParam a b t) := by
      ext x
      constructor
      · intro h; exact ⟨h.2.1, h.1⟩
      · intro h; exact ⟨h.2, h.1, h.2.trans hpt.2⟩
    rw [heq, γ.arcLengthMeasure_Icc]

/-- The cost of a subcurve is the original arc-length integral restricted to that subinterval. -/
theorem cost_subcurve [MeasurableSpace E] [BorelSpace E] (γ : RectifiableCurve E)
    {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (γ.subcurve a b ha hab hb).cost ρ = ∫⁻ t in Icc a b, ρ (γ.toFun t) ∂γ.arcLengthMeasure := by
  have heq : (∫⁻ t in Icc a b, ρ (γ.toFun t) ∂γ.arcLengthMeasure) =
      ∫⁻ t in Icc a b, ρ (γ.clamped t) ∂γ.arcLengthMeasure := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    change ρ (γ.toFun t) = ρ (γ.clamped t)
    rw [γ.clamped_eq (Icc_subset_Icc ha hb ht)]
  rw [heq, ← γ.map_arcLengthMeasure_subcurve ha hab hb]
  change _ = ∫⁻ t, (ρ ∘ γ.clamped) t ∂Measure.map (subParam a b) _
  rw [lintegral_map (hρ.comp γ.continuous_clamped.measurable)
    (show Measurable (subParam a b) by fun_prop [subParam])]
  apply lintegral_congr_ae
  filter_upwards [(γ.subcurve a b ha hab hb).ae_mem_Icc] with t ht
  change ρ (γ.toFun (subParam a b t)) = ρ (γ.clamped (subParam a b t))
  rw [γ.clamped_eq (Icc_subset_Icc ha hb (subParam_mapsTo hab ht))]

lemma subcurve_start (γ : RectifiableCurve E) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (γ.subcurve a b ha hab hb).toFun 0 = γ.toFun a := by
  simp [subcurve, subParam]

lemma subcurve_end (γ : RectifiableCurve E) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (γ.subcurve a b ha hab hb).toFun 1 = γ.toFun b := by
  simp [subcurve, subParam]

end IsotropicVariance.RectifiableCurve
