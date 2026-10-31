/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Congr
public import Mathlib.Analysis.ConstantSpeed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # Natural parametrization of a continuous rectifiable curve -/

@[expose] public section
open Set MeasureTheory Function
open scoped NNReal ENNReal Topology

namespace IsotropicVariance.RectifiableCurve
open IsotropicVariance.Infra.Curves
variable {E : Type*} [MetricSpace E]

/-- Unit-speed representative on the interval of arc lengths. -/
noncomputable def natural (γ : RectifiableCurve E) : ℝ → E :=
  naturalParameterization γ.toFun (Icc 0 1) 0

lemma variation_image (γ : RectifiableCurve E) :
    variationOnFromTo γ.toFun (Icc 0 1) 0 '' Icc 0 1 = Icc 0 γ.length.toReal := by
  have hc : ContinuousOn (variationOnFromTo γ.toFun (Icc 0 1) 0) (Icc 0 1) := by
    intro t ht
    exact (γ.boundedVariationOn.continuousWithinAt_variationOnFromTo_iff
      (by simp) ht).mpr (γ.continuousOn t ht)
  have hm := variationOnFromTo.monotoneOn γ.boundedVariationOn.locallyBoundedVariationOn
    (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
  rw [hc.image_Icc_of_monotoneOn zero_le_one hm]
  simp [variationOnFromTo.self, variationOnFromTo.eq_of_le _ _ zero_le_one, length]

lemma natural_cumulativeLength (γ : RectifiableCurve E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    γ.natural (γ.cumulativeLength t) = γ.toFun t := by
  rw [γ.cumulativeLength_eq ht]
  exact edist_eq_zero.mp (edist_naturalParameterization_eq_zero
    γ.boundedVariationOn.locallyBoundedVariationOn (by simp) ht)

lemma unitSpeed_natural (γ : RectifiableCurve E) :
    HasUnitSpeedOn γ.natural (Icc 0 γ.length.toReal) := by
  rw [← γ.variation_image]
  exact has_unit_speed_naturalParameterization γ.toFun
    γ.boundedVariationOn.locallyBoundedVariationOn (by simp)

lemma lipschitzOnWith_natural (γ : RectifiableCurve E) :
    LipschitzOnWith 1 γ.natural (Icc 0 γ.length.toReal) := by
  have hbound : ∀ s ∈ Icc 0 γ.length.toReal, ∀ t ∈ Icc 0 γ.length.toReal,
      s ≤ t → edist (γ.natural s) (γ.natural t) ≤ edist s t := by
    intro s hs t ht hst
    calc
      _ ≤ eVariationOn γ.natural (Icc 0 γ.length.toReal ∩ Icc s t) :=
        eVariationOn.edist_le _ ⟨hs, le_rfl, hst⟩ ⟨ht, hst, le_rfl⟩
      _ = ENNReal.ofReal (t - s) := by simpa using γ.unitSpeed_natural hs ht
      _ = edist s t := by rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
  intro s hs t ht
  simp only [ENNReal.coe_one, one_mul]
  rcases le_total s t with hst | hts
  · exact hbound s hs t ht hst
  · rw [edist_comm (γ.natural s), edist_comm s]
    exact hbound t ht s hs hts

lemma lipschitzOnWith_natural_scaled (γ : RectifiableCurve E) :
    LipschitzOnWith (Real.toNNReal γ.length.toReal)
      (fun t => γ.natural (t * γ.length.toReal)) (Icc 0 1) := by
  have hlin := LipCurve.lipschitzWith_affine 0 γ.length.toReal ENNReal.toReal_nonneg
  have hmap : MapsTo (fun t : ℝ => t * γ.length.toReal) (Icc 0 1)
      (Icc 0 γ.length.toReal) := by
    intro t ht
    constructor
    · exact mul_nonneg ht.1 ENNReal.toReal_nonneg
    · simpa using mul_le_mul_of_nonneg_right ht.2 ENNReal.toReal_nonneg
  simpa only [one_mul, Function.comp_def] using γ.lipschitzOnWith_natural.comp
    (show LipschitzOnWith (Real.toNNReal γ.length.toReal)
      (fun t : ℝ => t * γ.length.toReal) (Icc 0 1) by simpa using hlin.lipschitzOnWith) hmap

/-- Constant-speed representative on the unit parameter interval. -/
noncomputable def constantSpeed (γ : RectifiableCurve E) : RectifiableCurve E :=
  ofLipschitzOn (fun t => γ.natural (t * γ.length.toReal)) γ.lipschitzOnWith_natural_scaled

lemma lipschitzOnWith_constantSpeed (γ : RectifiableCurve E) :
    LipschitzOnWith (Real.toNNReal γ.length.toReal) γ.constantSpeed.toFun (Icc 0 1) :=
  γ.lipschitzOnWith_natural_scaled

lemma constantSpeed_start (γ : RectifiableCurve E) :
    γ.constantSpeed.toFun 0 = γ.toFun 0 := by
  have h := γ.natural_cumulativeLength (t := 0) (by simp)
  simpa [constantSpeed, ofLipschitzOn, γ.cumulativeLength_of_nonpos le_rfl] using h

lemma constantSpeed_end (γ : RectifiableCurve E) :
    γ.constantSpeed.toFun 1 = γ.toFun 1 := by
  have h := γ.natural_cumulativeLength (t := 1) (by simp)
  simpa [constantSpeed, ofLipschitzOn, γ.cumulativeLength_of_one_le le_rfl] using h

end IsotropicVariance.RectifiableCurve
