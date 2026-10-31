/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.TimeConstant.Mean

/-! # The positive continuum time constant

The limit is over all real parameters tending to infinity. The lower tangent
bound holds at every nonnegative real parameter, as used in Section `ssec:overview`.
-/

@[expose] public section
open MeasureTheory Set Filter Topology
namespace IsotropicVariance.Infra.TimeConstant
open Paper

/-- The mean has a positive finite asymptotic slope and lies above its tangent
at every nonnegative real parameter. -/
theorem exists_timeConstant {m : ℕ} (X : Setting m) :
    ∃ μ : ℝ, 0 < μ ∧ Tendsto (fun t : ℝ => X.mean t / t) atTop (𝓝 μ) ∧
      ∀ t, 0 ≤ t → μ * t ≤ X.mean t := by
  obtain ⟨a, b, ha, hBounds⟩ := mean_bounds X
  obtain ⟨L, _, hLip⟩ := mean_lipschitz X
  let B := max b L
  have hBounds' (t : ℝ) (ht : 0 ≤ t) : a * t ≤ X.mean t ∧ X.mean t ≤ B * t :=
    ⟨(hBounds t ht).1, (hBounds t ht).2.trans (mul_le_mul_of_nonneg_right (le_max_left b L) ht)⟩
  have hLip' (s t : ℝ) (_hs : 0 ≤ s) (_ht : 0 ≤ t) : |X.mean s - X.mean t| ≤ B * |s - t| :=
    (hLip s t).trans (mul_le_mul_of_nonneg_right (le_max_right b L) (abs_nonneg _))
  obtain ⟨μ, hμa, _, hLim, hTan⟩ := exists_slope_of_subadditive X.mean ha hBounds'
    (fun s t _ _ => mean_subadditive X s t) hLip'
  exact ⟨μ, ha.trans_le hμa, hLim, hTan⟩

/-- The continuum time constant, characterized by `tendsto_mean_div_timeConstant`. -/
noncomputable def timeConstant {m : ℕ} (X : Setting m) : ℝ :=
  Classical.choose (exists_timeConstant X)

/-- Uniform ellipticity makes the time constant strictly positive. -/
theorem timeConstant_pos {m : ℕ} (X : Setting m) : 0 < timeConstant X :=
  (Classical.choose_spec (exists_timeConstant X)).1

/-- The defining real-parameter limit of the time constant. -/
theorem tendsto_mean_div_timeConstant {m : ℕ} (X : Setting m) :
    Tendsto (fun t : ℝ => X.mean t / t) atTop (𝓝 (timeConstant X)) :=
  (Classical.choose_spec (exists_timeConstant X)).2.1

/-- The mean lies above the time-constant tangent at every nonnegative scale. -/
theorem timeConstant_mul_le_mean {m : ℕ} (X : Setting m) {t : ℝ} (ht : 0 ≤ t) :
    timeConstant X * t ≤ X.mean t :=
  (Classical.choose_spec (exists_timeConstant X)).2.2 t ht

/-- The slope supplied by normalization is unique. -/
theorem timeConstant_eq_of_tendsto {m : ℕ} (X : Setting m) {μ : ℝ}
    (h : Tendsto (fun t : ℝ => X.mean t / t) atTop (𝓝 μ)) : timeConstant X = μ :=
  tendsto_nhds_unique (tendsto_mean_div_timeConstant X) h

/-- A setting already normalized in the paper's sense has time constant one. -/
theorem timeConstant_eq_one_of_isNormalized {m : ℕ} (X : Setting m) (h : X.IsNormalized) :
    timeConstant X = 1 := timeConstant_eq_of_tendsto X h

/-- The normalized lower mean bound consumed in the paper. -/
theorem mean_ge_of_isNormalized {m : ℕ} (X : Setting m) (h : X.IsNormalized)
    {t : ℝ} (ht : 0 ≤ t) : t ≤ X.mean t := by
  have hh := timeConstant_mul_le_mean X ht
  rwa [timeConstant_eq_one_of_isNormalized X h, one_mul] at hh

end IsotropicVariance.Infra.TimeConstant
