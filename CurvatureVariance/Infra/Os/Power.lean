/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Os.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Concave powers of exponential moments

A probability-space Hölder inequality used to normalize exponential moments.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
namespace CurvatureVariance.Infra.Os

/-- Concave-power Jensen for nonnegative extended-real functions. -/
theorem lintegral_rpow_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫⁻ ω, f ω ^ a ∂P) ≤ (∫⁻ ω, f ω ∂P) ^ a := by
  rcases eq_or_lt_of_le ha1 with rfl | ha1
  · simp only [ENNReal.rpow_one, le_refl]
  have hpq : (a⁻¹).HolderConjugate ((1 - a)⁻¹) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact (one_lt_inv₀ ha).mpr ha1
    · simp only [inv_inv]; ring
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq (hf.pow_const a)
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simpa only [Pi.mul_apply, mul_one, ← ENNReal.rpow_mul, mul_inv_cancel₀ ha.ne',
    ENNReal.rpow_one, ENNReal.one_rpow, lintegral_const, measure_univ, one_mul, one_div, inv_inv] using hh

/-- Normalize an exponential moment bounded by `2^r`, enlarging the scale by
`r^(1/s)`. This is the concave-power step in AKM A.4. -/
theorem isOs_of_exp_moment_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s θ r : ℝ} {X : Ω → ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (hr : 1 ≤ r) (hX : AEMeasurable X P)
    (hBound : (∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s)) ∂P) ≤ (2 : ℝ≥0∞) ^ r) :
    IsOs P s (r ^ (1 / s) * θ) X := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hScale : (r ^ (1 / s)) ^ s = r := by
    rw [← Real.rpow_mul hrpos.le, one_div_mul_cancel hs.ne', Real.rpow_one]
  refine ⟨hX, ?_⟩
  calc
    _ = ∫⁻ ω, (ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s))) ^ (1 / r) ∂P := by
      apply lintegral_congr
      intro ω
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
      congr 2
      rw [mul_comm (r ^ (1 / s)), ← div_div, Real.div_rpow (by positivity) (Real.rpow_nonneg hrpos.le _), hScale]
      ring
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s)) ∂P) ^ (1 / r) :=
      lintegral_rpow_le (aemeasurable_exp_pos_rpow hX s θ) (one_div_pos.mpr hrpos) ((div_le_one hrpos).mpr hr)
    _ ≤ ((2 : ℝ≥0∞) ^ r) ^ (1 / r) := ENNReal.rpow_le_rpow hBound (by positivity)
    _ = 2 := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hrpos.ne', ENNReal.rpow_one]

end CurvatureVariance.Infra.Os
