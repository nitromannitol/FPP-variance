/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Os.Moments
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fourth moments and exceptional events

The indicator of an exceptional event is idempotent. Thus an arbitrarily high moment supplied
by the `O₂` bound gives a fourth norm with arbitrarily high power decay in its scale. Combining
this with Hölder avoids any measurable-set assumption on the good events of `SlabsStatement`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Good-event comparison and a fourth moment give a second-norm estimate. The event itself
need not be measurable: its indicator need only be almost everywhere strongly measurable. -/
theorem eLpNorm_two_le_good_add_four_mul {X : Ω → ℝ} (hX : AEStronglyMeasurable X P)
    [IsProbabilityMeasure P] {G : Set Ω}
    (hG : AEStronglyMeasurable (Gᶜ.indicator fun _ => (1 : ℝ)) P)
    {D : ℝ} (hD : 0 ≤ D) (hgood : ∀ ω ∈ G, ‖X ω‖ ≤ D) :
    eLpNorm X 2 P ≤ ENNReal.ofReal D +
      eLpNorm X 4 P * eLpNorm (Gᶜ.indicator fun _ => (1 : ℝ)) 4 P := by
  let B := Gᶜ.indicator fun _ => (1 : ℝ)
  have hnorm : ∀ ω, ‖X ω‖ ≤ ‖D + ‖X ω‖ * B ω‖ := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [B, Set.indicator_of_notMem (show ω ∉ Gᶜ from not_not.mpr hω),
        mul_zero, add_zero, Real.norm_eq_abs, abs_of_nonneg hD] using hgood ω hω
    · simp only [B, Set.indicator_of_mem (show ω ∈ Gᶜ from hω), mul_one]
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg hD (abs_nonneg _))]
      exact le_add_of_nonneg_left hD
  have hholder : eLpNorm (fun ω => ‖X ω‖ * B ω) 2 P ≤
      eLpNorm X 4 P * eLpNorm B 4 P := by
    have : ENNReal.HolderTriple 4 4 2 := by
      constructor
      change ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ + ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0) : ℝ≥0∞)⁻¹
      rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
        ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
      norm_num
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (p := (4 : ℝ≥0∞)) (q := (4 : ℝ≥0∞)) (r := (2 : ℝ≥0∞))
      (fun a b : ℝ => a * b) 1 continuous_mul hX.norm hG
      (ae_of_all _ fun _ => by norm_num [Real.norm_eq_abs, abs_mul])
    simpa only [ENNReal.coe_one, one_mul, eLpNorm_norm _ hX] using h
  calc
    _ ≤ eLpNorm (fun ω => D + ‖X ω‖ * B ω) 2 P :=
      eLpNorm_mono_ae hX (ae_of_all _ hnorm)
    _ ≤ eLpNorm (fun _ : Ω => D) 2 P + eLpNorm (fun ω => ‖X ω‖ * B ω) 2 P :=
      eLpNorm_add_le (by norm_num)
    _ ≤ _ := by
      rw [eLpNorm_const D (by norm_num) (NeZero.ne P), measure_univ, ENNReal.one_rpow,
        mul_one, Real.enorm_of_nonneg hD]
      exact add_le_add le_rfl hholder

end CurvatureVariance.Paper.Responses
