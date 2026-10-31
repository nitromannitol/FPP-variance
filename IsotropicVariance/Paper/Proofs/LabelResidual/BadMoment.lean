/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Small changes off an exceptional event

The Holder estimate in the proof of Lemma `lem:residual`: a `4p` moment of the
reward costs only the `3/4` power of the exceptional-event probability in its `p`-th moment.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.LabelResidual

/-- Holder bounds the `p`-th moment on an event by its probability to the power `3/4`. -/
theorem lintegral_indicator_pow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ≥0∞} (hY : AEMeasurable Y P) {B : Set Ω} (hB : MeasurableSet B)
    (p : ℕ) {M : ℝ≥0∞} (h4p : ∫⁻ ω, Y ω ^ (4 * p) ∂P ≤ M ^ (4 * p)) :
    ∫⁻ ω, B.indicator (fun ω => Y ω ^ p) ω ∂P ≤ M ^ p * P B ^ (3 / 4 : ℝ) := by
  have hpq : (4 : ℝ).HolderConjugate (4 / 3) :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).2 (by norm_num)
  have heq : (fun ω => B.indicator (fun ω => Y ω ^ p) ω) =
      (fun ω => Y ω ^ p) * B.indicator 1 := by
    funext ω
    by_cases hω : ω ∈ B <;> simp [hω]
  rw [heq]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq (hY.pow_const p)
    (measurable_one.indicator hB).aemeasurable).trans ?_
  have hpow : ∀ ω, (Y ω ^ p) ^ (4 : ℝ) = Y ω ^ (4 * p) := fun ω => by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, ← pow_mul, mul_comm]
  have hind : ∀ ω, (B.indicator (1 : Ω → ℝ≥0∞) ω) ^ (4 / 3 : ℝ) = B.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ B
    · simp [hω]
    · simp [hω, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
  simp_rw [hpow,hind]
  rw [lintegral_indicator_one hB, show (1 : ℝ) / (4 / 3) = 3 / 4 by norm_num]
  apply mul_le_mul' _ le_rfl
  calc
    _ ≤ (M ^ (4 * p)) ^ (1 / 4 : ℝ) := ENNReal.rpow_le_rpow h4p (by norm_num)
    _ = M ^ p := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast]
      congr 1
      push_cast
      ring

/-- A small comparison outside a bad event and a `4p` moment on it give a small `p` moment. -/
theorem lintegral_pow_le_of_small_off_event {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y U : Ω → ℝ≥0∞} (hY : AEMeasurable Y P) {B : Set Ω} (hB : MeasurableSet B)
    (p : ℕ) {a M : ℝ≥0∞} (hsmall : ∫⁻ ω, U ω ^ p ∂P ≤ a)
    (h4p : ∫⁻ ω, Y ω ^ (4 * p) ∂P ≤ M ^ (4 * p))
    (hgood : ∀ᵐ ω ∂P, ω ∉ B → Y ω ≤ U ω) :
    ∫⁻ ω, Y ω ^ p ∂P ≤ a + M ^ p * P B ^ (3 / 4 : ℝ) := by
  have hpt : ∀ᵐ ω ∂P, Y ω ^ p ≤ U ω ^ p + B.indicator (fun ω => Y ω ^ p) ω := by
    filter_upwards [hgood] with ω hω
    by_cases hωB : ω ∈ B
    · rw [indicator_of_mem hωB]
      exact le_add_self
    · rw [indicator_of_notMem hωB, add_zero]
      exact pow_le_pow_left' (hω hωB) p
  calc
    _ ≤ ∫⁻ ω, U ω ^ p + B.indicator (fun ω => Y ω ^ p) ω ∂P := lintegral_mono_ae hpt
    _ = (∫⁻ ω, U ω ^ p ∂P) + ∫⁻ ω, B.indicator (fun ω => Y ω ^ p) ω ∂P :=
      lintegral_add_right' _ ((hY.pow_const p).indicator hB)
    _ ≤ _ := add_le_add hsmall (lintegral_indicator_pow_le hY hB p h4p)

end IsotropicVariance.Paper.Proofs.LabelResidual
