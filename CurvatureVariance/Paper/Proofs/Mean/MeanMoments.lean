/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Os.Moments
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CurvatureVariance.Paper.Proofs.Mean.MeanExcess
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.FieldSimp

/-!
# Polynomial norms of the exponential remainders

The explicit `O₁` moment bound supplies the uniform high moments used in the centered-profile
interpolation of the bound on the fluctuations in the proof of Lemma `lem:smallmean` (the second
paragraph of the proof of [AB26, Lemma 7.1]).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace CurvatureVariance.Paper.Mean

/-- Explicit finite-moment norms of the positive part of an `O₁` variable. -/
theorem eLpNorm_pos_le_of_isOs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {θ p : ℝ} (hX : CurvatureVariance.IsOs P 1 θ X) (hθ : 0 < θ) (hp : 0 < p) :
    eLpNorm (fun ω => max (X ω) 0) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal ((2 * (1 + ((Nat.ceil p).factorial : ℝ))) ^ (1 / p) * θ) := by
  have hm := hX.lintegral_pos_rpow_le zero_lt_one hθ hp.le
  simp only [div_one] at hm
  have heq : eLpNorm (fun ω => max (X ω) 0) (ENNReal.ofReal p) P =
      (∫⁻ ω, ENNReal.ofReal (max (X ω) 0 ^ p) ∂P) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
      ENNReal.ofReal_ne_top (hX.1.max aemeasurable_const).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hp.le]
    congr 1
    apply lintegral_congr
    intro ω
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (le_max_right _ _),
      ← ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) hp.le]
  rw [heq]
  apply (ENNReal.rpow_le_rpow hm (by positivity : 0 ≤ 1 / p)).trans_eq
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hθ.le _),
    ← Real.rpow_mul hθ.le, mul_one_div_cancel hp.ne', Real.rpow_one]

/-- A common exponential majorant about deterministic centers gives a common
finite-moment majorant after centering at expectations. -/
theorem exists_centered_majorant_of_isOs {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type*}
    (F : ι → Ω → ℝ) (center : ι → ℝ) (I : Set ι)
    (hFi : ∀ i, Integrable (F i) P) {X : Ω → ℝ} {θ p : ℝ}
    (hX : CurvatureVariance.IsOs P 1 θ X) (hθ : 0 < θ) (hp : 1 ≤ p)
    (hbound : ∀ᵐ ω ∂P, ∀ i ∈ I, |F i ω - center i| ≤ X ω) :
    ∃ Y : Ω → ℝ, AEMeasurable Y P ∧ (∀ ω, 0 ≤ Y ω) ∧
      (∀ᵐ ω ∂P, ∀ i ∈ I, |F i ω - ∫ ω', F i ω' ∂P| ≤ Y ω) ∧
      eLpNorm Y (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (2 * ((2 * (1 + ((Nat.ceil p).factorial : ℝ))) ^ (1 / p) * θ)) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let D : ℝ := (2 * (1 + ((Nat.ceil p).factorial : ℝ))) ^ (1 / p) * θ
  have hD : 0 < D := mul_pos (Real.rpow_pos_of_pos (by positivity) _) hθ
  have hXp : eLpNorm (fun ω => max (X ω) 0) (ENNReal.ofReal p) P ≤ ENNReal.ofReal D :=
    eLpNorm_pos_le_of_isOs hX hθ hp0
  have hE (i : ι) (hi : i ∈ I) : |(∫ ω, F i ω ∂P) - center i| ≤ D := by
    have hh := abs_integral_sub_le_of_ae_modulus
      (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal p by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
      (integrable_const (center i)) (hFi i)
      (hbound.mono fun ω hω => (hω i hi).trans (le_max_left _ _)) hD.le hXp
    simpa only [integral_const, probReal_univ, one_smul] using hh
  refine ⟨fun ω => max (X ω) 0 + D, (hX.1.max aemeasurable_const).add_const _,
    fun ω => add_nonneg (le_max_right _ _) hD.le, ?_, ?_⟩
  · filter_upwards [hbound] with ω hω
    intro i hi
    have hh : |F i ω - ∫ ω', F i ω' ∂P| ≤
        |F i ω - center i| + |(∫ ω', F i ω' ∂P) - center i| := by
      simpa only [abs_sub_comm (center i)] using abs_sub_le (F i ω) (center i) (∫ ω', F i ω' ∂P)
    exact hh.trans (add_le_add ((hω i hi).trans (le_max_left _ _)) (hE i hi))
  · have hc : eLpNorm (fun _ : Ω => D) (ENNReal.ofReal p) P = ENNReal.ofReal D := by
      rw [eLpNorm_const _ (ne_of_gt (ENNReal.ofReal_pos.mpr hp0))
        (IsProbabilityMeasure.ne_zero P)]
      simp only [measure_univ, ENNReal.one_rpow, mul_one,
        Real.enorm_eq_ofReal_abs, abs_of_nonneg hD.le]
    apply (eLpNorm_add_le (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal p by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)).trans
    apply (add_le_add hXp hc.le).trans_eq
    rw [← ENNReal.ofReal_add hD.le hD.le]
    congr 1
    dsimp only [D]
    ring

end CurvatureVariance.Paper.Mean
