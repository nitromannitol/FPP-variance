/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.Basic
public import Mathlib.Analysis.Real.Sqrt
import IsotropicVariance.Statements.Cited.IsOsOfMeasureGeLe
import IsotropicVariance.Infra.Os.SumRule
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Gaussian tails and the absolute-centered stochastic-order estimate

The strict tails supplied by BLM suffice: halve a positive threshold before
applying the estimate, so atoms at a boundary create no problem.
-/

@[expose] public section
open MeasureTheory Set Real Filter
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra

/-- A strict one-sided Gaussian tail controls the positive part in `O_2`. -/
theorem isOs_positive_of_gaussian_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P) {A : ℝ} (hA : 0 < A)
    (hTail : ∀ r : ℝ, 0 < r → P {ω | r < X ω} ≤ ENNReal.ofReal (exp (-(r ^ 2 / (4 * A))))) :
    Cited.IsOs P 2 ((2 : ℝ) ^ (1 / 2 : ℝ) * (4 * sqrt A)) (fun ω => max (X ω) 0) := by
  apply Cited.isOs_of_measure_ge_le (by norm_num : (0 : ℝ) < 2) (by positivity)
    (hX.max aemeasurable_const)
  intro t ht
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [mul_zero, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0), neg_zero, exp_zero,
      ENNReal.ofReal_one] using (show P {ω | (0 : ℝ) ≤ max (X ω) 0} ≤ 1 from (measure_mono (subset_univ _)).trans_eq measure_univ)
  have hSub : {ω | (4 * sqrt A) * t ≤ max (X ω) 0} ⊆ {ω | (4 * sqrt A) * t / 2 < X ω} := by
    intro ω hω
    change (4 * sqrt A) * t ≤ max (X ω) 0 at hω
    change (4 * sqrt A) * t / 2 < X ω
    have hpos : 0 < (4 * sqrt A) * t := by positivity
    rcases le_max_iff.mp hω with h | h
    · linarith only [h, hpos]
    · exact False.elim ((not_le_of_gt hpos) h)
  have hEq : ((4 * sqrt A) * t / 2) ^ 2 / (4 * A) = t ^ 2 := by
    calc
      _ = ((sqrt A) ^ 2 / A) * t ^ 2 := by field_simp; ring
      _ = _ := by rw [sq_sqrt hA.le, div_self hA.ne', one_mul]
  exact (measure_mono hSub).trans (by
    simpa only [hEq, Real.rpow_two] using hTail ((4 * sqrt A) * t / 2) (by positivity))

/-- Opposite one-sided Gaussian tails give the absolute-value `O_2` estimate. -/
theorem isOs_abs_of_gaussian_tails {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P) {A : ℝ} (hA : 0 < A)
    (hUp : ∀ r : ℝ, 0 < r → P {ω | r < X ω} ≤ ENNReal.ofReal (exp (-(r ^ 2 / (4 * A)))))
    (hDown : ∀ r : ℝ, 0 < r → P {ω | r < -X ω} ≤ ENNReal.ofReal (exp (-(r ^ 2 / (4 * A))))) :
    Cited.IsOs P 2 (2 * ((2 : ℝ) ^ (1 / 2 : ℝ) * (4 * sqrt A))) (fun ω => |X ω|) := by
  let θ := (2 : ℝ) ^ (1 / 2 : ℝ) * (4 * sqrt A)
  let Z := fun b : Bool => fun ω => if b then max (X ω) 0 else max (-X ω) 0
  have hZ (b : Bool) : Cited.IsOs P 2 θ (Z b) := by
    cases b
    · exact isOs_positive_of_gaussian_tail P hX.neg hA hDown
    · exact isOs_positive_of_gaussian_tail P hX hA hUp
  have hh := Os.isOs_sum_of_one_le (by norm_num : (1 : ℝ) ≤ 2) Finset.univ (fun _ : Bool => θ)
    (fun _ _ => by dsimp only [θ]; positivity) Z (fun b _ => hZ b)
    (fun b _ => Eventually.of_forall fun ω => by cases b <;> exact le_max_right _ _)
  have heq (ω : Ω) : (∑ b : Bool, Z b ω) = |X ω| := by
    rw [Fintype.sum_bool]
    simp only [Z, Bool.false_eq_true, ↓reduceIte]
    rcases le_total (X ω) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h, zero_add]
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h, add_zero]
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat, heq, θ] using hh

end IsotropicVariance.Paper.Proofs.Classical
