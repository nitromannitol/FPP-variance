/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
import IsotropicVariance.Statements.Cited.IsOsMeasureGeLe
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Gaussian tails for shifted localization radii

The probability of a cell belonging to a random tube in the proof of Lemma
`lem:blocks`. Adding a fixed radius changes only the Gaussian prefactor.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- An `O₂(θ)` radius has a Gaussian tube-membership tail after any nonnegative fixed shift. -/
theorem measure_le_shift_radius_le {θ a d : ℝ} (hθ : 0 < θ) (_ha : 0 ≤ a) (hd : 0 ≤ d)
    {R : Ω → ℝ} (hR : Cited.IsOs P 2 θ R) :
    P {ω | d ≤ a + R ω} ≤
      ENNReal.ofReal (2 * Real.exp ((a / θ) ^ 2) * Real.exp (-(1 / (4 * θ ^ 2)) * d ^ 2)) := by
  have hθsq : 0 < θ ^ 2 := sq_pos_of_pos hθ
  by_cases hda : d ≤ 2 * a
  · apply prob_le_one.trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have he : 0 ≤ (a / θ) ^ 2 - (1 / (4 * θ ^ 2)) * d ^ 2 := by
      have hd2 : d ^ 2 ≤ (2 * a) ^ 2 := pow_le_pow_left₀ hd hda 2
      field_simp
      nlinarith only [hd2]
    rw [mul_assoc, ← Real.exp_add]
    have hexp : 1 ≤ Real.exp ((a / θ) ^ 2 + -(1 / (4 * θ ^ 2)) * d ^ 2) :=
      Real.one_le_exp (by linarith only [he])
    linarith only [hexp]
  · have hgt : 2 * a < d := lt_of_not_ge hda
    have hsub : {ω | d ≤ a + R ω} ⊆ {ω | θ * (d / (2 * θ)) ≤ R ω} := by
      intro ω hω
      change d ≤ a + R ω at hω
      have heq : θ * (d / (2 * θ)) = d / 2 := by field_simp
      change θ * (d / (2 * θ)) ≤ R ω
      rw [heq]
      linarith only [hω, hgt]
    apply (measure_mono hsub).trans
    have htail := Cited.IsOs.measure_ge_le (by norm_num : (0 : ℝ) < 2) hθ hR _
      (div_nonneg hd (by positivity : 0 ≤ 2 * θ))
    apply htail.trans
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_two]
    have heq : -(d / (2 * θ)) ^ 2 = -(1 / (4 * θ ^ 2)) * d ^ 2 := by field_simp; ring
    rw [heq]
    have he : 1 ≤ Real.exp ((a / θ) ^ 2) := Real.one_le_exp (sq_nonneg _)
    nlinarith only [mul_le_mul_of_nonneg_right he
      (Real.exp_pos (-(1 / (4 * θ ^ 2)) * d ^ 2)).le]

end IsotropicVariance.Paper.Proofs.Responses
