/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.MomentTools
public import IsotropicVariance.Paper.Proofs.Responses.GaussianSegment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Moments of the cell sum

Hölder and Minkowski in the proof of Lemma `lem:blocks`. No independence of the
responses within a slab is needed: each cell uses a fourth-order moment and its own tube event.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Hölder bounds a cell's squared response by its fourth moment and the tube probability. -/
lemma eLpNorm_indicator_sq_le {p D : ℝ} (hp : 0 < p) (hD : 0 ≤ D)
    {U : Ω → ℝ≥0∞} (hU : AEMeasurable U P) {A : Set Ω} (hA : MeasurableSet A)
    (h : eLpNorm U (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal D) :
    eLpNorm (A.indicator fun ω => U ω ^ 2) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (D ^ 2) * P A ^ (1 / (2 * p)) := by
  have hs : (fun ω => U ω ^ 2) = fun ω => ‖U ω‖ₑ ^ (2 : ℝ) := by ext ω; simp
  have hn : eLpNorm (fun ω => U ω ^ 2) (ENNReal.ofReal (2 * p)) P ≤
      ENNReal.ofReal (D ^ 2) := by
    rw [hs, eLpNorm_enorm_rpow _ hU.aestronglyMeasurable (by norm_num : (0 : ℝ) < 2),
      ← ENNReal.ofReal_mul (by positivity), show 2 * p * 2 = 4 * p by ring,
      ENNReal.rpow_two, ENNReal.ofReal_pow hD]
    exact pow_le_pow_left₀ bot_le h 2
  exact (eLpNorm_indicator_le_double_ennreal hp (hU.pow_const 2) hA).trans
    (mul_le_mul' hn le_rfl)

/-- A Gaussian tube probability produces a Gaussian `L^p` bound for the cell contribution. -/
lemma eLpNorm_indicator_sq_le_gaussian {p D B c d : ℝ} (hp : 0 < p)
    (hD : 0 ≤ D) (hB : 0 ≤ B) {U : Ω → ℝ≥0∞} (hU : AEMeasurable U P)
    {A : Set Ω} (hA : MeasurableSet A)
    (h : eLpNorm U (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal D)
    (hprob : P A ≤ ENNReal.ofReal (B * Real.exp (-c * d ^ 2))) :
    eLpNorm (A.indicator fun ω => U ω ^ 2) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (D ^ 2 * B ^ (1 / (2 * p)) *
        Real.exp (-(c / (2 * p)) * d ^ 2)) := by
  refine (eLpNorm_indicator_sq_le hp hD hU hA h).trans ?_
  refine (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hprob (by positivity))).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    Real.mul_rpow hB (Real.exp_pos _).le, ← Real.exp_mul,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show -c * d ^ 2 * (1 / (2 * p)) = -(c / (2 * p)) * d ^ 2 by ring]
  ring

/-- A sum of cells with Gaussian `L^p` bounds costs at most one plus the segment length. -/
theorem eLpNorm_cell_sum_le {m : ℕ} {p D c : ℝ} (hp : 1 ≤ p) (hD : 0 ≤ D) (hc : 0 < c)
    (j k : Fin m → ℤ) {f : (Fin m → ℤ) → Ω → ℝ≥0∞}
    (hf : ∀ z, AEMeasurable (f z) P)
    (hcell : ∀ z, eLpNorm (f z) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (D * Real.exp (-c * infDist (transverseIntegerPoint z)
        (segment ℝ (transverseIntegerPoint j) (transverseIntegerPoint k)) ^ 2))) :
    eLpNorm (fun ω => ∑' z, f z ω) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (D * gaussianSegmentConst m c * (1 + zNorm (j - k))) := by
  refine (eLpNorm_tsum_le (by simpa using ENNReal.ofReal_le_ofReal hp) hf).trans ?_
  calc
    _ ≤ ∑' z : Fin m → ℤ, ENNReal.ofReal D * ENNReal.ofReal (Real.exp (-c *
        infDist (transverseIntegerPoint z)
          (segment ℝ (transverseIntegerPoint j) (transverseIntegerPoint k)) ^ 2)) := by
      apply ENNReal.tsum_le_tsum
      intro z
      rw [← ENNReal.ofReal_mul hD]
      exact hcell z
    _ = ENNReal.ofReal D * ∑' z : Fin m → ℤ, ENNReal.ofReal (Real.exp (-c *
        infDist (transverseIntegerPoint z)
          (segment ℝ (transverseIntegerPoint j) (transverseIntegerPoint k)) ^ 2)) :=
      ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal D *
        ENNReal.ofReal (gaussianSegmentConst m c * (1 + zNorm (j - k))) :=
      mul_le_mul' le_rfl (tsum_exp_neg_infDist_segment_sq_le hc j k)
    _ = _ := by rw [← ENNReal.ofReal_mul hD]; congr 1; ring

end IsotropicVariance.Paper.Proofs.Responses
