/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Proofs.Gain.RRReplacement
public import CurvatureVariance.Paper.Proofs.LabelResidual.SmallCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import CurvatureVariance.Paper.Proofs.Responses.RowCubes
import CurvatureVariance.Paper.Proofs.Responses.RowGeometry
import CurvatureVariance.Paper.Proofs.Responses.WidthBridge
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Paper.Proofs.Responses.SlabArrays
import CurvatureVariance.Paper.Proofs.Responses.RadiusArrays
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The tail of the radius `R_i(j,k)`

In the proof of Lemma `lem:residual`, the radius `R_i(j,k) = C_d(1 + R)` (`slabRadius`; the paper
takes `C R`, in Section `sec:gain`) is large only with small probability, by Markov's inequality
and a moment of the localization radius `R` (Lemma `lem:localization`, `LocalizationStatement`):

* `measure_ofReal_lt_radius_le`: Markov's inequality for a random radius `C_d(1 + G)` with
  `E G^q ≤ C₃^q`: `P(C_d(1 + G) > r) ≤ (2C_d + 1)^q max(1, C₃^q) r^{−q}` for `r > 0`. The bound
  for bounded pairs (`Proofs.Residual.Near`) applies it.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain.LabelResidual

open CurvatureVariance.Paper CurvatureVariance.Paper.Gain CurvatureVariance.Paper.Contracts

variable {m : ℕ}

/-- **Markov's inequality for a random radius** `C_d(1 + G)` (Section `sec:gain`) with
`E G^q ≤ C₃^q` and `C_d ≥ 0`: for `r > 0`,
`P(C_d(1 + G) > r) ≤ (2C_d + 1)^q max(1, C₃^q) r^{−q}`. -/
theorem measure_ofReal_lt_radius_le {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    [IsProbabilityMeasure Pr] {Cd : ℝ} (hCd : 0 ≤ Cd) {G : Ω → ℝ≥0∞} (hG : Measurable G)
    {q : ℕ} {C₃ : ℝ} (hmom : ∫⁻ ω, G ω ^ q ∂Pr ≤ ENNReal.ofReal (C₃ ^ q)) {r : ℝ} (hr : 0 < r) :
    Pr {ω | ENNReal.ofReal r < ENNReal.ofReal Cd * (1 + G ω)} ≤
      ENNReal.ofReal ((2 * Cd + 1) ^ q * max 1 (C₃ ^ q) * r ^ (-(q : ℝ))) := by
  have hpos : 0 < r ^ q := pow_pos hr q
  have hrpow : r ^ (-(q : ℝ)) = (r ^ q)⁻¹ := by
    rw [Real.rpow_neg hr.le, Real.rpow_natCast]
  rw [hrpow]
  have hB1 : (2 * Cd + 1) ^ q ≤ (2 * Cd + 1) ^ q * max 1 (C₃ ^ q) :=
    le_mul_of_one_le_right (by positivity) (le_max_left _ _)
  by_cases hcase : r ≤ 2 * Cd
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
    exact (pow_le_pow_left₀ hr.le (by linarith) q).trans hB1
  · push Not at hcase
    rcases hCd.eq_or_lt with hC0 | hCpos
    · -- `C_d = 0`: the radius is zero
      have hempty : {ω | ENNReal.ofReal r < ENNReal.ofReal Cd * (1 + G ω)} = ∅ := by
        ext ω
        simp [← hC0]
      rw [hempty, measure_empty]
      exact zero_le
    set t : ℝ := r / (2 * Cd) with ht
    have ht0 : 0 < t := by positivity
    have hCt : Cd * (1 + t) ≤ r := by
      have e : Cd * (1 + t) = Cd + r / 2 := by
        rw [ht]; field_simp
      rw [e]; linarith
    have hsub : {ω | ENNReal.ofReal r < ENNReal.ofReal Cd * (1 + G ω)} ⊆
        {ω | ENNReal.ofReal t ^ q ≤ G ω ^ q} := by
      intro ω hω
      by_contra hlt
      have hlt' : G ω < ENNReal.ofReal t := by
        by_contra h; exact hlt (pow_le_pow_left₀ bot_le (not_lt.1 h) q)
      have h2 : ENNReal.ofReal Cd * (1 + G ω) ≤ ENNReal.ofReal (Cd * (1 + t)) := by
        rw [ENNReal.ofReal_mul hCd, ENNReal.ofReal_add zero_le_one ht0.le, ENNReal.ofReal_one]
        exact mul_le_mul_right (add_le_add_right hlt'.le 1) _
      exact lt_irrefl _ ((show ENNReal.ofReal r < _ from hω).trans_le
        (h2.trans (ENNReal.ofReal_le_ofReal hCt)))
    have hmark : ENNReal.ofReal t ^ q * Pr {ω | ENNReal.ofReal t ^ q ≤ G ω ^ q} ≤
        ENNReal.ofReal (C₃ ^ q) :=
      (mul_meas_ge_le_lintegral₀ (hG.pow_const q).aemeasurable _).trans hmom
    have hεpos : ENNReal.ofReal t ^ q ≠ 0 := by
      rw [← ENNReal.ofReal_pow ht0.le]
      exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    refine (measure_mono hsub).trans ?_
    have hP : Pr {ω | ENNReal.ofReal t ^ q ≤ G ω ^ q} ≤
        ENNReal.ofReal (C₃ ^ q) / ENNReal.ofReal t ^ q := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hεpos) (Or.inl (by simp))]
      rwa [mul_comm]
    refine hP.trans ?_
    rw [← ENNReal.ofReal_pow ht0.le, ← ENNReal.ofReal_div_of_pos (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [ht, div_pow, div_div_eq_mul_div, ← div_eq_mul_inv, div_le_div_iff_of_pos_right hpos]
    calc C₃ ^ q * (2 * Cd) ^ q ≤ max 1 (C₃ ^ q) * (2 * Cd + 1) ^ q :=
          mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (by positivity) (by linarith) q)
            (by positivity) (by positivity)
      _ = (2 * Cd + 1) ^ q * max 1 (C₃ ^ q) := mul_comm _ _

end CurvatureVariance.Paper.Gain.LabelResidual
