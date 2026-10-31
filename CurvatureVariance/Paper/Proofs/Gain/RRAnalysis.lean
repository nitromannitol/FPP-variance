/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Cubes
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Analytic lemmas for equation `eq:rewardmoment`: moments and random tubes

Two estimates used in the proof of the first bound `‖Y_i(j,k)‖_{16d} ≤ C(1 + |j − k|)` of equation
`eq:rewardmoment`, besides those of the module
`CurvatureVariance.Paper.Proofs.Responses.LoadAnalysis` (Minkowski for countable sums, Hölder with
an indicator, the lattice sum about a segment):

* `measure_mem_tubeIndices_le`: Markov's inequality for a random tube radius `C_d(1 + G)` with
  `E G^q ≤ C₃^q`: an index at distance `r` from `[j, k]` lies in the tube with probability
  `≤ C (1 + r)^{-q}`;
* `lintegral_pow_le_of_eLpNorm_le`: an `L^n` bound as a bound for the `n`-th moment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

/-- An `L^n` bound for an integer exponent `n ≥ 1` is a bound for the `n`-th moment. -/
theorem lintegral_pow_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 0 ≤ c)
    (h : eLpNorm f (ENNReal.ofReal n) μ ≤ ENNReal.ofReal c) :
    ∫⁻ ω, f ω ^ n ∂μ ≤ ENNReal.ofReal (c ^ n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; omega) ENNReal.ofReal_ne_top
    hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hn0.le] at h
  have h2 := ENNReal.rpow_le_rpow h (by positivity : (0 : ℝ) ≤ n)
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hn0.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hc hn0.le, Real.rpow_natCast] at h2
  simpa only [enorm_eq_self, ENNReal.rpow_natCast] using h2

/-! ### A random tube contains a given index with small probability -/

/-- **An index lies in a random tube with small probability** (the proof of the first bound of
equation `eq:rewardmoment`): for a random radius `G` with `E G^q ≤ C₃^q` and `C_d ≥ 0`, the tube of
radius `C_d(1 + G)` (stated before Lemma `lem:blocks`) contains `ℓ` with probability at most
`max ((2C_d + 3)^q) ((2(C_d + 1))^q C₃^q) (1 + dist(ℓ, [j, k]))^{-q}`. -/
theorem measure_mem_tubeIndices_le {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    [IsProbabilityMeasure Pr] {Cd : ℝ} (hCd : 0 ≤ Cd) {G : Ω → ℝ≥0∞} (hG : Measurable G)
    {q : ℕ} {C₃ : ℝ}
    (hmom : ∫⁻ ω, G ω ^ q ∂Pr ≤ ENNReal.ofReal (C₃ ^ q)) (j k ℓ : Fin m → ℤ) :
    Pr {ω | ℓ ∈ tubeIndices j k (ENNReal.ofReal Cd * (1 + G ω))} ≤
      ENNReal.ofReal (max ((2 * Cd + 3) ^ q) ((2 * (Cd + 1)) ^ q * C₃ ^ q) *
        (1 + Metric.infDist (transversePoint ℓ)
          (segment ℝ (transversePoint j) (transversePoint k))) ^ (-(q : ℝ))) := by
  set d := Metric.infDist (transversePoint ℓ)
    (segment ℝ (transversePoint j) (transversePoint k)) with hd
  have hd0 : 0 ≤ d := Metric.infDist_nonneg
  set M : ℝ := max ((2 * Cd + 3) ^ q) ((2 * (Cd + 1)) ^ q * C₃ ^ q) with hM
  have hpos : 0 < (1 + d) ^ (q : ℕ) := by positivity
  have hrpow : (1 + d) ^ (-(q : ℝ)) = ((1 + d) ^ q)⁻¹ := by
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast]
  rw [hrpow]
  by_cases hcase : d ≤ 2 * Cd + 2
  · refine (prob_le_one).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
    exact (pow_le_pow_left₀ (by linarith) (by linarith) q).trans (le_max_left _ _)
  · push Not at hcase
    have hc1 : 0 < 2 * (Cd + 1) := by linarith
    set t : ℝ := (1 + d) / (2 * (Cd + 1)) with ht
    have ht0 : 0 < t := by positivity
    -- `C_d (1 + t) < d`
    have hCt : Cd * (1 + t) < d := by
      have h1 : Cd * t ≤ (1 + d) / 2 := by
        rw [ht, mul_div_assoc', div_le_div_iff₀ hc1 (by norm_num)]
        nlinarith
      nlinarith
    have hsub : {ω | ℓ ∈ tubeIndices j k (ENNReal.ofReal Cd * (1 + G ω))} ⊆
        {ω | ENNReal.ofReal t ^ q ≤ G ω ^ q} := by
      intro ω hω
      by_contra hlt
      have hlt' : G ω < ENNReal.ofReal t := by
        by_contra h; exact hlt (pow_le_pow_left₀ bot_le (not_lt.1 h) q)
      have h1 : ENNReal.ofReal d ≤ ENNReal.ofReal Cd * (1 + G ω) := hω
      have h2 : ENNReal.ofReal Cd * (1 + G ω) ≤ ENNReal.ofReal (Cd * (1 + t)) := by
        rw [ENNReal.ofReal_mul hCd, ENNReal.ofReal_add zero_le_one ht0.le, ENNReal.ofReal_one]
        exact mul_le_mul_right (add_le_add_right hlt'.le 1) _
      have h3 := h1.trans h2
      rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
      linarith
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
    calc C₃ ^ q * (2 * (Cd + 1)) ^ q = (2 * (Cd + 1)) ^ q * C₃ ^ q := mul_comm _ _
      _ ≤ M := le_max_right _ _

end CurvatureVariance.Paper.Gain
