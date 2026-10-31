/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The radius threshold of the localization event

In the proof of Lemma `lem:labels`, a slab geodesic between points of the subcube of a block leaves
the block only if the localization radius exceeds `r(L) = (⌈√L⌉ − 1)/(C_d + 1) − 1`
(`leaveRadius`): below it the tube radius `C_d(1 + r)` of Section `sec:gain` is less than the
margin `⌈√L⌉` of the subcube (`mul_one_add_leaveRadius_lt`). For `L ≥ ((8 C_d + 17)/7)²`,
`r(L) ≥ √(L + 1)/(8(C_d + 1))` (`leaveRadius_ge`), so Markov's inequality with a moment of the
radius makes the probability of leaving small. Here `m = d − 1`.
-/

@[expose] public section

open Filter Topology

namespace CurvatureVariance.Paper.Gain

/-- The radius threshold `r(L) = (⌈√L⌉ − 1)/(C_d + 1) − 1`. -/
noncomputable def leaveRadius (Cd : ℝ) (L : ℕ) : ℝ := ((⌈Real.sqrt L⌉₊ : ℝ) - 1) / (Cd + 1) - 1

/-- Below the threshold, the tube radius `C_d (1 + r)` is less than `⌈√L⌉`. -/
theorem mul_one_add_leaveRadius_lt {Cd : ℝ} (hCd : 0 ≤ Cd) {L : ℕ} (hr : 0 < leaveRadius Cd L) :
    Cd * (1 + leaveRadius Cd L) < ⌈Real.sqrt L⌉₊ := by
  have hd : 0 < Cd + 1 := by linarith
  have hX : 0 ≤ (⌈Real.sqrt L⌉₊ : ℝ) - 1 := by
    unfold leaveRadius at hr
    have : 1 < ((⌈Real.sqrt L⌉₊ : ℝ) - 1) / (Cd + 1) := by linarith
    rw [lt_div_iff₀ hd] at this
    linarith
  have h1 : 1 + leaveRadius Cd L = ((⌈Real.sqrt L⌉₊ : ℝ) - 1) / (Cd + 1) := by
    unfold leaveRadius; ring
  rw [h1, mul_div_assoc', div_lt_iff₀ hd]
  nlinarith

/-- For `L ≥ ((8 C_d + 17)/7)²`, the threshold is at least `√(L + 1)/(8(C_d + 1))`. -/
theorem leaveRadius_ge {Cd : ℝ} (hCd : 0 ≤ Cd) {L : ℕ} (hL : ((8 * Cd + 17) / 7) ^ 2 ≤ L) :
    Real.sqrt ((L : ℝ) + 1) / (8 * (Cd + 1)) ≤ leaveRadius Cd L := by
  have hs : (8 * Cd + 17) / 7 ≤ Real.sqrt L := Real.le_sqrt_of_sq_le hL
  have hceil : Real.sqrt L ≤ (⌈Real.sqrt L⌉₊ : ℝ) := Nat.le_ceil _
  have hsq : Real.sqrt ((L : ℝ) + 1) ≤ Real.sqrt L + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) L), Real.sqrt_nonneg (L : ℝ)]
  have hd : 0 < Cd + 1 := by linarith
  unfold leaveRadius
  rw [div_le_iff₀ (by positivity)]
  have e : (((⌈Real.sqrt L⌉₊ : ℝ) - 1) / (Cd + 1) - 1) * (8 * (Cd + 1)) =
      8 * ((⌈Real.sqrt L⌉₊ : ℝ) - 1) - 8 * (Cd + 1) := by
    field_simp
  rw [e]
  linarith

end CurvatureVariance.Paper.Gain
