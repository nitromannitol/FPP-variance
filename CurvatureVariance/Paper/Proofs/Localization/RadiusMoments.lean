/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Os.Basic
public import CurvatureVariance.Infra.Os.Moments
public import CurvatureVariance.Infra.Os.Sum
public import CurvatureVariance.Infra.Os.Maximum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# An elementary bound for moments

`add_pow_le`: `(a + b)^q ≤ 2^q (a^q + b^q)` for `a, b ≥ 0`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Localization.Radius

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `(a + b)^q ≤ 2^q (a^q + b^q)` for `a, b ≥ 0`. -/
theorem add_pow_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (q : ℕ) :
    (a + b) ^ q ≤ 2 ^ q * (a ^ q + b ^ q) := by
  have h1 : a + b ≤ 2 * max a b := by
    have := le_max_left a b; have := le_max_right a b; linarith
  have h2 : max a b ^ q ≤ a ^ q + b ^ q := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ha q]
    · rw [max_eq_left h]; linarith [pow_nonneg hb q]
  calc (a + b) ^ q ≤ (2 * max a b) ^ q := pow_le_pow_left₀ (by positivity) h1 q
    _ = 2 ^ q * max a b ^ q := mul_pow _ _ _
    _ ≤ 2 ^ q * (a ^ q + b ^ q) := mul_le_mul_of_nonneg_left h2 (by positivity)

end CurvatureVariance.Paper.Localization.Radius
