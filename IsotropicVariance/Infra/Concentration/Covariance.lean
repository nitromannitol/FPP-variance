/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Concentration.Basic
import Mathlib.Tactic.Linarith

/-! # Opposite-order covariance

The double-integral proof of the covariance inequality used in the entropy
argument for BLM Theorem 7 (printed p. 1592).
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Real Filter
namespace IsotropicVariance.Infra.Concentration

/-- Oppositely ordered functions have nonpositive covariance. -/
theorem integral_mul_le_mul_integral_of_opposite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {a b : Ω → ℝ}
    (ha : Integrable a P) (hb : Integrable b P) (hab : Integrable (fun x => a x * b x) P)
    (h : ∀ x y, (a x - a y) * (b x - b y) ≤ 0) :
    (∫ x, a x * b x ∂P) ≤ (∫ x, a x ∂P) * ∫ x, b x ∂P := by
  have hPoint (x y : Ω) : a x * b x + a y * b y ≤ a x * b y + a y * b x := by
    nlinarith only [h x y]
  have hFirst (y : Ω) : (∫ x, a x * b x ∂P) + a y * b y ≤
      (∫ x, a x ∂P) * b y + a y * ∫ x, b x ∂P := by
    have hh := integral_mono (hab.add (integrable_const (a y * b y)))
      ((ha.mul_const (b y)).add (hb.const_mul (a y))) (fun x => hPoint x y)
    dsimp only [Pi.add_apply] at hh
    simpa only [integral_add hab (integrable_const (a y * b y)), integral_const,
      probReal_univ, smul_eq_mul, one_mul,
      integral_add (ha.mul_const (b y)) (hb.const_mul (a y)), integral_mul_const,
      integral_const_mul] using hh
  have hh := integral_mono ((integrable_const (∫ x, a x * b x ∂P)).add hab)
    ((hb.const_mul (∫ x, a x ∂P)).add (ha.mul_const (∫ x, b x ∂P))) hFirst
  dsimp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) hab,
    integral_add (hb.const_mul _) (ha.mul_const _), integral_const, probReal_univ,
    smul_eq_mul, one_mul, integral_const_mul, integral_mul_const] at hh
  linarith only [hh]

end IsotropicVariance.Infra.Concentration
