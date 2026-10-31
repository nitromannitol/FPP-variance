/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.Moments
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The small penalized moment for far pairs

A real cutoff argument: a reward with `16d` moment bounded by `C(1+r)` has penalized `4d` moment
at most `λ^(4d)` once `r ≥ max(1,(2C/λ)^2)`. This is the far-pair estimate used in the proof of
Lemma `lem:residual`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.LabelResidual

/-- The explicit far-pair cutoff makes the moment ratio small, uniformly in the exponent. -/
theorem far_moment_ratio_le (p : ℕ) {C lam r : ℝ} (hC : 0 < C) (hlam : 0 < lam)
    (hr : max 1 ((2*C/lam)^2) ≤ r) :
    (C*(1+r))^(4*p) / (lam*r^2)^(3*p) ≤ lam^p := by
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := by linarith
  rw [div_le_iff₀ (by positivity)]
  have h1 : C*(1+r) ≤ 2*C*r := by nlinarith
  have h2 : (2*C)^2 ≤ lam^2*r := by
    have H := (le_max_right 1 ((2*C/lam)^2)).trans hr
    rw [div_pow, div_le_iff₀ (by positivity)] at H
    nlinarith only [H]
  calc
    (C*(1+r))^(4*p) ≤ (2*C*r)^(4*p) := pow_le_pow_left₀ (by positivity) h1 _
    _ = ((2*C)^2)^(2*p)*r^(4*p) := by rw [mul_pow, ← pow_mul]; ring_nf
    _ ≤ (lam^2*r)^(2*p)*r^(4*p) := by gcongr
    _ = lam^p*(lam*r^2)^(3*p) := by ring

/-- A `4p` reward moment of order `C(1+r)` gives a small penalized `p` moment at far pairs. -/
theorem lintegral_penalized_pow_le_far {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ≥0∞} (p : ℕ) {C lam r : ℝ} (hC : 0 < C) (hlam : 0 < lam)
    (hr : max 1 ((2*C/lam)^2) ≤ r)
    (h4p : ∫⁻ ω, Y ω^(4*p) ∂P ≤ ENNReal.ofReal ((C*(1+r))^(4*p))) :
    ∫⁻ ω, (Y ω - ENNReal.ofReal (lam*r^2))^p ∂P ≤ ENNReal.ofReal (lam^p) := by
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := by linarith
  apply (lintegral_sub_pow_le_far (by positivity : 0 < lam*r^2)
    (by positivity : 0 ≤ C*(1+r)) p ?_).trans
      (ENNReal.ofReal_le_ofReal (far_moment_ratio_le p hC hlam hr))
  simpa only [ENNReal.ofReal_pow (by positivity : 0 ≤ C*(1+r))] using h4p

end IsotropicVariance.Paper.Proofs.LabelResidual
