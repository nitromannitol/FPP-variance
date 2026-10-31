/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Slabs
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The deterministic excess estimates in Lemma `lem:smallmean`

The near and far estimates in the proof of Lemma `lem:smallmean` combine
into a positive constant excess and quadratic growth (equation `eq:meanbelow`).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Mean

/-- An almost sure modulus with bounded `Lᵖ` norm bounds the difference of expectations. -/
theorem abs_integral_sub_le_of_ae_modulus {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X₁ X₂ Z : Ω → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (h₁ : Integrable X₁ P) (h₂ : Integrable X₂ P)
    (hmod : ∀ᵐ ω ∂P, |X₂ ω - X₁ ω| ≤ Z ω) {B : ℝ} (hB : 0 ≤ B)
    (hZ : eLpNorm Z p P ≤ ENNReal.ofReal B) :
    |∫ ω, X₂ ω ∂P - ∫ ω, X₁ ω ∂P| ≤ B := by
  have hD : AEStronglyMeasurable (fun ω => |X₂ ω - X₁ ω|) P :=
    (h₂.sub h₁).norm.aestronglyMeasurable
  have hpbound : eLpNorm (fun ω => |X₂ ω - X₁ ω|) p P ≤ ENNReal.ofReal B := by
    apply (eLpNorm_mono_ae hD ?_).trans hZ
    filter_upwards [hmod] with ω hω
    simpa only [Real.norm_eq_abs, abs_abs] using hω.trans (le_abs_self _)
  have h1bound : eLpNorm (fun ω => |X₂ ω - X₁ ω|) 1 P ≤ ENNReal.ofReal B :=
    (eLpNorm_le_eLpNorm_of_exponent_le hp).trans hpbound
  rw [eLpNorm_one_eq_lintegral_enorm hD] at h1bound
  rw [← integral_sub h₂ h₁]
  have hi := norm_integral_le_lintegral_norm (μ := P) (fun ω => X₂ ω - X₁ ω)
  have heq : (∫⁻ ω, ENNReal.ofReal ‖X₂ ω - X₁ ω‖ ∂P) =
      ∫⁻ ω, ‖|X₂ ω - X₁ ω|‖ₑ ∂P := by
    apply lintegral_congr
    intro ω
    simp only [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs, abs_abs]
  have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (heq.le.trans h1bound)
  rw [ENNReal.toReal_ofReal hB] at h3
  exact hi.trans h3

/-- A square bound for the distance from a point to its cube center. -/
theorem sq_ge_half_sq_sub {x a b : ℝ} (ha : 0 ≤ a) (h : a - b ≤ x) :
    a ^ 2 / 2 - b ^ 2 ≤ x ^ 2 := by
  by_cases hab : 0 ≤ a - b
  · nlinarith only [sq_nonneg (a - 2 * b), mul_self_le_mul_self hab h]
  · have hab' : a ≤ b := by linarith only [hab]
    nlinarith only [sq_nonneg x, sq_nonneg b, mul_self_le_mul_self ha hab']

end CurvatureVariance.Paper.Mean
