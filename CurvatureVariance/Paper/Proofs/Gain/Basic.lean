/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Real

/-!
# An elementary tool for Section `sec:gain`

`evariance_le_two_mul_add`: `Var X ≤ 2 Var Y + 2 ‖X − Y‖₂²`, in `[0, ∞]`, with no integrability
assumption. It serves the comparison of `F̄` with the passage time in the proof of Proposition
`prop:gain`, and the reduction to the targets at the beginning of Section `sec:gain`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

/-- `Var(Y + Z) ≤ 2 Var Y + 2 Var Z` for square-integrable `Y, Z`. -/
theorem variance_add_le_two_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y Z : Ω → ℝ} (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P) :
    variance (Y + Z) P ≤ 2 * variance Y P + 2 * variance Z P := by
  have h1 := variance_add hY hZ
  have h2 := variance_sub hY hZ
  have h3 : 0 ≤ variance (Y - Z) P := variance_nonneg _ _
  linarith

/-- **`Var X ≤ 2 Var Y + 2 ‖X − Y‖₂²`**, in `[0, ∞]`. -/
theorem evariance_le_two_mul_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P) :
    evariance X P ≤ 2 * evariance Y P + 2 * eLpNorm (X - Y) 2 P ^ 2 := by
  by_cases hYm : MemLp Y 2 P
  swap
  · rw [evariance_eq_top hY hYm]; simp
  by_cases hZm : MemLp (X - Y) 2 P
  swap
  · have : eLpNorm (X - Y) 2 P = ⊤ := by
      by_contra h
      exact hZm (lt_top_iff_ne_top.2 h)
    rw [this]; simp
  have hXeq : X = Y + (X - Y) := by funext ω; simp
  have hXm : MemLp X 2 P := by rw [hXeq]; exact hYm.add hZm
  rw [← ofReal_variance hXm, ← ofReal_variance hYm]
  have hvar := variance_add_le_two_mul hYm hZm
  rw [← hXeq] at hvar
  have hVZ : variance (X - Y) P ≤ ∫ ω, (X - Y) ω ^ 2 ∂P := by
    simpa only [Pi.pow_apply] using variance_le_expectation_sq hZm.aestronglyMeasurable
  have hL2 : ENNReal.ofReal (∫ ω, (X - Y) ω ^ 2 ∂P) = eLpNorm (X - Y) 2 P ^ 2 := by
    rw [hZm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 1
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  calc ENNReal.ofReal (variance X P) ≤ ENNReal.ofReal (2 * variance Y P + 2 * variance (X - Y) P) :=
        ENNReal.ofReal_le_ofReal hvar
    _ ≤ ENNReal.ofReal (2 * variance Y P + 2 * ∫ ω, (X - Y) ω ^ 2 ∂P) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = 2 * ENNReal.ofReal (variance Y P) + 2 * eLpNorm (X - Y) 2 P ^ 2 := by
        rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (variance_nonneg Y P))
          (mul_nonneg (by norm_num) (integral_nonneg fun ω => sq_nonneg _)), ← hL2,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        simp

end CurvatureVariance.Paper.Gain
