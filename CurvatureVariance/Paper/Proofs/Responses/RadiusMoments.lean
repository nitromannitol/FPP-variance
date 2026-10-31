/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.SlabArrays
public import CurvatureVariance.Infra.Arrays.Basic
import CurvatureVariance.Paper.Proofs.Responses.LoadAnalysis
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.Positivity

/-!
# Polynomial tails of squared localization radii

The order-`128d²` localization moment controls the lower moments needed by the independent
array bound. These estimates concern the raw radius; zero extension outside retained pairs
can then be handled by the existing array infrastructure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A scaled localization radius `C(1+R)` has bounded lower moments when `R ≥ 1`. -/
theorem lintegral_scaled_radius_pow_le {R : Ω → ℝ≥0∞} {p q : ℕ}
    (hqp : q ≤ p) (hR1 : ∀ ω, 1 ≤ R ω) {C Cb : ℝ} (hC : 0 ≤ C)
    (hm : (∫⁻ ω, R ω ^ p ∂P) ≤ ENNReal.ofReal (Cb ^ p)) :
    (∫⁻ ω, (ENNReal.ofReal C * (1 + R ω)) ^ q ∂P) ≤
      ENNReal.ofReal ((2 * C + 1) ^ q * Cb ^ p) := by
  have hpt : ∀ ω, (ENNReal.ofReal C * (1 + R ω)) ^ q ≤
      ENNReal.ofReal ((2 * C + 1) ^ q) * R ω ^ p := by
    intro ω
    have hR : ENNReal.ofReal C * (1 + R ω) ≤ ENNReal.ofReal (2 * C + 1) * R ω := by
      calc
        _ ≤ ENNReal.ofReal C * (R ω + R ω) := mul_le_mul' le_rfl (add_le_add (hR1 ω) le_rfl)
        _ = ENNReal.ofReal (2 * C) * R ω := by
          rw [two_mul, ENNReal.ofReal_add hC hC, mul_add, add_mul]
        _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
    calc
      _ ≤ (ENNReal.ofReal (2 * C + 1) * R ω) ^ q := pow_le_pow_left₀ bot_le hR q
      _ = ENNReal.ofReal ((2 * C + 1) ^ q) * R ω ^ q := by
        rw [mul_pow, ENNReal.ofReal_pow (by positivity)]
      _ ≤ _ := mul_le_mul' le_rfl (pow_le_pow_right₀ (hR1 ω) hqp)
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal ((2 * C + 1) ^ q) * R ω ^ p ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal ((2 * C + 1) ^ q) * ∫⁻ ω, R ω ^ p ∂P :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2 * C + 1) ^ q) * ENNReal.ofReal (Cb ^ p) := mul_le_mul' le_rfl hm
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-- A nonzero integer vector has Euclidean norm at least one. -/
theorem norm_transversePoint_zero_or_one_le {m : ℕ} (v : Fin m → ℤ) :
    ‖transversePoint v‖ = 0 ∨ 1 ≤ ‖transversePoint v‖ := by
  by_cases hv : v = 0
  · left
    simp only [hv, Infra.FPP.transversePoint_zero, norm_zero]
  · right
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    have h1 : (1 : ℝ) ≤ |(v j : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hj
    exact h1.trans (by simpa only [Real.norm_eq_abs, transversePoint] using PiLp.norm_apply_le (transversePoint v) j)

end CurvatureVariance.Paper.Responses
