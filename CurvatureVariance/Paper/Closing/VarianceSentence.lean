/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Closing
import CurvatureVariance.Paper.Closing.Induction
import CurvatureVariance.Paper.Closing.MainExp

/-!
# The variance sentence after Theorem `thm:main`

The sentence after Theorem `thm:main`: "Theorem `thm:main` implies that
`Var[T(0,x)] ≤ 2C²|x|^{1−ε}` for every such `x`."

* `evariance_le_of_lintegral_exp_le`: if `E[exp(|X − c| / s)] ≤ 2`, then `Var X ≤ 2 s²`. Indeed
  `e^t ≥ 1 + t² / 2` for `t ≥ 0` gives `E[(X − c)²] ≤ 2 s²`, and the variance is at most the second
  moment about any constant.
* `evariance_le_of_lintegral_exp_rpow_le`: the case `s = C r^{(1−ε)/2}`, the scale of Theorem
  `thm:main`.
* `varianceSentenceStatement`: the contract `Contracts.VarianceSentenceStatement`.
* `evariance_le_of_isAbsOs_two`, `evariance_passageTime_le_of_premise`: the same argument for
  equation `eq:premise`: `Var T(0,(s,y)) ≤ 2 Q_s² = 2 A² s^{1−2δ/K}`.

The two first theorems are those of `IsotropicVariance.Paper.Closing.VarianceSentence` (continuum
library), with the same statements.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Closing

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

/-- A random variable whose exponential moment on the scale `s` about a constant `c` is at most
`2` has variance at most `2 s²`. As in the continuum library's
`IsotropicVariance.Paper.Closing.VarianceSentence`. -/
theorem evariance_le_of_lintegral_exp_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P) {c s : ℝ} (hs : 0 < s)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω - c| / s)) ∂P ≤ 2) :
    evariance X P ≤ ENNReal.ofReal (2 * s ^ 2) := by
  have hs2 : 0 < 2 * s ^ 2 := by positivity
  have hY : AEMeasurable (fun ω => X ω - c) P := hX.sub_const c
  have hpt : ∀ ω, ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) + 1 ≤
      ENNReal.ofReal (Real.exp (|X ω - c| / s)) := by
    intro ω
    have ht : 0 ≤ |X ω - c| / s := div_nonneg (abs_nonneg _) hs.le
    have hq := Real.quadratic_le_exp_of_nonneg ht
    have hsq : (|X ω - c| / s) ^ 2 / 2 = (X ω - c) ^ 2 / (2 * s ^ 2) := by
      rw [div_pow, sq_abs, div_div, mul_comm (s ^ 2)]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (div_nonneg (sq_nonneg _) hs2.le) zero_le_one]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hq, hsq, ht])
  have hmass : ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) ∂P ≤ 1 := by
    have hadd : ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) ∂P + 1 ≤ 1 + 1 := by
      calc ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) ∂P + 1
          = ∫⁻ ω, (ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) + 1) ∂P := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω - c| / s)) ∂P := lintegral_mono hpt
        _ ≤ 2 := h
        _ = 1 + 1 := one_add_one_eq_two.symm
    exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 hadd
  have hsecond : ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2) ∂P ≤ ENNReal.ofReal (2 * s ^ 2) := by
    calc ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2) ∂P
        = ∫⁻ ω, ENNReal.ofReal (2 * s ^ 2) *
            ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [← ENNReal.ofReal_mul hs2.le, mul_div_cancel₀ _ hs2.ne']
      _ = ENNReal.ofReal (2 * s ^ 2) *
            ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * s ^ 2) * 1 := mul_le_mul_right hmass _
      _ = ENNReal.ofReal (2 * s ^ 2) := mul_one _
  have hint : Integrable (fun ω => (X ω - c) ^ 2) P := by
    refine ⟨(hY.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)]
    exact hsecond.trans_lt ENNReal.ofReal_lt_top
  have hYL : MemLp (fun ω => X ω - c) 2 P :=
    (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).2 hint
  have hXL : MemLp X 2 P := by
    have hsum := hYL.add (memLp_const c)
    have hfun : (fun ω => X ω - c) + (fun _ => c) = X := by
      funext ω
      exact sub_add_cancel (X ω) c
    rwa [hfun] at hsum
  rw [← hXL.ofReal_variance_eq, ← variance_sub_const hX.aestronglyMeasurable c]
  calc ENNReal.ofReal (variance (fun ω => X ω - c) P)
      ≤ ENNReal.ofReal (∫ ω, (X ω - c) ^ 2 ∂P) :=
        ENNReal.ofReal_le_ofReal (variance_le_expectation_sq hY.aestronglyMeasurable)
    _ = ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2) ∂P :=
        ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => sq_nonneg _)
    _ ≤ ENNReal.ofReal (2 * s ^ 2) := hsecond

/-- The case `s = C r^{(1−ε)/2}` of `evariance_le_of_lintegral_exp_le`, for `r ≥ 1`: the variance
is at most `2 C² r^{1-ε}`. As in the continuum library's
`IsotropicVariance.Paper.Closing.VarianceSentence`. -/
theorem evariance_le_of_lintegral_exp_rpow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P) {c C ε r : ℝ} (hC : 0 < C)
    (hr : 1 ≤ r)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω - c| / (C * r ^ ((1 - ε) / 2)))) ∂P ≤ 2) :
    evariance X P ≤ ENNReal.ofReal (2 * C ^ 2 * r ^ (1 - ε)) := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hs : 0 < C * r ^ ((1 - ε) / 2) := mul_pos hC (Real.rpow_pos_of_pos (by linarith only [hr]) _)
  have hsq : (r ^ ((1 - ε) / 2)) ^ 2 = r ^ (1 - ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0]
    norm_num
  have hb := evariance_le_of_lintegral_exp_le hX hs h
  rwa [mul_pow, hsq, ← mul_assoc] at hb

/-- **The sentence after Theorem `thm:main`**, with the same `ε` and `C`. -/
theorem varianceSentenceStatement {m : ℕ} (hM : MainExpStatement m) :
    VarianceSentenceStatement m := by
  intro hm F _ hW P _ hP μ hμ δ r M c hδ hδ₁ hr hM' hc
  obtain ⟨ε, hε, C, hC, hb⟩ := hM hm F hW P hP μ hμ δ r M c hδ hδ₁ hr hM' hc
  refine ⟨ε, hε, C, hC, fun ξ hξ hCξ x hx hnear => ?_⟩
  obtain ⟨h1, h2⟩ := hb ξ hξ hCξ x hx hnear
  exact ⟨h1, h2, evariance_le_of_lintegral_exp_rpow_le h1 hC (one_le_norm_point hx) h2⟩

/-- `|X − c| ≤ O₁(θ)` gives `Var X ≤ 2 θ²`. -/
theorem evariance_le_of_isAbsOs_two {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {c θ : ℝ} (hθ : 0 < θ)
    (h : IsAbsOs P 1 θ (fun ω => X ω - c)) : evariance X P ≤ ENNReal.ofReal (2 * θ ^ 2) := by
  have hX : AEMeasurable X P := by
    have h1 := h.1.add_const c
    simpa only [sub_add_cancel] using h1
  exact evariance_le_of_lintegral_exp_le hX hθ (lintegral_exp_le_of_isAbsOs hθ le_rfl h)

/-- Equation `eq:premise` at every length gives `Var T(0,(s,y)) ≤ 2 Q_s² = 2 A² s^{1−2δ/K}` on
`𝒟(s)`. -/
theorem evariance_passageTime_le_of_premise {m : ℕ} {M : Model m} [IsProbabilityMeasure M.P]
    {K : ℕ} {A : ℝ} (hA : 1 ≤ A) (hprem : ∀ N, Premise M K A N) {s : ℕ} (hs : 1 ≤ s)
    {y : Fin m → ℤ} (hy : y ∈ premiseDomain M s) :
    evariance (fun ω => passageTimeReal ω 0 ((s : ℤ), y)) M.P ≤
      ENNReal.ofReal (2 * A ^ 2 * (s : ℝ) ^ (1 - 2 * (M.δ / K))) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hQ := Q_pos M K hA hs0
  have hle : (s : ℝ) ≤ 2 * ((2 * s : ℕ) : ℝ) / 3 := by
    push_cast
    linarith only [hs0]
  refine (evariance_le_of_isAbsOs_two hQ (hprem (2 * s) s hs hle y hy)).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  have hQsq : Q M K A s ^ 2 = A ^ 2 * (s : ℝ) ^ (1 - 2 * (M.δ / K)) := by
    rw [Q, mul_pow, ← Real.rpow_natCast ((s : ℝ) ^ _) 2, ← Real.rpow_mul hs0.le]
    congr 2
    push_cast
    ring
  rw [hQsq]
  ring

end CurvatureVariance.Paper.Closing
