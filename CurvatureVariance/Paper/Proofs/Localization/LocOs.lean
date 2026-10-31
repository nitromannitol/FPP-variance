/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Os.Basic
public import CurvatureVariance.Infra.Os.Power
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `O_s` estimates for Lemma `lem:localization`

As in the module `IsotropicVariance.Paper.Proofs.Localization.Os` of the continuum library:

* `isOs_sup'_sub`: the supremum over finitely many thickenings of `X_i − w_i`, with `X_i ≤ O_1(θ)`
  and weights whose exponential sum `Σ_i e^{−w_i/(2θ)}` is bounded, is `O_1(Cθ)` with `C` depending
  on that sum only. This is "the sum of the tails of their `O₁` terms over the thickenings and over
  `β`, as in the proof of [AB26, (5.3)]" (the second change in the proof of Lemma
  `lem:localization`).
* `isOs_sqrt`: `X ≤ O_1(θ)` gives `√X₊ ≤ O_2(√θ)`.

New here, in place of the Gaussian sum `sum_exp_neg_sq_le` of the model, whose index set is a box:

* `sum_pow_mul_exp_neg_sq_le`: the sum over the annuli `Σ_{β ≥ 1} β^k e^{−cβ²}` is bounded uniformly
  in the number of annuli.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Infra.Os

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The supremum of finitely many almost everywhere measurable functions. As
`IsotropicVariance.Paper.Proofs.Localization.aemeasurable_sup'` in the continuum library. -/
lemma aemeasurable_sup' {ι : Type*} (T : Finset ι) (hT : T.Nonempty) {X : ι → Ω → ℝ}
    (hX : ∀ i ∈ T, AEMeasurable (X i) P) : AEMeasurable (T.sup' hT X) P :=
  Finset.sup'_induction hT X (p := fun f => AEMeasurable f P)
    (fun _ hf _ hg => AEMeasurable.sup hf hg) hX

/-- **The weighted union bound**: `sup_i (X_i − w_i) ≤ O_1(log₂(1 + 2S) · 2θ)` if every
`X_i ≤ O_1(θ)` and `Σ_i e^{−w_i/(2θ)} ≤ S`, `S ≥ 1`. As
`IsotropicVariance.Paper.Proofs.Localization.isOs_sup'_sub` in the continuum library. -/
theorem isOs_sup'_sub [IsProbabilityMeasure P] {ι : Type*} (T : Finset ι) (hT : T.Nonempty)
    {θ S : ℝ} (hθ : 0 < θ) (hS : 1 ≤ S) (X : ι → Ω → ℝ) (w : ι → ℝ)
    (hX : ∀ i ∈ T, IsOs P 1 θ (X i)) (hw : ∑ i ∈ T, Real.exp (-(w i) / (2 * θ)) ≤ S) :
    IsOs P 1 (Real.logb 2 (1 + 2 * S) * (2 * θ)) (T.sup' hT fun i ω => X i ω - w i) := by
  have hmeas : AEMeasurable (T.sup' hT fun i ω => X i ω - w i) P :=
    aemeasurable_sup' T hT fun i hi => (hX i hi).1.sub_const _
  have hr : 1 ≤ Real.logb 2 (1 + 2 * S) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; linarith
  have h := isOs_of_exp_moment_le (P := P) (s := 1) zero_lt_one (by positivity : 0 < 2 * θ) hr
    hmeas ?_
  · simpa using h
  -- the exponential moment of the supremum is at most `1 + √2 S`
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp ((max ((T.sup' hT fun i ω => X i ω - w i) ω) 0 /
      (2 * θ)) ^ (1 : ℝ))) ≤ 1 + ∑ i ∈ T, ENNReal.ofReal (Real.exp (-(w i) / (2 * θ))) *
        ENNReal.ofReal (Real.exp (max (X i ω) 0 / (2 * θ))) := by
    intro ω
    rw [Real.rpow_one, Finset.sup'_apply]
    rcases le_total (T.sup' hT fun i => X i ω - w i) 0 with h0 | h0
    · rw [max_eq_right h0, zero_div, Real.exp_zero, ENNReal.ofReal_one]
      exact le_self_add
    · rw [max_eq_left h0]
      obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' hT fun i => X i ω - w i
      rw [hmax]
      refine le_trans ?_ (le_add_left (Finset.single_le_sum (f := fun i =>
        ENNReal.ofReal (Real.exp (-(w i) / (2 * θ))) *
          ENNReal.ofReal (Real.exp (max (X i ω) 0 / (2 * θ)))) (fun _ _ => bot_le) hi))
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith [le_max_left (X i ω) 0]) (by positivity)
  have hhalf : ∀ i ∈ T, ∫⁻ ω, ENNReal.ofReal (Real.exp (max (X i ω) 0 / (2 * θ))) ∂P ≤
      ENNReal.ofReal (Real.sqrt 2) := by
    intro i hi
    have hm : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (max (X i ω) 0 / θ))) P := by
      have := aemeasurable_exp_pos_rpow (hX i hi).1 1 θ
      simpa using this
    have hJ := lintegral_rpow_le hm (a := 1 / 2) (by norm_num) (by norm_num)
    have h2 : (∫⁻ ω, ENNReal.ofReal (Real.exp (max (X i ω) 0 / θ)) ∂P) ≤ 2 := by
      have := (hX i hi).2
      simpa using this
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (max (X i ω) 0 / (2 * θ))) ∂P
        = ∫⁻ ω, ENNReal.ofReal (Real.exp (max (X i ω) 0 / θ)) ^ (1 / 2 : ℝ) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
          congr 2
          field_simp
      _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (max (X i ω) 0 / θ)) ∂P) ^ (1 / 2 : ℝ) := hJ
      _ ≤ (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h2 (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt 2) := by
          rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
          simp
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((max ((T.sup' hT fun i ω => X i ω - w i) ω) 0 /
        (2 * θ)) ^ (1 : ℝ))) ∂P
      ≤ ∫⁻ ω, (1 + ∑ i ∈ T, ENNReal.ofReal (Real.exp (-(w i) / (2 * θ))) *
          ENNReal.ofReal (Real.exp (max (X i ω) 0 / (2 * θ)))) ∂P := lintegral_mono hpt
    _ = 1 + ∑ i ∈ T, ENNReal.ofReal (Real.exp (-(w i) / (2 * θ))) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (max (X i ω) 0 / (2 * θ))) ∂P := by
        have hm : ∀ i ∈ T, AEMeasurable
            (fun ω => ENNReal.ofReal (Real.exp (max (X i ω) 0 / (2 * θ)))) P := fun i hi =>
          (((hX i hi).1.max aemeasurable_const).div_const _).exp.ennreal_ofReal
        rw [lintegral_add_left' aemeasurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_finsetSum' _ fun i hi => (hm i hi).const_mul _]
        congr 1
        exact Finset.sum_congr rfl fun i hi => lintegral_const_mul'' _ (hm i hi)
    _ ≤ 1 + ∑ i ∈ T, ENNReal.ofReal (Real.exp (-(w i) / (2 * θ))) *
          ENNReal.ofReal (Real.sqrt 2) := by
        gcongr with i hi
        exact hhalf i hi
    _ = 1 + ENNReal.ofReal ((∑ i ∈ T, Real.exp (-(w i) / (2 * θ))) * Real.sqrt 2) := by
        rw [← Finset.sum_mul, ENNReal.ofReal_mul (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le),
          ENNReal.ofReal_sum_of_nonneg fun _ _ => (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (1 + 2 * S) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have : Real.sqrt 2 ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        nlinarith [Finset.sum_nonneg fun i (_ : i ∈ T) => (Real.exp_pos (-(w i) / (2 * θ))).le]
    _ = (2 : ℝ≥0∞) ^ Real.logb 2 (1 + 2 * S) := by
        rw [← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_rpow_of_pos (by norm_num),
          Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]

/-- `X ≤ O_1(θ)` gives `√X₊ ≤ O_2(√θ)`. As `IsotropicVariance.Paper.Proofs.Localization.isOs_sqrt`
in the continuum library. -/
theorem isOs_sqrt {θ : ℝ} (hθ : 0 < θ) {X : Ω → ℝ} (hX : IsOs P 1 θ X) :
    IsOs P 2 (Real.sqrt θ) (fun ω => Real.sqrt (max (X ω) 0)) := by
  refine ⟨(hX.1.max aemeasurable_const).sqrt, (lintegral_mono fun ω => ?_).trans hX.2⟩
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq ?_))
  rw [max_eq_left (Real.sqrt_nonneg _), Real.rpow_one, Real.rpow_two, div_pow,
    Real.sq_sqrt (le_max_right _ _), Real.sq_sqrt hθ.le]

/-- **The sum over the annuli**: `Σ_{1 ≤ β ≤ B} β^k e^{−cβ²}` is bounded uniformly in `B`. -/
theorem sum_pow_mul_exp_neg_sq_le {c : ℝ} (hc : 0 < c) (k B : ℕ) :
    ∑ β ∈ Finset.Icc 1 B, (β : ℝ) ^ k * Real.exp (-c * (β : ℝ) ^ 2) ≤
      ∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-c * n) := by
  have hs := Real.summable_pow_mul_exp_neg_nat_mul k hc
  refine le_trans (Finset.sum_le_sum fun β hβ => ?_) (hs.sum_le_tsum (Finset.Icc 1 B)
    fun n _ => by positivity)
  have h1 : (1 : ℝ) ≤ β := by exact_mod_cast (Finset.mem_Icc.1 hβ).1
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have h2 : (β : ℝ) ≤ (β : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- The constant of the sum over the annuli is positive when `k ≥ 0`: the term `n = 1`. -/
theorem tsum_pow_mul_exp_neg_pos {c : ℝ} (hc : 0 < c) (k : ℕ) :
    0 < ∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-c * n) := by
  have hs := Real.summable_pow_mul_exp_neg_nat_mul k hc
  refine hs.tsum_pos (fun n => by positivity) 1 ?_
  simp only [Nat.cast_one, one_pow, one_mul, mul_one]
  positivity

end CurvatureVariance.Paper.Localization.Loc
