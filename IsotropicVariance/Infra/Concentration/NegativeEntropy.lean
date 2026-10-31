/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Concentration.ProductEntropy
public import IsotropicVariance.Infra.Concentration.BoundedDifference
public import IsotropicVariance.Infra.Concentration.Covariance

/-! # The negative-parameter entropy bound in BLM Theorem 7

The monotonicity of `g` and the opposite monotonicity of the exponential remove
the weighted factor `g(f)`; see BLM (2003), printed p. 1592.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal
namespace IsotropicVariance.Infra.Concentration

/-- A uniform absolute bound on an argument bounds its exponential. -/
theorem norm_exp_mul_le {x B : ℝ} (hx : |x| ≤ B) (θ : ℝ) :
    ‖exp (θ * x)‖ ≤ exp (|θ| * B) := by
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply exp_le_exp.mpr
  exact (le_abs_self _).trans ((abs_mul θ x).trans_le (mul_le_mul_of_nonneg_left hx (abs_nonneg θ)))

/-- For a negative parameter, the exponential and a monotone function of the
same random variable have nonpositive covariance. -/
theorem integral_exp_mul_monotone_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) (g : ℝ → ℝ) (hg : Monotone g)
    (hgi : Integrable (fun x => g (f x)) P) {θ : ℝ} (hθ : θ ≤ 0) :
    (∫ x, exp (θ * f x) * g (f x) ∂P) ≤
      (∫ x, exp (θ * f x) ∂P) * ∫ x, g (f x) ∂P := by
  apply integral_mul_le_mul_integral_of_opposite P (integrable_exp_of_abs_le P hf hB θ) hgi
    (hgi.bdd_mul (hf.const_mul θ).exp.aestronglyMeasurable
      (Eventually.of_forall fun x => norm_exp_mul_le (hB x) θ))
  intro x y
  rcases le_total (f x) (f y) with h | h
  · exact mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (exp_le_exp.mpr (mul_le_mul_of_nonpos_left h hθ)))
      (sub_nonpos.mpr (hg h))
  · exact mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (exp_le_exp.mpr (mul_le_mul_of_nonpos_left h hθ)))
      (sub_nonneg.mpr (hg h))

/-- The negative-parameter entropy estimate for the `K = 1` form of BLM Theorem 7. -/
theorem eentropy_exp_le_of_monotone_vPlus_bound {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) (g : ℝ → ℝ) (hg : Monotone g)
    (hg0 : ∀ z, 0 ≤ g z) (hgi : Integrable (fun x => g (f x)) (Measure.pi μ))
    (hV : ∀ᵐ x ∂Measure.pi μ, vPlus μ f x ≤ ENNReal.ofReal (g (f x)))
    (hdiff : ∀ x i y, |f x - f (Function.update x i y)| ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Icc (-1) 0) :
    IsotropicVariance.Infra.Entropy.eentropy (Measure.pi μ) (fun x => exp (θ * f x)) ≤
      ENNReal.ofReal (((exp 1 - 1) * ∫ x, g (f x) ∂Measure.pi μ) * θ ^ 2 *
        mgf f (Measure.pi μ) θ) := by
  obtain ⟨B, hB⟩ := exists_abs_le_of_update_le μ f hdiff
  have he : 0 ≤ exp 1 - 1 := sub_nonneg.mpr (by
    simpa only [exp_zero] using exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1))
  have hC : 0 ≤ θ ^ 2 * (exp 1 - 1) := mul_nonneg (sq_nonneg θ) he
  have hInt := integrable_exp_of_abs_le (Measure.pi μ) hf hB θ
  have hBound := eentropy_exp_le_lintegral_vPlus μ f hf θ (θ ^ 2 * (exp 1 - 1)) hC hInt
    (fun x i y hy => by
      have hd0 : 0 ≤ f x - f (Function.update x i y) := sub_nonneg.mpr hy
      have hd1 : f x - f (Function.update x i y) ≤ 1 := (le_abs_self _).trans (hdiff x i y)
      have hu0 : 0 ≤ -θ * (f x - f (Function.update x i y)) := mul_nonneg (neg_nonneg.mpr hθ.2) hd0
      have hu1 : -θ * (f x - f (Function.update x i y)) ≤ 1 := by
        calc
          _ ≤ 1 * 1 := mul_le_mul (by linarith only [hθ.1]) hd1 hd0 zero_le_one
          _ = _ := one_mul 1
      have hh := mul_exp_sub_one_le_sq_mul_exp_one hu0 hu1
      convert hh using 1; ring)
  have hProd : Integrable (fun x => exp (θ * f x) * g (f x)) (Measure.pi μ) :=
    hgi.bdd_mul (hf.const_mul θ).exp.aestronglyMeasurable
      (Eventually.of_forall fun x => norm_exp_mul_le (hB x) θ)
  have hWeight : (∫⁻ x, ENNReal.ofReal (exp (θ * f x)) * vPlus μ f x ∂Measure.pi μ) ≤
      ENNReal.ofReal ((∫ x, exp (θ * f x) ∂Measure.pi μ) * ∫ x, g (f x) ∂Measure.pi μ) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (exp (θ * f x) * g (f x)) ∂Measure.pi μ :=
        lintegral_mono_ae (hV.mono fun x hx => by
          rw [ENNReal.ofReal_mul (exp_pos _).le]
          exact mul_le_mul_right hx _)
      _ = ENNReal.ofReal (∫ x, exp (θ * f x) * g (f x) ∂Measure.pi μ) :=
        (ofReal_integral_eq_lintegral_ofReal hProd
          (Eventually.of_forall fun x => mul_nonneg (exp_pos _).le (hg0 _))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (integral_exp_mul_monotone_le (Measure.pi μ) f hf hB g hg hgi hθ.2)
  refine hBound.trans ((mul_le_mul_right hWeight _).trans_eq ?_)
  rw [← ENNReal.ofReal_mul hC]
  congr 1
  unfold mgf
  ring

end IsotropicVariance.Infra.Concentration
