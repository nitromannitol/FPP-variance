/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Concentration.Entropy

/-!
# The product positive-proxy entropy inequality

Tensorization and refresh invariance turn the coordinate inequality into BLM's
modified logarithmic Sobolev bound (Proposition 10, p. 1588).
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
namespace IsotropicVariance.Infra.Concentration
open IsotropicVariance.Infra.Entropy

/-- Measurability of each integrated positive refresh difference. -/
theorem measurable_positive_refresh {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (Fin n → A) → ℝ} (hf : Measurable f) (i : Fin n) :
    Measurable fun x => ∫⁻ y, ENNReal.ofReal (max (f x - f (Function.update x i y)) 0 ^ 2) ∂μ i := by
  have hm : Measurable fun p : (Fin n → A) × A =>
      ENNReal.ofReal (max (f p.1 - f (Function.update p.1 i p.2)) 0 ^ 2) := by
    exact ENNReal.measurable_ofReal.comp
      ((((hf.comp measurable_fst).sub (hf.comp (IsotropicVariance.Infra.Entropy.measurable_update i))).max measurable_const).pow_const 2)
  exact hm.lintegral_prod_right'

/-- The general product entropy bound, before estimating BLM's scalar function
`ψ(u) = u (exp u - 1)`. -/
theorem eentropy_exp_le_lintegral_vPlus {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) (θ C : ℝ) (hC : 0 ≤ C)
    (hInt : Integrable (fun x => exp (θ * f x)) (Measure.pi μ))
    (hψ : ∀ x i y, f (Function.update x i y) ≤ f x →
      (-θ * (f x - f (Function.update x i y))) *
        (exp (-θ * (f x - f (Function.update x i y))) - 1) ≤
        C * (f x - f (Function.update x i y)) ^ 2) :
    eentropy (Measure.pi μ) (fun x => exp (θ * f x)) ≤
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (exp (θ * f x)) * vPlus μ f x ∂Measure.pi μ := by
  let P := Measure.infinitePi μ
  have hInt' : Integrable (fun x => exp (θ * f x)) P := by
    simpa only [P, Measure.infinitePi_eq_pi] using hInt
  let F := fun i x => ENNReal.ofReal (exp (θ * f x)) *
    ∫⁻ y, ENNReal.ofReal (max (f x - f (Function.update x i y)) 0 ^ 2) ∂μ i
  have hF (i : Fin n) : Measurable (F i) :=
    (ENNReal.measurable_ofReal.comp (hf.const_mul θ).exp).mul (measurable_positive_refresh μ hf i)
  have hCoord (i : Fin n) :
      (∫⁻ x, coordEntropy μ i (fun x => exp (θ * f x)) x ∂P) ≤
        ENNReal.ofReal C * ∫⁻ x, F i x ∂P := by
    have hx : ∀ᵐ x ∂P, coordEntropy μ i (fun x => exp (θ * f x)) x ≤
        ENNReal.ofReal C * ∫⁻ y, F i (Function.update x i y) ∂μ i := by
      filter_upwards [ae_integrable_update i hInt'] with x hxi
      have hh := eentropy_exp_le_positive_proxy (μ i) (fun y => f (Function.update x i y))
        (hf.comp ((IsotropicVariance.Infra.Entropy.measurable_update i).comp measurable_prodMk_left)) θ C hC hxi
        (fun a b hab => by simpa only [Function.update_idem] using hψ (Function.update x i a) i b (by simpa only [Function.update_idem] using hab))
      simpa only [coordEntropy, F, Function.update_idem] using hh
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal C * ∫⁻ y, F i (Function.update x i y) ∂μ i ∂P :=
        lintegral_mono_ae hx
      _ = ENNReal.ofReal C * ∫⁻ x, ∫⁻ y, F i (Function.update x i y) ∂μ i ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = _ := by
        rw [lintegral_lintegral_glue (EfronStein.measurePreserving_update_infinitePi μ i)
          (hF i).aemeasurable]
  have ht := eentropy_le_tsum_coordEntropy (fun x => (exp_pos (θ * f x)).le)
    (hf.const_mul θ).exp hInt'
  rw [tsum_fintype] at ht
  have hSum := ht.trans (Finset.sum_le_sum fun i _ => hCoord i)
  have hEq : (∑ i, ENNReal.ofReal C * ∫⁻ x, F i x ∂P) =
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (exp (θ * f x)) * vPlus μ f x ∂P := by
    rw [← Finset.mul_sum, ← lintegral_finsetSum _ (fun i _ => hF i)]
    congr 1
    apply lintegral_congr
    intro x
    simp only [F, vPlus, Finset.mul_sum]
  simpa only [P, Measure.infinitePi_eq_pi] using hSum.trans_eq hEq

/-- On the negative half-line BLM's scalar function is bounded by the square. -/
theorem mul_exp_sub_one_le_sq {u : ℝ} (hu : u ≤ 0) : u * (exp u - 1) ≤ u ^ 2 := by
  have h : u ≤ exp u - 1 := by linarith only [Real.add_one_le_exp u]
  simpa only [pow_two] using mul_le_mul_of_nonpos_left h hu

/-- BLM's positive-parameter modified logarithmic Sobolev inequality. -/
theorem eentropy_exp_le_vPlus {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) {θ : ℝ} (hθ : 0 ≤ θ)
    (hInt : Integrable (fun x => exp (θ * f x)) (Measure.pi μ)) :
    eentropy (Measure.pi μ) (fun x => exp (θ * f x)) ≤
      ENNReal.ofReal (θ ^ 2) *
        ∫⁻ x, ENNReal.ofReal (exp (θ * f x)) * vPlus μ f x ∂Measure.pi μ := by
  apply eentropy_exp_le_lintegral_vPlus μ f hf θ (θ ^ 2) (sq_nonneg θ) hInt
  intro x i y hy
  calc
    _ ≤ (-θ * (f x - f (Function.update x i y))) ^ 2 :=
      mul_exp_sub_one_le_sq (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) (sub_nonneg.mpr hy))
    _ = _ := by ring

/-- A bounded positive variance proxy gives the quadratic entropy estimate needed
by the Herbst argument, whenever the exponential is integrable. -/
theorem eentropy_exp_le_of_vPlus_le {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) {c θ : ℝ} (hc : 0 ≤ c) (hθ : 0 ≤ θ)
    (hV : ∀ᵐ x ∂Measure.pi μ, vPlus μ f x ≤ ENNReal.ofReal c)
    (hInt : Integrable (fun x => exp (θ * f x)) (Measure.pi μ)) :
    eentropy (Measure.pi μ) (fun x => exp (θ * f x)) ≤
      ENNReal.ofReal (c * θ ^ 2 * ∫ x, exp (θ * f x) ∂Measure.pi μ) := by
  have hBound : (∫⁻ x, ENNReal.ofReal (exp (θ * f x)) * vPlus μ f x ∂Measure.pi μ) ≤
      ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (exp (θ * f x)) ∂Measure.pi μ := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal c * ENNReal.ofReal (exp (θ * f x)) ∂Measure.pi μ :=
        lintegral_mono_ae (hV.mono fun x hx => by simpa only [mul_comm] using mul_le_mul_right hx (ENNReal.ofReal (exp (θ * f x))))
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  refine (eentropy_exp_le_vPlus μ f hf hθ hInt).trans ((mul_le_mul_right hBound _).trans_eq ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall fun x => (exp_pos _).le)]
  rw [ENNReal.ofReal_mul (mul_nonneg hc (sq_nonneg θ)), ENNReal.ofReal_mul hc]
  ring

end IsotropicVariance.Infra.Concentration
