/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Concentration.ProductEntropy
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! # A coupled summed-energy bound controls every weighted product proxy

Only the pair marginals of the coupling matter. This permits a common old
physical field to be used for all replacements before taking expectations.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.Concentration IsotropicVariance.Infra.Entropy

/-- Transfer a pathwise summed-energy bound to a weighted positive proxy by
identifying each coupled pair with its product-coordinate refresh law. -/
theorem lintegral_weight_mul_vPlus_le_of_coupling {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f)
    (W : (Fin n → A) → ℝ≥0∞) (hW : Measurable W)
    (Q : Measure ((Fin n → A) × (Fin n → Fin n → A)))
    (hOld : Q.map Prod.fst = Measure.pi μ)
    (hPair : ∀ i, Q.map (fun p => (p.1, p.2 i)) =
      ((Measure.pi μ).prod (μ i)).map (fun p => (p.1, Function.update p.1 i p.2)))
    {C : ℝ} (hEnergy : ∀ᵐ p ∂Q,
      ∑ i : Fin n, max (f p.1 - f (p.2 i)) 0 ^ 2 ≤ C) :
    (∫⁻ x, W x * vPlus μ f x ∂Measure.pi μ) ≤
      ENNReal.ofReal C * ∫⁻ x, W x ∂Measure.pi μ := by
  let H : (Fin n → A) × (Fin n → A) → ℝ≥0∞ :=
    fun p => W p.1 * ENNReal.ofReal (max (f p.1 - f p.2) 0 ^ 2)
  have hH : Measurable H := (hW.comp measurable_fst).mul
    ((((hf.comp measurable_fst).sub (hf.comp measurable_snd)).max measurable_const).pow_const 2).ennreal_ofReal
  have hTerm (i : Fin n) :
      (∫⁻ x, W x * ∫⁻ y, ENNReal.ofReal (max (f x - f (Function.update x i y)) 0 ^ 2) ∂μ i ∂Measure.pi μ) =
      ∫⁻ p, H (p.1, p.2 i) ∂Q := by
    have hD : Measurable (fun p : (Fin n → A) × A => (p.1, Function.update p.1 i p.2)) :=
      measurable_fst.prodMk (IsotropicVariance.Infra.Entropy.measurable_update i)
    have hg : Measurable (fun p : (Fin n → A) × (Fin n → Fin n → A) => (p.1, p.2 i)) :=
      measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
    calc
      _ = ∫⁻ p : (Fin n → A) × A, H (p.1, Function.update p.1 i p.2) ∂(Measure.pi μ).prod (μ i) := by
        have hHD : Measurable (fun p : (Fin n → A) × A =>
            H (p.1, Function.update p.1 i p.2)) := hH.comp hD
        rw [lintegral_prod _ hHD.aemeasurable]
        apply lintegral_congr
        intro x
        have hfx : Measurable (fun y => f (Function.update x i y)) :=
          hf.comp ((IsotropicVariance.Infra.Entropy.measurable_update i).comp measurable_prodMk_left)
        exact (lintegral_const_mul (W x)
          (((measurable_const.sub hfx).max measurable_const).pow_const 2).ennreal_ofReal).symm
      _ = ∫⁻ p, H p ∂((Measure.pi μ).prod (μ i)).map
          (fun p => (p.1, Function.update p.1 i p.2)) := (lintegral_map hH hD).symm
      _ = ∫⁻ p, H p ∂Q.map (fun p => (p.1, p.2 i)) := by rw [hPair i]
      _ = _ := lintegral_map hH hg
  have hMeas (i : Fin n) : Measurable (fun x => W x *
      ∫⁻ y, ENNReal.ofReal (max (f x - f (Function.update x i y)) 0 ^ 2) ∂μ i) :=
    hW.mul (measurable_positive_refresh μ hf i)
  have hMeasQ (i : Fin n) : Measurable (fun p : (Fin n → A) × (Fin n → Fin n → A) =>
      H (p.1, p.2 i)) := hH.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  calc
    _ = ∑ i : Fin n, ∫⁻ x, W x *
        ∫⁻ y, ENNReal.ofReal (max (f x - f (Function.update x i y)) 0 ^ 2) ∂μ i ∂Measure.pi μ := by
      simp only [Cited.vPlus, Finset.mul_sum]
      exact lintegral_finsetSum _ (fun i _ => hMeas i)
    _ = ∑ i : Fin n, ∫⁻ p, H (p.1, p.2 i) ∂Q := Finset.sum_congr rfl fun i _ => hTerm i
    _ = ∫⁻ p, ∑ i : Fin n, H (p.1, p.2 i) ∂Q :=
      (lintegral_finsetSum _ (fun i _ => hMeasQ i)).symm
    _ ≤ ∫⁻ p, ENNReal.ofReal C * W p.1 ∂Q := by
      apply lintegral_mono_ae
      filter_upwards [hEnergy] with p hp
      have hSum : (∑ i : Fin n, ENNReal.ofReal (max (f p.1 - f (p.2 i)) 0 ^ 2)) ≤ ENNReal.ofReal C := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hp
      simpa only [H, ← Finset.mul_sum, mul_comm] using mul_le_mul_right hSum (W p.1)
    _ = ENNReal.ofReal C * ∫⁻ p, W p.1 ∂Q := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      have hh := lintegral_map hW measurable_fst (μ := Q)
      rw [hOld] at hh
      rw [hh]

/-- Testing the weighted estimate on measurable indicators gives the required
almost-sure pointwise product proxy bound. -/
theorem ae_vPlus_le_of_coupling {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f)
    (Q : Measure ((Fin n → A) × (Fin n → Fin n → A)))
    (hOld : Q.map Prod.fst = Measure.pi μ)
    (hPair : ∀ i, Q.map (fun p => (p.1, p.2 i)) =
      ((Measure.pi μ).prod (μ i)).map (fun p => (p.1, Function.update p.1 i p.2)))
    {C : ℝ} (hEnergy : ∀ᵐ p ∂Q,
      ∑ i : Fin n, max (f p.1 - f (p.2 i)) 0 ^ 2 ≤ C) :
    ∀ᵐ x ∂Measure.pi μ, vPlus μ f x ≤ ENNReal.ofReal C := by
  have hV : Measurable (vPlus μ f) :=
    Finset.measurable_sum _ fun i _ => measurable_positive_refresh μ hf i
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hV
  intro S hS _hSfinite
  have hh := lintegral_weight_mul_vPlus_le_of_coupling μ f hf
    (S.indicator (fun _ => 1)) (measurable_const.indicator hS) Q hOld hPair hEnergy
  have hEq : (fun x => S.indicator (fun _ => (1 : ℝ≥0∞)) x * vPlus μ f x) =
      S.indicator (vPlus μ f) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx, one_mul]
    · simp only [indicator_of_notMem hx, zero_mul]
  rw [hEq, lintegral_indicator hS, lintegral_indicator hS] at hh
  simpa only [lintegral_const, Measure.restrict_apply_univ, one_mul] using hh

/-- Dividing the coded observable divides its coupled energy bound by the
square of the normalization scale. -/
theorem ae_vPlus_div_le_of_coupling {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f)
    (Q : Measure ((Fin n → A) × (Fin n → Fin n → A)))
    (hOld : Q.map Prod.fst = Measure.pi μ)
    (hPair : ∀ i, Q.map (fun p => (p.1, p.2 i)) =
      ((Measure.pi μ).prod (μ i)).map (fun p => (p.1, Function.update p.1 i p.2)))
    {C r : ℝ} (hr : 0 < r) (hEnergy : ∀ᵐ p ∂Q,
      ∑ i : Fin n, max (f p.1 - f (p.2 i)) 0 ^ 2 ≤ C) :
    ∀ᵐ x ∂Measure.pi μ, vPlus μ (fun x => f x / r) x ≤ ENNReal.ofReal (C / r ^ 2) := by
  apply ae_vPlus_le_of_coupling μ (fun x => f x / r) (hf.div_const r) Q hOld hPair
  have hScale (x y : Fin n → A) :
      max (f x / r - f y / r) 0 ^ 2 = max (f x - f y) 0 ^ 2 / r ^ 2 := by
    have hmax : max ((f x - f y) / r) 0 = max (f x - f y) 0 / r := by
      simpa only [zero_div] using max_div_div_right hr.le (f x - f y) 0
    rw [← sub_div, hmax, div_pow]
  filter_upwards [hEnergy] with p hp
  simp_rw [hScale, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right hp (sq_nonneg r)

end IsotropicVariance.Paper.Proofs.Classical
