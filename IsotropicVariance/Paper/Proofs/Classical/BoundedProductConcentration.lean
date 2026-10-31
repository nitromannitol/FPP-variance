/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.ProductConcentrationAE

/-! # Concentration after normalizing a bounded coded passage time -/

@[expose] public section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.Concentration IsotropicVariance.Infra

/-- Bounded observables with almost-sure bounded refresh differences satisfy
the normalized two-sided BLM estimate from the bound `V₊(-f / r) ≤ c`, the sum of the squared
increases of `f / r`. -/
theorem isOs_abs_centered_of_neg_proxy {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) {L r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hBounds : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (hRange : L / r ≤ (exp 1 - 1) * c)
    (hV : ∀ᵐ x ∂Measure.pi μ, vPlus μ (fun x => -f x / r) x ≤ ENNReal.ofReal c)
    (hDiff : ∀ i, ∀ᵐ p : (Fin n → A) × A ∂(Measure.pi μ).prod (μ i),
      |f p.1 - f (Function.update p.1 i p.2)| ≤ r) :
    Cited.IsOs (Measure.pi μ) 2
      (r * (2 * ((2 : ℝ) ^ (1 / 2 : ℝ) * (4 * sqrt ((exp 1 - 1) * c)))))
      (fun x => |f x - ∫ z, f z ∂Measure.pi μ|) := by
  let P := Measure.pi μ
  let g := fun x => -f x / r
  have hg : Measurable g := hf.neg.div_const r
  have hgBounds (x : Fin n → A) : -(L / r) ≤ g x ∧ g x ≤ 0 := by
    constructor
    · dsimp only [g]
      rw [neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_right (hBounds x).2 hr.le)
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hBounds x).1) hr.le
  have hgAbs (x : Fin n → A) : |g x| ≤ L / r := by
    rw [abs_of_nonpos (hgBounds x).2]
    linarith only [(hgBounds x).1]
  have hgi : Integrable g P := by
    apply Integrable.mono' (integrable_const (L / r)) hg.aestronglyMeasurable
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hgAbs x
  have hMean0 : (∫ x, g x ∂P) ≤ 0 := integral_nonpos fun x => (hgBounds x).2
  have hMeanL : -(L / r) ≤ ∫ x, g x ∂P := by
    have hh := integral_mono (integrable_const (-(L / r))) hgi (fun x => (hgBounds x).1)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  have hCentered (x : Fin n → A) : |g x - ∫ z, g z ∂P| ≤ (exp 1 - 1) * c := by
    apply le_trans _ hRange
    rw [abs_le]
    constructor <;> linarith only [(hgBounds x).1, (hgBounds x).2, hMean0, hMeanL]
  have hD (i : Fin n) : ∀ᵐ p : (Fin n → A) × A ∂P.prod (μ i),
      |g p.1 - g (Function.update p.1 i p.2)| ≤ 1 := by
    filter_upwards [hDiff i] with p hp
    dsimp only [g]
    rw [← sub_div, abs_div, abs_of_pos hr, neg_sub_neg, abs_sub_comm]
    exact (div_le_one hr).mpr hp
  have hOs := isOs_abs_centered_of_ae_bounded_positive_proxy μ g hg hgi hc hV hD hCentered
  have hScaled := (Os.isOs_mul_iff (P := P) (s := 2) hr).mpr hOs
  have hEq : (fun x => r * |g x - ∫ z, g z ∂P|) =
      (fun x => |f x - ∫ z, f z ∂P|) := by
    funext x
    have hMean : (∫ z, g z ∂P) = -(∫ z, f z ∂P) / r := by
      dsimp only [g]
      rw [integral_div, integral_neg]
    rw [hMean]
    dsimp only [g]
    rw [← sub_div, abs_div, abs_of_pos hr, neg_sub_neg, abs_sub_comm]
    field_simp
  rw [hEq] at hScaled
  exact hScaled

end IsotropicVariance.Paper.Proofs.Classical
