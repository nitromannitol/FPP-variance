/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import CurvatureVariance.Statements.Inputs.IsOs
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.Positivity

/-!
# The stochastic order `O_s`

The definition is [AKM, (0.41)], equivalently [AKM, (A.1), (A.2), p. 455].
All powers in the definition are real powers of a nonnegative real number.
No independence is required for the elementary calculus.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace CurvatureVariance.Infra.Os

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Measurability of the exponential integrand. -/
theorem aemeasurable_exp_pos_rpow {X : Ω → ℝ} (hX : AEMeasurable X P) (s θ : ℝ) :
    AEMeasurable (fun ω => ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s))) P :=
  (((hX.max aemeasurable_const).div_const θ).pow_const s).exp.ennreal_ofReal

/-- Almost-everywhere modification does not change stochastic order. -/
theorem _root_.CurvatureVariance.IsOs.congr {s θ : ℝ} {X Y : Ω → ℝ} (h : IsOs P s θ X) (hXY : X =ᵐ[P] Y) :
    IsOs P s θ Y := by
  refine ⟨h.1.congr hXY, ?_⟩
  exact (lintegral_congr_ae (hXY.fun_comp fun x => ENNReal.ofReal (Real.exp ((max x 0 / θ) ^ s)))).symm.le.trans h.2

/-- Monotonicity in the random variable, with only a.e. comparison. -/
theorem _root_.CurvatureVariance.IsOs.mono {s θ : ℝ} {X Y : Ω → ℝ} (h : IsOs P s θ X)
    (hs : 0 ≤ s) (hθ : 0 < θ) (hY : AEMeasurable Y P) (hYX : Y ≤ᵐ[P] X) :
    IsOs P s θ Y := by
  refine ⟨hY, (lintegral_mono_ae ?_).trans h.2⟩
  filter_upwards [hYX] with ω hω
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact Real.rpow_le_rpow (div_nonneg (le_max_right _ _) hθ.le)
    (div_le_div_of_nonneg_right (max_le_max hω le_rfl) hθ.le) hs

/-- Increasing the scale weakens an `O_s` bound. -/
theorem _root_.CurvatureVariance.IsOs.mono_scale {s θ η : ℝ} {X : Ω → ℝ} (h : IsOs P s θ X)
    (hs : 0 ≤ s) (hθ : 0 < θ) (hθη : θ ≤ η) : IsOs P s η X := by
  refine ⟨h.1, (lintegral_mono fun ω => ?_).trans h.2⟩
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact Real.rpow_le_rpow (div_nonneg (le_max_right _ _) (hθ.le.trans hθη))
    (div_le_div_of_nonneg_left (le_max_right _ _) hθ hθη) hs

/-- Exact positive homogeneity of the scale, AKM p. 455. -/
theorem isOs_mul_iff {s θ a : ℝ} {X : Ω → ℝ} (ha : 0 < a) :
    IsOs P s (a * θ) (fun ω => a * X ω) ↔ IsOs P s θ X := by
  have hMeas : AEMeasurable (fun ω => a * X ω) P ↔ AEMeasurable X P := by
    constructor
    · intro h
      have hh := h.const_mul a⁻¹
      simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using hh
    · exact fun h => h.const_mul a
  have heq (ω : Ω) : max (a * X ω) 0 / (a * θ) = max (X ω) 0 / θ := by
    rw [show max (a * X ω) 0 = a * max (X ω) 0 by
      rw [mul_max_of_nonneg _ _ ha.le, mul_zero]]
    exact mul_div_mul_left _ _ ha.ne'
  simp only [IsOs, hMeas, heq]

/-- The normalized formulation of `O_s`, explicitly recorded in AKM p. 455. -/
theorem isOs_div_iff {s θ : ℝ} {X : Ω → ℝ} (hθ : 0 < θ) :
    IsOs P s 1 (fun ω => X ω / θ) ↔ IsOs P s θ X := by
  have hh := isOs_mul_iff (P := P) (s := s) (θ := θ) (X := X) (inv_pos.mpr hθ)
  simpa only [inv_mul_cancel₀ hθ.ne', div_eq_mul_inv, mul_comm] using hh

/-- The zero variable has every positive-exponent stochastic bound on a probability space. -/
theorem isOs_zero [IsProbabilityMeasure P] {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    IsOs P s θ (fun _ => 0) := by
  refine ⟨aemeasurable_const, ?_⟩
  simp only [max_self, zero_div, Real.zero_rpow hs.ne', Real.exp_zero,
    ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]
  norm_num

/-- The forward tail estimate of AKM Lemma A.1, with its exact factor two. -/
theorem isOs_measure_ge_le [IsProbabilityMeasure P] {s θ : ℝ} {X : Ω → ℝ}
    (h : IsOs P s θ X) (hs : 0 < s) (hθ : 0 < θ) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | θ * t ≤ X ω} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ s))) := by
  let f := fun ω => ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s))
  have hf : AEMeasurable f P := aemeasurable_exp_pos_rpow h.1 s θ
  have he : ENNReal.ofReal (Real.exp (t ^ s)) ≠ 0 := by positivity
  have hsub : {ω | θ * t ≤ X ω} ⊆ {ω | ENNReal.ofReal (Real.exp (t ^ s)) ≤ f ω} := by
    intro ω hω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply Real.rpow_le_rpow ht _ hs.le
    exact (le_div_iff₀ hθ).mpr ((mul_comm t θ).trans_le hω |>.trans (le_max_left _ _))
  calc
    _ ≤ P {ω | ENNReal.ofReal (Real.exp (t ^ s)) ≤ f ω} := measure_mono hsub
    _ ≤ (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp (t ^ s)) := meas_ge_le_lintegral_div hf he ENNReal.ofReal_ne_top
    _ ≤ 2 / ENNReal.ofReal (Real.exp (t ^ s)) := by gcongr; exact h.2
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
      congr 1
      rw [div_eq_mul_inv, Real.exp_neg]

end CurvatureVariance.Infra.Os
