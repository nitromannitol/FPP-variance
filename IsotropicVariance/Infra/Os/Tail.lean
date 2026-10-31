/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Tail probabilities and stochastic order

AKM Lemma A.1 and Remark A.2, p. 456. The converse in A.1 has
unit tail prefactor and scale `2^(1/s) θ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace IsotropicVariance.Infra.Os

open Cited

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Integrating a unit exponential tail gives the exact half-exponential moment. -/
theorem lintegral_exp_half_le_two [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZ : AEMeasurable Z P) (hZ0 : 0 ≤ᵐ[P] Z)
    (hTail : ∀ t : ℝ, 0 < t → P {ω | t ≤ Z ω} ≤ ENNReal.ofReal (Real.exp (-t))) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω / 2)) ∂P) ≤ 2 := by
  let g : ℝ → ℝ := fun t => Real.exp (t / 2) / 2
  have hg : Continuous g := (Real.continuous_exp.comp (continuous_id.div_const 2)).div_const 2
  have hPrimitive (z : ℝ) : (∫ t in 0..z, g t) = Real.exp (z / 2) - 1 := by
    have hd (x : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (g x) x := by
      simpa only [g, mul_one_div, id_eq] using ((hasDerivAt_id x).div_const 2).exp
    simpa only [zero_div, Real.exp_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hg.intervalIntegrable 0 z)
  have hLayer := lintegral_comp_eq_lintegral_meas_le_mul (g := g) P hZ0 hZ
    (fun t _ => hg.intervalIntegrable 0 t) (Filter.Eventually.of_forall fun t => div_nonneg (Real.exp_pos _).le (by norm_num))
  -- Specify the nonnegative kernel separately to keep the layer-cake statement small.
  have hBound : (∫⁻ t in Ioi (0 : ℝ), P {ω | t ≤ Z ω} * ENNReal.ofReal (g t)) ≤ 1 := by
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (g t) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        exact mul_le_mul (hTail t ht) le_rfl zero_le zero_le
      _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp ((-1 / 2 : ℝ) * t)) := by
        apply lintegral_congr
        intro t
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        dsimp only [g]
        rw [← mul_div_assoc, ← Real.exp_add]
        rw [show -t + t / 2 = (-1 / 2 : ℝ) * t by ring]
        ring
      _ = 1 := by
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0)]
          norm_num
        · exact (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0).const_mul _
        · exact Filter.Eventually.of_forall fun t => by positivity
  have hSmall : (∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω / 2) - 1) ∂P) ≤ 1 := by
    simp_rw [hPrimitive] at hLayer
    exact hLayer.trans_le hBound
  calc
    _ = (∫⁻ ω, 1 + ENNReal.ofReal (Real.exp (Z ω / 2) - 1) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [hZ0] with ω hω
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num)
        (sub_nonneg.mpr (Real.one_le_exp (div_nonneg hω (by norm_num))))]
      congr 1
      ring
    _ = 1 + ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω / 2) - 1) ∂P := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 2 := by simpa only [one_add_one_eq_two] using add_le_add_right hSmall 1

/-- The converse in AKM Lemma A.1, with the exact scale `2^(1/s) θ`. This is the proof of
`Cited.isOs_of_measure_ge_le`, which the other modules use. -/
theorem isOs_of_tail [IsProbabilityMeasure P] {s θ : ℝ} {X : Ω → ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (hX : AEMeasurable X P)
    (hTail : ∀ t : ℝ, 0 ≤ t → P {ω | θ * t ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-(t ^ s)))) :
    IsOs P s ((2 : ℝ) ^ (1 / s) * θ) X := by
  let Z := fun ω => (max (X ω) 0 / θ) ^ s
  have hZ : AEMeasurable Z P := ((hX.max aemeasurable_const).div_const θ).pow_const s
  have hBound := lintegral_exp_half_le_two hZ (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (by positivity) _)
    (fun t ht => by
      have hroot : (t ^ (1 / s)) ^ s = t := by rw [← Real.rpow_mul ht.le]; simp only [one_div_mul_cancel hs.ne', Real.rpow_one]
      have htpos := Real.rpow_pos_of_pos ht (1 / s)
      have hsub : {ω | t ≤ Z ω} ⊆ {ω | θ * t ^ (1 / s) ≤ X ω} := by
        intro ω hω
        have hr : t ^ (1 / s) ≤ max (X ω) 0 / θ :=
          (Real.rpow_le_rpow_iff (by positivity) (by positivity) hs).mp (hroot.le.trans hω)
        have hp : θ * t ^ (1 / s) ≤ max (X ω) 0 := by simpa only [mul_comm] using (le_div_iff₀ hθ).mp hr
        rcases le_max_iff.mp hp with h | h
        · exact h
        · exact False.elim ((not_le_of_gt (mul_pos hθ htpos)) h)
      exact (measure_mono hsub).trans (by simpa only [hroot] using hTail (t ^ (1 / s)) htpos.le))
  refine ⟨hX, ?_⟩
  convert hBound using 1
  apply lintegral_congr
  intro ω
  congr 2
  rw [mul_comm ((2 : ℝ) ^ (1 / s)) θ, ← div_div, Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hs.ne', Real.rpow_one]

end IsotropicVariance.Infra.Os
