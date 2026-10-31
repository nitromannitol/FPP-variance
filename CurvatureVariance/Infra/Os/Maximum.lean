/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Os.Power
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Ring

/-! # Maxima of finitely many stochastic bounds

The exponential moment of a maximum is at most the sum of the moments.
Concave-power normalization gives the logarithmic scale, without independence.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
namespace CurvatureVariance.Infra.Os

/-- The maximum of a finite nonempty family of `O_s(θ)` variables has scale
`(log(2m)/log 2)^(1/s) θ`. This precise bound implies the usual
`C_s θ log(2+m)^(1/s)` formulation. -/
theorem isOs_finset_sup' {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s θ : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (T : Finset ι) (hT : T.Nonempty) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ T, IsOs P s θ (X i)) :
    IsOs P s ((Real.log (2 * (T.card : ℝ)) / Real.log 2) ^ (1 / s) * θ)
      (T.sup' hT X) := by
  classical
  have hm : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hr : 1 ≤ Real.log (2 * (T.card : ℝ)) / Real.log 2 := by
    apply (le_div_iff₀ hlog).mpr
    rw [one_mul]
    exact Real.log_le_log (by norm_num) (by linarith only [hm])
  have hM : AEMeasurable (T.sup' hT X) P :=
    Finset.sup'_induction (p := fun f : Ω → ℝ => AEMeasurable f P) hT X (fun _ hf _ hg => hf.sup hg) (fun i hi => (hX i hi).1)
  apply isOs_of_exp_moment_le hs hθ hr hM
  calc
    _ ≤ ∫⁻ ω, ∑ i ∈ T, ENNReal.ofReal (Real.exp ((max (X i ω) 0 / θ) ^ s)) ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      obtain ⟨i, hi, heq⟩ := T.exists_mem_eq_sup' hT (fun i => X i ω)
      have hh : T.sup' hT X ω = X i ω := by rw [Finset.sup'_apply]; exact heq
      rw [hh]
      exact Finset.single_le_sum (f := fun j => ENNReal.ofReal (Real.exp ((max (X j ω) 0 / θ) ^ s))) (fun j _ => zero_le) hi
    _ = ∑ i ∈ T, ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X i ω) 0 / θ) ^ s)) ∂P :=
      lintegral_finsetSum' T fun i hi => aemeasurable_exp_pos_rpow (hX i hi).1 s θ
    _ ≤ ∑ i ∈ T, (2 : ℝ≥0∞) := Finset.sum_le_sum fun i hi => (hX i hi).2
    _ = ENNReal.ofReal (2 * (T.card : ℝ)) := by simp only [Finset.sum_const, nsmul_eq_mul]; rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast, mul_comm]
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat, ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), show Real.log 2 * (Real.log (2 * (T.card : ℝ)) / Real.log 2) = Real.log (2 * (T.card : ℝ)) by field_simp, Real.exp_log (by positivity)]

/-- The conventional maximum bound with constant depending only on `s` and
scale `θ log(2+m)^(1/s)`. The explicit admissible constant is `(2/log 2)^(1/s)`. -/
theorem isOs_finset_sup'_log {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s θ : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (T : Finset ι) (hT : T.Nonempty) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ T, IsOs P s θ (X i)) :
    IsOs P s (((2 : ℝ) / Real.log 2) ^ (1 / s) * θ *
      Real.log (2 + (T.card : ℝ)) ^ (1 / s)) (T.sup' hT X) := by
  have hm : 0 < (T.card : ℝ) := Nat.cast_pos.mpr hT.card_pos
  have hm1 : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogm : Real.log (2 * (T.card : ℝ)) ≤ 2 * Real.log (2 + (T.card : ℝ)) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hm.ne']
    have h₁ := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (le_add_of_nonneg_right hm.le)
    have h₂ := Real.log_le_log hm (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [two_mul] using add_le_add h₁ h₂
  have hRatio : Real.log (2 * (T.card : ℝ)) / Real.log 2 ≤
      (2 / Real.log 2) * Real.log (2 + (T.card : ℝ)) := by
    calc
      _ ≤ (2 * Real.log (2 + (T.card : ℝ))) / Real.log 2 := div_le_div_of_nonneg_right hlogm hlog.le
      _ = _ := by ring
  have hSharp := isOs_finset_sup' hs hθ T hT X hX
  apply hSharp.mono_scale hs.le (mul_pos (Real.rpow_pos_of_pos
    (div_pos (Real.log_pos (by nlinarith only [hm1])) hlog) _) hθ)
  calc
    _ ≤ (((2 / Real.log 2) * Real.log (2 + (T.card : ℝ))) ^ (1 / s)) * θ :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (div_nonneg (Real.log_nonneg (by nlinarith only [hm1])) hlog.le) hRatio (one_div_nonneg.mpr hs.le)) hθ.le
    _ = _ := by rw [Real.mul_rpow (by positivity) (Real.log_nonneg (by linarith only [hm]))]; ring

end CurvatureVariance.Infra.Os
