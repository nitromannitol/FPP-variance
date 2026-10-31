/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
public import IsotropicVariance.Infra.Os.Power
public import IsotropicVariance.Paper.Proofs.Induction.Tools
import IsotropicVariance.Paper.Proofs.Profiles.OsTools

/-!
# Exponential moments for Section `sec:completion`

* `isOs_one_of_isOs_two`: `O_2(θ)` gives `O_1(λ)` for `λ ≥ 2θ`.
* `isOs_one_add`: the sum rule for `O_1`.
* `lintegral_exp_abs_sub_integral_le`: the exponential moment of `|Y − EY|` from a bound of the
  form of equation `eq:parent`.
* `isOs_abs_sub_integral_of_evariance_le`: `O_1(θ/4)` for `|Y − EY|` from that moment and a
  small variance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Induction

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `O_2(θ)` gives `O_1(λ)` for `λ ≥ 2θ`: `y/λ ≤ (y/θ)²/2 + 1/8`, Jensen, and
`e^{1/8} √2 ≤ 2`. -/
theorem isOs_one_of_isOs_two [IsProbabilityMeasure P] {θ l : ℝ} {Y : Ω → ℝ} (hθ : 0 < θ)
    (hθl : 2 * θ ≤ l) (h : Cited.IsOs P 2 θ Y) : Cited.IsOs P 1 l Y := by
  have hl : 0 < l := by linarith
  refine ⟨h.1, ?_⟩
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal
      (Real.exp ((max (Y ω) 0 / θ) ^ (2 : ℝ)))) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.measurable_exp.comp_aemeasurable
        ((((h.1.max aemeasurable_const).div_const θ)).pow_const _))
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (Y ω) 0 / l) ^ (1 : ℝ))) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (1 / 8)) *
          (ENNReal.ofReal (Real.exp ((max (Y ω) 0 / θ) ^ (2 : ℝ)))) ^ (1 / 2 : ℝ) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp, Real.rpow_one, Real.rpow_two]
        have hy : 0 ≤ max (Y ω) 0 := le_max_right _ _
        have h1 : max (Y ω) 0 / l ≤ max (Y ω) 0 / θ / 2 :=
          calc max (Y ω) 0 / l ≤ max (Y ω) 0 / (2 * θ) :=
                div_le_div_of_nonneg_left hy (by positivity) hθl
            _ = max (Y ω) 0 / θ / 2 := by field_simp
        have h2 := sq_nonneg (max (Y ω) 0 / θ - 1 / 2)
        nlinarith
    _ = ENNReal.ofReal (Real.exp (1 / 8)) *
          ∫⁻ ω, (ENNReal.ofReal (Real.exp ((max (Y ω) 0 / θ) ^ (2 : ℝ)))) ^ (1 / 2 : ℝ) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (1 / 8)) * (∫⁻ ω,
          ENNReal.ofReal (Real.exp ((max (Y ω) 0 / θ) ^ (2 : ℝ))) ∂P) ^ (1 / 2 : ℝ) := by
        gcongr
        exact Infra.Os.lintegral_rpow_le hmeas (by norm_num) (by norm_num)
    _ ≤ ENNReal.ofReal (Real.exp (1 / 8)) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
        gcongr
        exact h.2
    _ ≤ 2 := by
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [h2, ENNReal.ofReal_rpow_of_pos (by norm_num), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
        calc Real.exp (1 / 8 + Real.log 2 * (1 / 2)) ≤ Real.exp (Real.log 2) :=
              Real.exp_le_exp.2 (by linarith [Real.log_two_gt_d9])
          _ = 2 := Real.exp_log (by norm_num)

/-- The sum rule for `O_1` (equation `eq:sum`). -/
theorem isOs_one_add [IsProbabilityMeasure P] {θ₁ θ₂ : ℝ} {X₁ X₂ : Ω → ℝ} (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (h₁ : Cited.IsOs P 1 θ₁ X₁) (h₂ : Cited.IsOs P 1 θ₂ X₂) :
    Cited.IsOs P 1 (θ₁ + θ₂) (fun ω => X₁ ω + X₂ ω) :=
  Profiles.isOs_add h₁ h₂ hθ₁ hθ₂

/-- **The exponential moment from equation `eq:parent`** (proof of Proposition `prop:induction`):
if `|Y − c| − Cθ ≤ O_1(θ/100)`, then
`E exp(8|Y − EY|/θ) ≤ 2 e^{16C + 1}`. -/
theorem lintegral_exp_abs_sub_integral_le [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : Integrable Y P) {c C θ : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    (h : Cited.IsOs P 1 (θ / 100) (fun ω => |Y ω - c| - C * θ)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (8 * |Y ω - ∫ ω', Y ω' ∂P| / θ)) ∂P ≤
      ENNReal.ofReal (2 * Real.exp (16 * C + 1)) := by
  set W : Ω → ℝ := fun ω => max (|Y ω - c| - C * θ) 0 with hW
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => le_max_right _ _
  have hWle : ∀ ω, |Y ω - c| ≤ C * θ + W ω := fun ω => by
    have := le_max_left (|Y ω - c| - C * θ) 0
    simp only [W]; linarith
  have hWle' : ∀ ω, W ω ≤ |Y ω - c| := fun ω => by
    refine max_le (by linarith [mul_nonneg hC hθ.le]) (abs_nonneg _)
  have hWm : AEMeasurable W P := h.1.max aemeasurable_const
  have hYc : Integrable (fun ω => |Y ω - c|) P := (hY.sub (integrable_const c)).abs
  have hWi : Integrable W P :=
    hYc.mono' hWm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hW0 ω)]; exact hWle' ω)
  have hθ100 : 0 < θ / 100 := by positivity
  have hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (W ω / (θ / 100))) ∂P ≤ 2 := by
    simpa only [Real.rpow_one, W] using h.2
  -- the mean of `W`
  have hEW : ∫ ω, W ω ∂P ≤ θ / 50 := by
    have h1 : ∫⁻ ω, ENNReal.ofReal (W ω) ∂P ≤ ENNReal.ofReal (θ / 50) := by
      calc ∫⁻ ω, ENNReal.ofReal (W ω) ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal (θ / 100) *
              ENNReal.ofReal (Real.exp (W ω / (θ / 100))) ∂P := by
            refine lintegral_mono fun ω => ?_
            rw [← ENNReal.ofReal_mul hθ100.le]
            refine ENNReal.ofReal_le_ofReal ?_
            have := Real.add_one_le_exp (W ω / (θ / 100))
            have h3 : W ω / (θ / 100) ≥ 0 := div_nonneg (hW0 ω) hθ100.le
            calc W ω = θ / 100 * (W ω / (θ / 100)) := by field_simp
              _ ≤ θ / 100 * Real.exp (W ω / (θ / 100)) :=
                  mul_le_mul_of_nonneg_left (by linarith) hθ100.le
        _ = ENNReal.ofReal (θ / 100) *
              ∫⁻ ω, ENNReal.ofReal (Real.exp (W ω / (θ / 100))) ∂P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (θ / 100) * 2 := by gcongr
        _ = ENNReal.ofReal (θ / 50) := by
            rw [show θ / 50 = θ / 100 * 2 by ring,
              ENNReal.ofReal_mul hθ100.le, ENNReal.ofReal_ofNat]
    rw [← ofReal_integral_eq_lintegral_ofReal hWi (Filter.Eventually.of_forall hW0)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have hmean : |(∫ ω', Y ω' ∂P) - c| ≤ C * θ + θ / 50 := by
    have h1 : |∫ ω, (Y ω - c) ∂P| ≤ ∫ ω, |Y ω - c| ∂P := abs_integral_le_integral_abs
    rw [integral_sub hY (integrable_const c)] at h1
    simp only [integral_const, probReal_univ, one_smul] at h1
    have h2 : ∫ ω, |Y ω - c| ∂P ≤ ∫ ω, (C * θ + W ω) ∂P :=
      integral_mono hYc ((integrable_const _).add hWi) hWle
    rw [integral_add (integrable_const _) hWi] at h2
    simp only [integral_const, probReal_univ, one_smul] at h2
    linarith
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (8 * |Y ω - ∫ ω', Y ω' ∂P| / θ)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (16 * C + 1)) *
          ENNReal.ofReal (Real.exp (W ω / (θ / 100))) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.exp_add, Real.exp_le_exp]
        have h1 : |Y ω - ∫ ω', Y ω' ∂P| ≤ |Y ω - c| + |(∫ ω', Y ω' ∂P) - c| := by
          calc |Y ω - ∫ ω', Y ω' ∂P| = |(Y ω - c) - ((∫ ω', Y ω' ∂P) - c)| := by ring_nf
            _ ≤ _ := abs_sub _ _
        have h2 : 8 * |Y ω - ∫ ω', Y ω' ∂P| ≤ 8 * (2 * C * θ + θ / 50 + W ω) := by
          nlinarith [hWle ω]
        have h3 : 8 * |Y ω - ∫ ω', Y ω' ∂P| / θ ≤ 8 * (2 * C * θ + θ / 50 + W ω) / θ :=
          div_le_div_of_nonneg_right h2 hθ.le
        have h4 : 8 * (2 * C * θ + θ / 50 + W ω) / θ = 16 * C + 8 / 50 + 8 * (W ω / θ) := by
          field_simp
          ring
        have h5 : W ω / (θ / 100) = 100 * (W ω / θ) := by field_simp
        have h6 : 0 ≤ W ω / θ := div_nonneg (hW0 ω) hθ.le
        rw [h5]
        linarith
    _ = ENNReal.ofReal (Real.exp (16 * C + 1)) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (W ω / (θ / 100))) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (16 * C + 1)) * 2 := by gcongr
    _ = ENNReal.ofReal (2 * Real.exp (16 * C + 1)) := by
        rw [mul_comm 2, ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_ofNat]

/-- **From a small variance to `O_1(θ/4)`** (proof of Proposition `prop:induction`):
`eˣ − 1 ≤ x eˣ` and Cauchy–Schwarz give
`E exp(4|Y − EY|/θ) ≤ 1 + (16 Var(Y)/θ²)^{1/2} (E exp(8|Y − EY|/θ))^{1/2}`. -/
theorem isOs_abs_sub_integral_of_evariance_le [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) {θ v B : ℝ} (hθ : 0 < θ) (hv : 0 ≤ v)
    (hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (8 * |Y ω - ∫ ω', Y ω' ∂P| / θ)) ∂P ≤
      ENNReal.ofReal B)
    (hvar : evariance Y P ≤ ENNReal.ofReal (v * θ ^ 2)) (hvB : 16 * v * B ≤ 1) :
    Cited.IsOs P 1 (θ / 4) (fun ω => |Y ω - ∫ ω', Y ω' ∂P|) := by
  set m : ℝ := ∫ ω', Y ω' ∂P with hm
  set x : Ω → ℝ := fun ω => 4 * |Y ω - m| / θ with hx
  have hx0 : ∀ ω, 0 ≤ x ω := fun ω => by positivity
  have hmeas : AEMeasurable (fun ω => |Y ω - m|) P :=
    (continuous_abs.measurable.comp_aemeasurable
      (hY.aestronglyMeasurable.aemeasurable.sub_const m))
  have hxm : AEMeasurable x P := (hmeas.const_mul 4).div_const θ
  refine ⟨hmeas, ?_⟩
  have hform : ∀ ω, max |Y ω - m| 0 / (θ / 4) = x ω := fun ω => by
    rw [max_eq_left (abs_nonneg _)]; simp only [x]; field_simp
  simp only [Real.rpow_one, hform]
  -- pointwise
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (x ω)) ≤
      1 + ENNReal.ofReal (x ω) * ENNReal.ofReal (Real.exp (x ω)) := fun ω => by
    have h1 := Real.add_one_le_exp (-x ω)
    rw [Real.exp_neg] at h1
    have h2 := Real.exp_pos (x ω)
    have h3 : Real.exp (x ω) ≤ 1 + x ω * Real.exp (x ω) := by
      have := mul_le_mul_of_nonneg_left h1 h2.le
      rw [mul_add, mul_inv_cancel₀ h2.ne'] at this
      linarith
    calc ENNReal.ofReal (Real.exp (x ω))
        ≤ ENNReal.ofReal (1 + x ω * Real.exp (x ω)) := ENNReal.ofReal_le_ofReal h3
      _ = 1 + ENNReal.ofReal (x ω) * ENNReal.ofReal (Real.exp (x ω)) := by
        rw [ENNReal.ofReal_add zero_le_one (mul_nonneg (hx0 ω) h2.le),
          ENNReal.ofReal_mul (hx0 ω), ENNReal.ofReal_one]
  have hfm : AEMeasurable (fun ω => ENNReal.ofReal (x ω)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable hxm
  have hgm : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (x ω))) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (Real.measurable_exp.comp_aemeasurable hxm)
  have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hfm hgm
  -- the two factors
  have hA : ∫⁻ ω, ENNReal.ofReal (x ω) ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal (16 * v) := by
    have e1 : ∀ ω, ENNReal.ofReal (x ω) ^ (2 : ℝ) =
        ENNReal.ofReal (16 / θ ^ 2) * ENNReal.ofReal ((Y ω - m) ^ 2) := fun ω => by
      rw [ENNReal.ofReal_rpow_of_nonneg (hx0 ω) (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [x, Real.rpow_two]
      rw [div_pow, mul_pow, sq_abs]
      field_simp
      ring
    simp_rw [e1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← evariance_eq_lintegral_ofReal]
    calc ENNReal.ofReal (16 / θ ^ 2) * evariance Y P
        ≤ ENNReal.ofReal (16 / θ ^ 2) * ENNReal.ofReal (v * θ ^ 2) := by gcongr
      _ = ENNReal.ofReal (16 * v) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
  have hG : ∫⁻ ω, ENNReal.ofReal (Real.exp (x ω)) ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal B := by
    refine le_trans (le_of_eq ?_) hexp
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2
    simp only [x]; ring
  have hone : (∫⁻ ω, ENNReal.ofReal (x ω) * ENNReal.ofReal (Real.exp (x ω)) ∂P) ≤ 1 := by
    refine hHold.trans ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc (_ * _) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (16 * v) * ENNReal.ofReal B) ^ (1 / 2 : ℝ) := by
          gcongr
      _ ≤ (ENNReal.ofReal 1) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          gcongr
      _ = 1 := by simp
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (x ω)) ∂P
      ≤ ∫⁻ ω, (1 + ENNReal.ofReal (x ω) * ENNReal.ofReal (Real.exp (x ω))) ∂P :=
        lintegral_mono hpt
    _ = 1 + ∫⁻ ω, ENNReal.ofReal (x ω) * ENNReal.ofReal (Real.exp (x ω)) ∂P := by
        rw [lintegral_add_left' aemeasurable_const]
        simp
    _ ≤ 1 + 1 := by gcongr
    _ = 2 := by norm_num

end IsotropicVariance.Paper.Proofs.Induction
