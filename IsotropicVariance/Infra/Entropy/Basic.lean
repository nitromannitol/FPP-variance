/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Statements.Cited.Entropy
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Entropy of a nonnegative function

For a measure `μ` and a function `g ≥ 0`, the entropy is
`Ent_μ g = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)`, with the convention `0 log 0 = 0` (which is
Lean's `Real.log 0 = 0`). This is `IsotropicVariance.Cited.entropy`.

On a probability space, `Ent_μ g = ∫ ψ_m(g) dμ` with `m = ∫ g dμ` and the nonnegative Bregman
integrand `ψ_m(t) = t log t - t log m - t + m` (`entropyDensity`). Its lower integral
`eentropy μ g ∈ [0, ∞]` is the entropy with the value `∞` when `g log g` is not integrable; it is
the form used for tensorization, where integrability is not known in advance.

## Main results

* `entropy_nonneg`, `entropy_eq_integral_entropyDensity`: `Ent_μ g ≥ 0` and the Bregman form.
* `eentropy_eq_ofReal_entropy`, `integrable_mul_log_of_eentropy_ne_top`: the two entropies agree
  when `g log g` is integrable, and `eentropy μ g < ∞` forces integrability.
* `mul_log_div_le_entropy_sq`: the Falik–Samorodnitsky lower bound
  `E V² log (E V² / (E |V|)²) ≤ Ent_μ (V²)`.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal

namespace IsotropicVariance.Infra.Entropy

variable {α : Type*} [MeasurableSpace α]

/-! ### Elementary inequalities -/

/-- `y log y ≥ y log l + y - l` for `y ≥ 0` and `l > 0`: the inequality `u log u ≥ u - 1`. -/
theorem mul_log_ge (y : ℝ) {l : ℝ} (hy : 0 ≤ y) (hl : 0 < l) :
    y * log l + y - l ≤ y * log y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [hl.le]
  · have h := log_le_sub_one_of_pos (div_pos hl hy)
    rw [log_div hl.ne' hy.ne'] at h
    have h' : y * (log l - log y) ≤ y * (l / y - 1) := mul_le_mul_of_nonneg_left h hy.le
    rw [mul_sub, mul_sub, mul_div_cancel₀ _ hy.ne', mul_one] at h'
    linarith

/-- The Bregman integrand of the entropy: `ψ_m(t) = t log t - t log m - t + m`. -/
noncomputable def entropyDensity (m t : ℝ) : ℝ :=
  t * log t - t * log m - t + m

theorem entropyDensity_nonneg {m t : ℝ} (hm : 0 < m) (ht : 0 ≤ t) : 0 ≤ entropyDensity m t := by
  have := mul_log_ge t ht hm
  unfold entropyDensity
  linarith

@[simp] theorem entropyDensity_zero_right (m : ℝ) : entropyDensity m 0 = m := by
  simp [entropyDensity]

theorem entropyDensity_self (m : ℝ) : entropyDensity m m = 0 := by
  simp [entropyDensity]

/-! ### The entropy -/

/-- The extended entropy: the lower integral of the Bregman integrand `ψ_m(g)`, `m = ∫ g dμ`.
It equals `ENNReal.ofReal (entropy μ g)` when `g log g` is integrable
(`eentropy_eq_ofReal_entropy`) and is `∞` otherwise (`integrable_mul_log_of_eentropy_ne_top`). -/
noncomputable def eentropy (μ : Measure α) (g : α → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (entropyDensity (∫ y, g y ∂μ) (g x)) ∂μ

variable {μ : Measure α} {g : α → ℝ}

theorem integrable_entropyDensity [IsFiniteMeasure μ] (m : ℝ) (hg : Integrable g μ)
    (hlog : Integrable (fun x => g x * log (g x)) μ) :
    Integrable (fun x => entropyDensity m (g x)) μ := by
  unfold entropyDensity
  exact ((hlog.sub (hg.mul_const _)).sub hg).add (integrable_const m)

theorem integral_entropyDensity [IsProbabilityMeasure μ] (m : ℝ) (hg : Integrable g μ)
    (hlog : Integrable (fun x => g x * log (g x)) μ) :
    ∫ x, entropyDensity m (g x) ∂μ =
      ∫ x, g x * log (g x) ∂μ - (∫ x, g x ∂μ) * log m - ∫ x, g x ∂μ + m := by
  unfold entropyDensity
  have h1 : Integrable (fun x => g x * log (g x) - g x * log m) μ := hlog.sub (hg.mul_const _)
  have h2 : Integrable (fun x => g x * log (g x) - g x * log m - g x) μ := h1.sub hg
  rw [integral_add h2 (integrable_const m), integral_sub h1 hg,
    integral_sub hlog (hg.mul_const _), integral_mul_const, integral_const, probReal_univ,
    one_smul]

/-- The Bregman form of the entropy: `Ent_μ g = ∫ ψ_m(g) dμ` with `m = ∫ g dμ`. -/
theorem entropy_eq_integral_entropyDensity [IsProbabilityMeasure μ] (hg : Integrable g μ)
    (hlog : Integrable (fun x => g x * log (g x)) μ) :
    Cited.entropy μ g = ∫ x, entropyDensity (∫ y, g y ∂μ) (g x) ∂μ := by
  rw [integral_entropyDensity _ hg hlog, Cited.entropy]
  ring

theorem integral_eq_zero_imp_ae_zero (hg0 : 0 ≤ᵐ[μ] g) (hg : Integrable g μ)
    (h : ∫ x, g x ∂μ = 0) : g =ᵐ[μ] 0 :=
  (integral_eq_zero_iff_of_nonneg_ae hg0 hg).1 h

/-- The entropy of a nonnegative function on a probability space is nonnegative. -/
theorem entropy_nonneg [IsProbabilityMeasure μ] (hg0 : 0 ≤ᵐ[μ] g) (hg : Integrable g μ)
    (hlog : Integrable (fun x => g x * log (g x)) μ) : 0 ≤ Cited.entropy μ g := by
  rcases (integral_nonneg_of_ae hg0).eq_or_lt with hm | hm
  · have hz := integral_eq_zero_imp_ae_zero hg0 hg hm.symm
    have : ∫ x, g x * log (g x) ∂μ = 0 := by
      rw [integral_eq_zero_of_ae]
      filter_upwards [hz] with x hx
      simp [hx]
    rw [Cited.entropy, this, ← hm]
    simp
  · rw [entropy_eq_integral_entropyDensity hg hlog]
    exact integral_nonneg_of_ae (hg0.mono fun x hx => entropyDensity_nonneg hm hx)

theorem entropyDensity_integral_ae_nonneg [IsProbabilityMeasure μ] (hg0 : 0 ≤ᵐ[μ] g)
    (hg : Integrable g μ) : 0 ≤ᵐ[μ] fun x => entropyDensity (∫ y, g y ∂μ) (g x) := by
  rcases (integral_nonneg_of_ae hg0).eq_or_lt with hm | hm
  · filter_upwards [integral_eq_zero_imp_ae_zero hg0 hg hm.symm] with x hx
    simp [hx, ← hm]
  · filter_upwards [hg0] with x hx using entropyDensity_nonneg hm hx

/-- When `g log g` is integrable, the extended entropy is the entropy. -/
theorem eentropy_eq_ofReal_entropy [IsProbabilityMeasure μ] (hg0 : 0 ≤ᵐ[μ] g)
    (hg : Integrable g μ) (hlog : Integrable (fun x => g x * log (g x)) μ) :
    eentropy μ g = ENNReal.ofReal (Cited.entropy μ g) := by
  rw [entropy_eq_integral_entropyDensity hg hlog, eentropy,
    ofReal_integral_eq_lintegral_ofReal (integrable_entropyDensity _ hg hlog)
      (entropyDensity_integral_ae_nonneg hg0 hg)]

/-- A finite extended entropy forces `g log g` to be integrable. -/
theorem integrable_mul_log_of_eentropy_ne_top [IsProbabilityMeasure μ] (hg0 : 0 ≤ᵐ[μ] g)
    (hg : Integrable g μ) (hfin : eentropy μ g ≠ ∞) :
    Integrable (fun x => g x * log (g x)) μ := by
  set m := ∫ y, g y ∂μ
  have hmeas : AEStronglyMeasurable (fun x => entropyDensity m (g x)) μ := by
    unfold entropyDensity
    have h1 : AEStronglyMeasurable (fun x => g x * log (g x)) μ :=
      (hg.aestronglyMeasurable.aemeasurable.mul
        (Real.measurable_log.comp_aemeasurable hg.aestronglyMeasurable.aemeasurable))
        |>.aestronglyMeasurable
    exact ((h1.sub (hg.aestronglyMeasurable.mul_const _)).sub hg.aestronglyMeasurable).add
      aestronglyMeasurable_const
  have hint : Integrable (fun x => entropyDensity m (g x)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas
      (entropyDensity_integral_ae_nonneg hg0 hg)).1 hfin
  have : (fun x => g x * log (g x)) =
      fun x => entropyDensity m (g x) + g x * log m + g x - m := by
    funext x; unfold entropyDensity; ring
  rw [this]
  exact ((hint.add (hg.mul_const _)).add hg).sub (integrable_const m)

theorem eentropy_eq_top_of_not_integrable [IsProbabilityMeasure μ] (hg0 : 0 ≤ᵐ[μ] g)
    (hg : Integrable g μ) (hlog : ¬ Integrable (fun x => g x * log (g x)) μ) :
    eentropy μ g = ∞ := by
  by_contra h
  exact hlog (integrable_mul_log_of_eentropy_ne_top hg0 hg h)

/-! ### The Falik–Samorodnitsky lower bound -/

/-- **Falik–Samorodnitsky.** For `V ∈ L²(μ)` on a probability space, with `a = E V²` and
`b = (E |V|)²`, `a log (a / b) ≤ Ent_μ (V²)`. -/
theorem mul_log_div_le_entropy_sq [IsProbabilityMeasure μ] {V : α → ℝ} (hV : MemLp V 2 μ)
    (hlog : Integrable (fun x => V x ^ 2 * log (V x ^ 2)) μ) :
    (∫ x, V x ^ 2 ∂μ) * log ((∫ x, V x ^ 2 ∂μ) / (∫ x, |V x| ∂μ) ^ 2) ≤
      Cited.entropy μ (fun x => V x ^ 2) := by
  set a := ∫ x, V x ^ 2 ∂μ with ha_def
  set c := ∫ x, |V x| ∂μ with hc_def
  have hV2 : Integrable (fun x => V x ^ 2) μ := hV.integrable_sq
  have hV1 : Integrable (fun x => |V x|) μ := (hV.integrable one_le_two).abs
  have hnn : 0 ≤ᵐ[μ] fun x => V x ^ 2 := ae_of_all _ fun x => sq_nonneg _
  have hEnt := entropy_nonneg hnn hV2 hlog
  rcases (integral_nonneg (fun x => abs_nonneg (V x)) : 0 ≤ c).eq_or_lt with hc | hc
  · have hc0 : c = 0 := hc.symm
    rw [hc0]; simpa using hEnt
  have ha : 0 < a := by
    rcases (integral_nonneg (fun x => sq_nonneg (V x)) : 0 ≤ a).eq_or_lt with ha | ha
    · exfalso
      have hz := integral_eq_zero_imp_ae_zero hnn hV2 ha.symm
      have : c = 0 := by
        rw [hc_def]
        refine integral_eq_zero_of_ae (hz.mono fun x hx => ?_)
        simpa using hx
      exact hc.ne' this
    · exact ha
  set l := a / c with hl_def
  have hl : 0 < l := div_pos ha hc
  have hpt : ∀ x, 2 * (V x ^ 2 * log l + V x ^ 2 - l * |V x|) ≤ V x ^ 2 * log (V x ^ 2) := by
    intro x
    have h := mul_log_ge |V x| (abs_nonneg _) hl
    have h' := mul_le_mul_of_nonneg_left h (abs_nonneg (V x))
    have e1 : V x ^ 2 * log (V x ^ 2) = 2 * (|V x| * (|V x| * log |V x|)) := by
      rw [log_pow, log_abs, ← sq_abs (V x)]
      push_cast; ring
    rw [e1, ← sq_abs (V x)]
    nlinarith [h']
  have hlow : Integrable (fun x => 2 * (V x ^ 2 * log l + V x ^ 2 - l * |V x|)) μ :=
    (((hV2.mul_const _).add hV2).sub (hV1.const_mul _)).const_mul _
  have hint := integral_mono hlow hlog hpt
  have hcomp : ∫ x, 2 * (V x ^ 2 * log l + V x ^ 2 - l * |V x|) ∂μ =
      2 * (a * log l + a - l * c) := by
    have i1 : Integrable (fun x => V x ^ 2 * log l) μ := hV2.mul_const _
    have i2 : Integrable (fun x => V x ^ 2 * log l + V x ^ 2) μ := i1.add hV2
    have i3 : Integrable (fun x => l * |V x|) μ := hV1.const_mul _
    rw [integral_const_mul, integral_sub i2 i3, integral_add i1 hV2, integral_mul_const,
      integral_const_mul]
  rw [hcomp] at hint
  have hlc : l * c = a := div_mul_cancel₀ a hc.ne'
  rw [Cited.entropy]
  rw [log_div ha.ne' (pow_ne_zero 2 hc.ne'), log_pow, hl_def, log_div ha.ne' hc.ne'] at *
  push_cast at *
  nlinarith [hint, hlc]

/-- The Falik–Samorodnitsky bound for the extended entropy, without integrability of
`V² log V²`. -/
theorem ofReal_mul_log_div_le_eentropy_sq [IsProbabilityMeasure μ] {V : α → ℝ}
    (hV : MemLp V 2 μ) :
    ENNReal.ofReal ((∫ x, V x ^ 2 ∂μ) * log ((∫ x, V x ^ 2 ∂μ) / (∫ x, |V x| ∂μ) ^ 2)) ≤
      eentropy μ (fun x => V x ^ 2) := by
  have hnn : 0 ≤ᵐ[μ] fun x => V x ^ 2 := ae_of_all _ fun x => sq_nonneg _
  by_cases hlog : Integrable (fun x => V x ^ 2 * log (V x ^ 2)) μ
  · rw [eentropy_eq_ofReal_entropy hnn hV.integrable_sq hlog]
    exact ENNReal.ofReal_le_ofReal (mul_log_div_le_entropy_sq hV hlog)
  · rw [eentropy_eq_top_of_not_integrable hnn hV.integrable_sq hlog]
    exact le_top

end IsotropicVariance.Infra.Entropy
