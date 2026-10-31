/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Countable Minkowski and indicator Hölder estimates

The analytic inequalities used in the proof of Lemma `lem:blocks`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

/-- **Minkowski's inequality for countable sums** of nonnegative extended functions. -/
theorem eLpNorm_tsum_le {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ι → Ω → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) μ) :
    eLpNorm (fun ω => ∑' i, f i ω) p μ ≤ ∑' i, eLpNorm (f i) p μ := by
  classical
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hmt : AEMeasurable (fun ω => ∑' i, f i ω) μ := AEMeasurable.tsum hf
  by_cases hptop : p = ∞
  · subst hptop
    rw [eLpNorm_exponent_top hmt.aestronglyMeasurable]
    have hae : ∀ᵐ ω ∂μ, ∀ i, f i ω ≤ eLpNorm (f i) ∞ μ :=
      ae_all_iff.2 fun i => by
        filter_upwards [enorm_ae_le_eLpNormEssSup (f i) μ] with ω hω
        exact hω.trans eLpNormEssSup_le_eLpNorm_top
    refine eLpNormEssSup_le_of_ae_enorm_bound ?_
    filter_upwards [hae] with ω hω
    exact ENNReal.tsum_le_tsum hω
  · have hq : 1 ≤ p.toReal := by
      have := ENNReal.toReal_mono hptop hp
      simpa using this
    have hq0 : 0 < p.toReal := zero_lt_one.trans_le hq
    set T := ∑' i, eLpNorm (f i) p μ with hT
    set S : Finset ι → Ω → ℝ≥0∞ := fun s ω => ∑ i ∈ s, f i ω with hS
    have hSeq : ∀ s, S s = ∑ i ∈ s, f i := fun s => by
      funext ω; simp [hS, Finset.sum_apply]
    have hSm : ∀ s, AEMeasurable (S s) μ := fun s => by
      rw [hSeq]; exact Finset.aemeasurable_sum s fun i _ => hf i
    have hSle : ∀ s, ∫⁻ ω, S s ω ^ p.toReal ∂μ ≤ T ^ p.toReal := by
      intro s
      have h1 : eLpNorm (S s) p μ ≤ T := by
        rw [hSeq]; exact (eLpNorm_sum_le hp).trans (ENNReal.sum_le_tsum s)
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (hSm s).aestronglyMeasurable] at h1
      have h2 := ENNReal.rpow_le_rpow h1 hq0.le
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one] at h2
      simpa using h2
    have hsup : ∀ ω, (∑' i, f i ω) ^ p.toReal = ⨆ s, S s ω ^ p.toReal := by
      intro ω
      rw [ENNReal.tsum_eq_iSup_sum]
      have hmono := ENNReal.monotone_rpow_of_nonneg hq0.le
      refine hmono.map_iSup_of_continuousAt ENNReal.continuous_rpow_const.continuousAt ?_
      simp [hq0]
    have hdir : Directed (· ≤ ·) fun s : Finset ι => fun ω => S s ω ^ p.toReal := by
      intro s t
      refine ⟨s ∪ t, fun ω => ?_, fun ω => ?_⟩
      · exact ENNReal.rpow_le_rpow (by
          simpa [hS] using Finset.sum_le_sum_of_subset (f := fun i => f i ω)
            (Finset.subset_union_left (s₁ := s) (s₂ := t))) hq0.le
      · exact ENNReal.rpow_le_rpow (by
          simpa [hS] using Finset.sum_le_sum_of_subset (f := fun i => f i ω)
            (Finset.subset_union_right (s₁ := s) (s₂ := t))) hq0.le
    have hint : ∫⁻ ω, (∑' i, f i ω) ^ p.toReal ∂μ ≤ T ^ p.toReal := by
      simp_rw [hsup]
      rw [lintegral_iSup_directed (fun s => (hSm s).pow_const _) hdir]
      exact iSup_le hSle
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hmt.aestronglyMeasurable]
    have h3 := ENNReal.rpow_le_rpow hint (by positivity : 0 ≤ 1 / p.toReal)
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] at h3
    simpa using h3

/-- **Hölder with an indicator**, for extended functions:
`‖1_s f‖_a ≤ ‖f‖_{2a} μ(s)^{1/(2a)}`. -/
theorem eLpNorm_indicator_le_double_ennreal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : ℝ} (ha : 0 < a) {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ) {s : Set Ω}
    (hs : MeasurableSet s) :
    eLpNorm (s.indicator f) (ENNReal.ofReal a) μ ≤
      eLpNorm f (ENNReal.ofReal (2 * a)) μ * μ s ^ (1 / (2 * a)) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := f) (μ := μ.restrict s)
    (p := ENNReal.ofReal a) (q := ENNReal.ofReal (2 * a))
    (ENNReal.ofReal_le_ofReal (by linarith)) hf.aestronglyMeasurable.restrict
  have hexp : 1 / a - 1 / (2 * a) = 1 / (2 * a) := by field_simp; ring
  simp only [ENNReal.toReal_ofReal ha.le,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * a), Measure.restrict_apply_univ, hexp] at h
  exact h.trans (mul_le_mul' (eLpNorm_restrict_le f _ μ s) le_rfl)

/-- An `L^n` bound for an integer exponent `n ≥ 1` is a bound for the `n`-th moment. -/
theorem lintegral_pow_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 0 ≤ c)
    (h : eLpNorm f (ENNReal.ofReal n) μ ≤ ENNReal.ofReal c) :
    ∫⁻ ω, f ω ^ n ∂μ ≤ ENNReal.ofReal (c ^ n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; omega) ENNReal.ofReal_ne_top
    hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hn0.le] at h
  have h2 := ENNReal.rpow_le_rpow h (by positivity : (0 : ℝ) ≤ n)
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hn0.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hc hn0.le, Real.rpow_natCast] at h2
  simpa only [enorm_eq_self, ENNReal.rpow_natCast] using h2

end IsotropicVariance.Paper.Proofs.Responses
