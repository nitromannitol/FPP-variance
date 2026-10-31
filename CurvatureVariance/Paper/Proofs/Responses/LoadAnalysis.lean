/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.IndexTubeCount
public import CurvatureVariance.Statements.Space.TransversePoint
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analytic estimates for slab loads

These are the countable Minkowski, indicator Hölder, summable shell, and penalized-tail estimates
used in the proof of the first bound of equation `eq:rewardmoment` (the proof of Lemma
`lem:blocks`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

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

/-- **The lattice sum about a segment**: for `s > m + 1` there is `C` with
`∑_{ℓ ∈ ℤ^m} (1 + dist(ℓ, [j, k]))^{-s} ≤ C (1 + |j - k|)` for all `j, k ∈ ℤ^m`. -/
theorem tsum_rpow_infDist_segment_le {m : ℕ} {s : ℝ} (hs : (m : ℝ) + 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ j k : Fin m → ℤ,
      ∑' ℓ : Fin m → ℤ, ENNReal.ofReal ((1 + Metric.infDist (transversePoint ℓ)
          (segment ℝ (transversePoint j) (transversePoint k))) ^ (-s)) ≤
        ENNReal.ofReal (C * (1 + ‖transversePoint (j - k)‖)) := by
  classical
  set u : ℕ → ℝ := fun r => ((r : ℝ) + 1) ^ ((m : ℝ) - s) with hu
  have hsum : Summable u := by
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ ((m : ℝ) - s) :=
      Real.summable_nat_rpow.2 (by linarith only [hs])
    have := (summable_nat_add_iff 1).2 h1
    simpa [hu] using this
  have hu0 : ∀ r, 0 < u r := fun r => by positivity
  refine ⟨2 * 5 ^ m * 2 ^ m * ∑' r, u r, mul_pos (by positivity)
    (hsum.tsum_pos (fun r => (hu0 r).le) 0 (hu0 0)), fun j k => ?_⟩
  set δ : ℝ := ‖transversePoint (j - k)‖ with hδ
  have hδ' : δ = ‖Geometry.indexPoint j - Geometry.indexPoint k‖ := by
    rw [hδ, Infra.FPP.transversePoint_sub]; rfl
  set d : (Fin m → ℤ) → ℝ := fun ℓ =>
    Metric.infDist (transversePoint ℓ) (segment ℝ (transversePoint j) (transversePoint k)) with hd
  have hd0 : ∀ ℓ, 0 ≤ d ℓ := fun ℓ => Metric.infDist_nonneg
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hfib : ∀ r : ℕ, ∑' ℓ : Fin m → ℤ, (if r = ⌊d ℓ⌋₊ then
      ENNReal.ofReal ((1 + d ℓ) ^ (-s)) else 0) ≤
      ENNReal.ofReal (2 * 5 ^ m * 2 ^ m * (1 + δ) * u r) := by
    intro r
    have hR : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
    set T := (Geometry.indexTube_finite j k ((r : ℝ) + 1)).toFinset with hT
    have hz : ∀ ℓ ∉ T, (if r = ⌊d ℓ⌋₊ then ENNReal.ofReal ((1 + d ℓ) ^ (-s)) else 0) = 0 := by
      intro ℓ hℓ
      refine ite_eq_right_iff.2 ?_
      intro h
      exfalso
      apply hℓ
      rw [hT, Set.Finite.mem_toFinset]
      show d ℓ ≤ (r : ℝ) + 1
      rw [h]; exact (Nat.lt_floor_add_one (d ℓ)).le
    have hle : ∀ ℓ ∈ T, (if r = ⌊d ℓ⌋₊ then ENNReal.ofReal ((1 + d ℓ) ^ (-s)) else 0) ≤
        ENNReal.ofReal (((r : ℝ) + 1) ^ (-s)) := by
      intro ℓ _
      split_ifs with h
      · refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) ?_
          (by linarith only [hs, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]))
        rw [h]; linarith only [Nat.floor_le (hd0 ℓ)]
      · exact bot_le
    rw [tsum_eq_sum hz]
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard := Geometry.card_indexTube_le j k hR
    rw [← hT, ← hδ'] at hcard
    have h2 : (1 + ((r : ℝ) + 1)) ^ m ≤ 2 ^ m * ((r : ℝ) + 1) ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith only [Nat.cast_nonneg (α := ℝ) r]) m
    have hpow : ((r : ℝ) + 1) ^ m * ((r : ℝ) + 1) ^ (-s) = u r := by
      rw [hu]; dsimp only
      rw [sub_eq_add_neg, Real.rpow_add (by positivity), Real.rpow_natCast]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw : 0 ≤ ((r : ℝ) + 1) ^ (-s) := by positivity
    calc (T.card : ℝ) * ((r : ℝ) + 1) ^ (-s)
        ≤ (2 * 5 ^ m * (1 + δ) * (1 + ((r : ℝ) + 1)) ^ m) * ((r : ℝ) + 1) ^ (-s) :=
          mul_le_mul_of_nonneg_right hcard hw
      _ ≤ (2 * 5 ^ m * (1 + δ) * (2 ^ m * ((r : ℝ) + 1) ^ m)) * ((r : ℝ) + 1) ^ (-s) := by
          gcongr
      _ = 2 * 5 ^ m * 2 ^ m * (1 + δ) * (((r : ℝ) + 1) ^ m * ((r : ℝ) + 1) ^ (-s)) := by ring
      _ = _ := by rw [hpow]
  calc ∑' ℓ : Fin m → ℤ, ENNReal.ofReal ((1 + d ℓ) ^ (-s))
      = ∑' ℓ : Fin m → ℤ, ∑' r : ℕ, (if r = ⌊d ℓ⌋₊ then
          ENNReal.ofReal ((1 + d ℓ) ^ (-s)) else 0) :=
        tsum_congr fun ℓ =>
          (tsum_ite_eq (⌊d ℓ⌋₊) (fun _ => ENNReal.ofReal ((1 + d ℓ) ^ (-s)))).symm
    _ = ∑' r : ℕ, ∑' ℓ : Fin m → ℤ, (if r = ⌊d ℓ⌋₊ then
          ENNReal.ofReal ((1 + d ℓ) ^ (-s)) else 0) := ENNReal.tsum_comm
    _ ≤ ∑' r : ℕ, ENNReal.ofReal (2 * 5 ^ m * 2 ^ m * (1 + δ) * u r) :=
        ENNReal.tsum_le_tsum hfib
    _ = ENNReal.ofReal (∑' r : ℕ, 2 * 5 ^ m * 2 ^ m * (1 + δ) * u r) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun r => by have := hu0 r; positivity)
          (hsum.mul_left _)).symm
    _ = _ := by rw [tsum_mul_left]; congr 1; ring


end CurvatureVariance.Paper.Responses
