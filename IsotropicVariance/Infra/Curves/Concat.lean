/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Subcurve
public import IsotropicVariance.Infra.Curves.Clamped
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Concatenation and additivity of rectifiable curve costs -/

@[expose] public section
open Set MeasureTheory Filter Function
open scoped ENNReal Topology

namespace IsotropicVariance.RectifiableCurve
open IsotropicVariance.Infra.Curves
variable {E : Type*} [PseudoMetricSpace E]

noncomputable def concatFun (γ δ : RectifiableCurve E) (t : ℝ) : E :=
  if t ≤ 1 / 2 then γ.clamped (2 * t) else δ.clamped (2 * t - 1)

lemma concatFun_left (γ δ : RectifiableCurve E) {t : ℝ} (ht : t ≤ 1 / 2) :
    concatFun γ δ t = γ.clamped (2 * t) := ite_eq_left ht

lemma concatFun_right (γ δ : RectifiableCurve E) (hend : γ.toFun 1 = δ.toFun 0)
    {t : ℝ} (ht : 1 / 2 ≤ t) : concatFun γ δ t = δ.clamped (2 * t - 1) := by
  rcases ht.eq_or_lt with h | h
  · subst t
    simp only [concatFun, le_refl, ↓reduceIte]
    norm_num
    rw [γ.clamped_eq (by simp), δ.clamped_eq (by simp), hend]
  · exact ite_eq_right (not_le_of_gt h)

/-- Concatenation at the common endpoint, using half of the parameter interval for each curve. -/
noncomputable def concat (γ δ : RectifiableCurve E) (hend : γ.toFun 1 = δ.toFun 0) :
    RectifiableCurve E where
  toFun := concatFun γ δ
  continuousOn := by
    apply Continuous.continuousOn
    apply Continuous.if
    · intro t ht
      change t ∈ frontier (Iic (1 / 2 : ℝ)) at ht
      have heq : t = 1 / 2 := by simpa only [frontier_Iic, mem_singleton_iff] using ht
      subst t
      norm_num
      rw [γ.clamped_eq (by simp), δ.clamped_eq (by simp), hend]
    · exact γ.continuous_clamped.comp (by fun_prop)
    · exact δ.continuous_clamped.comp (by fun_prop)
  boundedVariationOn := by
    have hl : BoundedVariationOn (concatFun γ δ) (Icc 0 (1 / 2)) := by
      unfold BoundedVariationOn
      rw [eVariationOn.congr (show EqOn (concatFun γ δ) (fun t => γ.clamped (2 * t))
        (Icc 0 (1 / 2)) from fun _ ht => concatFun_left γ δ ht.2)]
      apply ne_top_of_le_ne_top γ.boundedVariationOn_clamped
      exact eVariationOn.comp_le_of_monotoneOn γ.clamped (fun t : ℝ => 2 * t)
        (fun s _ t _ hst => by dsimp; linarith) (mapsTo_univ _ _)
    have hr : BoundedVariationOn (concatFun γ δ) (Icc (1 / 2) 1) := by
      unfold BoundedVariationOn
      rw [eVariationOn.congr (show EqOn (concatFun γ δ) (fun t => δ.clamped (2 * t - 1))
        (Icc (1 / 2) 1) from fun _ ht => concatFun_right γ δ hend ht.1)]
      apply ne_top_of_le_ne_top δ.boundedVariationOn_clamped
      exact eVariationOn.comp_le_of_monotoneOn δ.clamped (fun t : ℝ => 2 * t - 1)
        (fun s _ t _ hst => by dsimp; linarith) (mapsTo_univ _ _)
    have hv := eVariationOn.Icc_add_Icc (concatFun γ δ) (s := univ)
      (a := 0) (b := 1 / 2) (c := 1) (by norm_num) (by norm_num) (mem_univ _)
    simp only [univ_inter] at hv
    rw [BoundedVariationOn, ← hv]
    exact ENNReal.add_ne_top.mpr ⟨hl, hr⟩

lemma concat_subcurve_left (γ δ : RectifiableCurve E) (hend : γ.toFun 1 = δ.toFun 0) :
    EqOn ((γ.concat δ hend).subcurve 0 (1 / 2) (by norm_num) (by norm_num)
      (by norm_num)).toFun γ.toFun (Icc 0 1) := by
  intro t ht
  change concatFun γ δ (subParam 0 (1 / 2) t) = _
  rw [concatFun_left γ δ (by dsimp [subParam]; linarith [ht.2])]
  have heq : 2 * subParam 0 (1 / 2) t = t := by dsimp [subParam]; ring
  rw [heq, γ.clamped_eq ht]

lemma concat_subcurve_right (γ δ : RectifiableCurve E) (hend : γ.toFun 1 = δ.toFun 0) :
    EqOn ((γ.concat δ hend).subcurve (1 / 2) 1 (by norm_num) (by norm_num)
      (by norm_num)).toFun δ.toFun (Icc 0 1) := by
  intro t ht
  change concatFun γ δ (subParam (1 / 2) 1 t) = _
  rw [concatFun_right γ δ hend (by dsimp [subParam]; linarith [ht.1])]
  have heq : 2 * subParam (1 / 2) 1 t - 1 = t := by dsimp [subParam]; ring
  rw [heq, δ.clamped_eq ht]

/-- Splitting the parameter interval adds its arc-length integrals; endpoints carry no mass. -/
lemma arcCost_add (γ : RectifiableCurve E) (ρ : E → ℝ≥0∞) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    (∫⁻ t in Icc a b, ρ (γ.toFun t) ∂γ.arcLengthMeasure) +
      (∫⁻ t in Icc b c, ρ (γ.toFun t) ∂γ.arcLengthMeasure) =
        ∫⁻ t in Icc a c, ρ (γ.toFun t) ∂γ.arcLengthMeasure := by
  rw [← restrict_Ioc_eq_restrict_Icc, ← restrict_Ioc_eq_restrict_Icc,
    ← restrict_Ioc_eq_restrict_Icc]
  rw [← lintegral_union measurableSet_Ioc (show Disjoint (Ioc a b) (Ioc b c) by
    apply disjoint_left.mpr
    intro t ht ht'; exact (not_lt_of_ge ht.2) ht'.1)]
  rw [Ioc_union_Ioc_eq_Ioc hab hbc]

/-- Concatenation adds the literal arc-length costs for every Borel density. -/
theorem cost_concat [MeasurableSpace E] [BorelSpace E] (γ δ : RectifiableCurve E)
    (hend : γ.toFun 1 = δ.toFun 0) {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) :
    (γ.concat δ hend).cost ρ = γ.cost ρ + δ.cost ρ := by
  have hl := cost_congr_curve (γ.concat_subcurve_left δ hend) ρ
  have hr := cost_congr_curve (γ.concat_subcurve_right δ hend) ρ
  rw [(γ.concat δ hend).cost_subcurve hρ (by norm_num) (by norm_num) (by norm_num)] at hl hr
  rw [← hl, ← hr, (γ.concat δ hend).arcCost_add ρ (by norm_num) (by norm_num)]
  change (∫⁻ t, ρ ((γ.concat δ hend).toFun t) ∂(γ.concat δ hend).arcLengthMeasure) =
    ∫⁻ t, ρ ((γ.concat δ hend).toFun t) ∂(γ.concat δ hend).arcLengthMeasure.restrict (Icc 0 1)
  rw [(γ.concat δ hend).restrict_arcLengthMeasure_Icc]

lemma concat_start (γ δ : RectifiableCurve E) (hend : γ.toFun 1 = δ.toFun 0) :
    (γ.concat δ hend).toFun 0 = γ.toFun 0 := by
  change concatFun γ δ 0 = _
  rw [concatFun_left γ δ (by norm_num)]
  simpa using γ.clamped_eq (t := 0) (by simp)

lemma concat_end (γ δ : RectifiableCurve E) (hend : γ.toFun 1 = δ.toFun 0) :
    (γ.concat δ hend).toFun 1 = δ.toFun 1 := by
  change concatFun γ δ 1 = _
  rw [concatFun_right γ δ hend (by norm_num)]
  convert δ.clamped_eq (t := 1) (by simp) using 1; norm_num

/-- Splitting a subarc at an intermediate parameter adds its costs. -/
theorem cost_subcurve_add [MeasurableSpace E] [BorelSpace E] (γ : RectifiableCurve E)
    {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) :
    (γ.subcurve a b ha hab (hbc.trans hc)).cost ρ +
      (γ.subcurve b c (ha.trans hab) hbc hc).cost ρ =
        (γ.subcurve a c ha (hab.trans hbc) hc).cost ρ := by
  rw [γ.cost_subcurve hρ ha hab (hbc.trans hc),
    γ.cost_subcurve hρ (ha.trans hab) hbc hc,
    γ.cost_subcurve hρ ha (hab.trans hbc) hc]
  exact γ.arcCost_add ρ hab hbc

end IsotropicVariance.RectifiableCurve
