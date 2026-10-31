/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.PassageBounds
public import Mathlib.Probability.Moments.Variance

/-! # Deterministic bounds and density scaling for the continuum passage time

The real passage time is the literal rectifiable-curve infimum, as in
`IsotropicVariance.passageTime`. The bridge to the paper's setting is proved in
`IsotropicVariance.Infra.TimeConstant.SettingBounds`.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace IsotropicVariance.Infra.TimeConstant
open Curves

/-- The real passage time associated with a real-valued density. -/
noncomputable def passage {E : Type*} [MetricSpace E] [MeasurableSpace E]
    (σ : E → ℝ) (u v : E) : ℝ := (Measurability.passageTime (fun x => ENNReal.ofReal (σ x)) u v).toReal

/-- A lower density bound gives the corresponding endpoint lower bound. -/
theorem edist_mul_le_passageTime {E : Type*} [MetricSpace E] [MeasurableSpace E]
    (ρ : E → ℝ≥0∞) {a : ℝ≥0∞} (ha : ∀ x, a ≤ ρ x) (u v : E) :
    a * edist u v ≤ Measurability.passageTime ρ u v := by
  refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => ?_
  have h := γ.edist_endpoints_le_length
  rw [h0, h1] at h
  exact (mul_le_mul_right h a).trans (γ.mul_length_le_cost ha)

/-- Multiplying a density by a positive finite scalar multiplies the literal
extended passage time by that scalar. -/
theorem passageTime_mul {E : Type*} [MetricSpace E] [MeasurableSpace E]
    (ρ : E → ℝ≥0∞) {k : ℝ≥0∞} (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (u v : E) :
    Measurability.passageTime (fun x => k * ρ x) u v = k * Measurability.passageTime ρ u v := by
  simp only [Measurability.passageTime, ENNReal.mul_iInf_of_ne hk0 hkt]
  apply iInf_congr
  intro γ
  apply iInf_congr
  intro _
  apply iInf_congr
  intro _
  exact lintegral_const_mul' _ _ hkt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
/-- Real passage times lie between the lower and upper density bounds times
the Euclidean distance. -/
theorem passage_bounds {σ : E → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hσ : ∀ x, a ≤ σ x ∧ σ x ≤ b) (u v : E) :
    a * dist u v ≤ passage σ u v ∧ passage σ u v ≤ b * dist u v := by
  have hb : 0 ≤ b := ha.trans ((hσ u).1.trans (hσ u).2)
  have hUp : Measurability.passageTime (fun x => ENNReal.ofReal (σ x)) u v ≤
      ENNReal.ofReal b * edist u v :=
    Measurability.passageTime_le_edist (fun x => ENNReal.ofReal_le_ofReal (hσ x).2) u v
  have hFin : Measurability.passageTime (fun x => ENNReal.ofReal (σ x)) u v ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top _ _)) hUp
  have hLo := edist_mul_le_passageTime (fun x => ENNReal.ofReal (σ x))
    (fun x => ENNReal.ofReal_le_ofReal (hσ x).1) u v
  constructor
  · have hh := ENNReal.toReal_mono hFin hLo
    simpa only [passage, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] using hh
  · have hh := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top _ _)) hUp
    simpa only [passage, ENNReal.toReal_mul, ENNReal.toReal_ofReal hb, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] using hh

/-- Endpoint Lipschitz bound in its additive form. -/
theorem abs_passage_sub_le {σ : E → ℝ} (hm : Measurable σ) {b : ℝ} (hb : 0 ≤ b)
    (hσ : ∀ x, σ x ≤ b) (u v u' v' : E) :
    |passage σ u v - passage σ u' v'| ≤ b * (dist u u' + dist v v') := by
  let B : ℝ≥0 := ⟨b, hb⟩
  have hBound : ∀ x, ENNReal.ofReal (σ x) ≤ (B : ℝ≥0∞) := by
    intro x
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hσ x)
  have h1 := Measurability.passageTime_endpoint_bound hm.ennreal_ofReal hBound u v u' v'
  have h2 := Measurability.passageTime_endpoint_bound hm.ennreal_ofReal hBound u' v' u v
  rw [dist_comm u' u, dist_comm v' v] at h2
  change passage σ u v ≤ passage σ u' v' + b * (dist u u' + dist v v') at h1
  change passage σ u' v' ≤ passage σ u v + b * (dist u u' + dist v v') at h2
  exact abs_sub_le_iff.mpr ⟨by linarith only [h1], by linarith only [h2]⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Positive scalar division commutes with the real passage time. -/
theorem passage_div (σ : E → ℝ) {k : ℝ} (hk : 0 < k) (u v : E) :
    passage (fun x => σ x / k) u v = passage σ u v / k := by
  have he : (fun x => ENNReal.ofReal (σ x / k)) =
      fun x => ENNReal.ofReal (k⁻¹) * ENNReal.ofReal (σ x) := by
    funext x
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (inv_pos.mpr hk).le]
  unfold passage
  rw [he, passageTime_mul _ (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr hk)) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_pos.mpr hk).le]
  ring

end IsotropicVariance.Infra.TimeConstant
