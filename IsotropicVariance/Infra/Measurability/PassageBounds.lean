/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.Passage
import Mathlib.Tactic.Linarith

/-! # Endpoint continuity of rectifiable passage times -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace IsotropicVariance.Infra.Measurability
open Curves
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/-- The literal passage-time definition equals the Lipschitz-curve infimum. -/
lemma passageTime_eq_lipschitz {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) (u v : E) :
    passageTime ρ u v = ⨅ γ : LipCurve E u v, γ.toRectifiable.cost ρ :=
  iInf_cost_rectifiable_eq_lipschitz hρ u v

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma passageTime_le_cost (ρ : E → ℝ≥0∞) {u v : E} (γ : RectifiableCurve E)
    (h0 : γ.toFun 0 = u) (h1 : γ.toFun 1 = v) : passageTime ρ u v ≤ γ.cost ρ :=
  iInf_le_of_le γ (iInf_le_of_le h0 (iInf_le _ h1))

omit [MeasurableSpace E] [BorelSpace E] in
lemma passageTime_le_edist {ρ : E → ℝ≥0∞} {b : ℝ≥0∞} (hb : ∀ x, ρ x ≤ b) (u v : E) :
    passageTime ρ u v ≤ b * edist u v := by
  have h := (segment u v).toRectifiable.cost_le_mul_length hb
  rw [rectifiable_length_segment] at h
  have heq : ‖v - u‖ₑ = edist u v := by rw [edist_eq_enorm_sub, enorm_sub_rev]
  rw [heq] at h
  exact (passageTime_le_cost ρ (segment u v).toRectifiable
    (segment u v).map_zero (segment u v).map_one).trans h

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma passageTime_triangle {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) (u v w : E) :
    passageTime ρ u w ≤ passageTime ρ u v + passageTime ρ v w := by
  simp only [passageTime, ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 =>
    le_iInf fun δ => le_iInf fun h2 => le_iInf fun h3 => ?_
  have hend := h3.trans h0.symm
  have h := passageTime_le_cost ρ (δ.concat γ hend)
    ((δ.concat_start γ hend).trans h2) ((δ.concat_end γ hend).trans h1)
  rw [δ.cost_concat γ hend hρ] at h
  exact h

omit [MeasurableSpace E] [BorelSpace E] in
lemma passageTime_ne_top {ρ : E → ℝ≥0∞} {b : ℝ≥0} (hb : ∀ x, ρ x ≤ b) (u v : E) :
    passageTime ρ u v ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _))
    (passageTime_le_edist hb u v)

/-- Endpoint perturbations cost at most two short straight segments. -/
lemma passageTime_endpoint_bound {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) {b : ℝ≥0}
    (hb : ∀ x, ρ x ≤ b) (u v u' v' : E) :
    (passageTime ρ u v).toReal ≤ (passageTime ρ u' v').toReal +
      (b : ℝ) * (dist u u' + dist v v') := by
  have h := (passageTime_triangle hρ u u' v).trans
    (add_le_add le_rfl (passageTime_triangle hρ u' v' v))
  have h' : passageTime ρ u v ≤ (b : ℝ≥0∞) * edist u u' +
      (passageTime ρ u' v' + (b : ℝ≥0∞) * edist v' v) :=
    h.trans (add_le_add (passageTime_le_edist hb u u')
      (add_le_add le_rfl (passageTime_le_edist hb v' v)))
  have hn (x y : E) : (b : ℝ≥0∞) * edist x y ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)
  have hnT := passageTime_ne_top hb u' v'
  have hnS := ENNReal.add_ne_top.mpr ⟨hnT, hn v' v⟩
  have H := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hn u u', hnS⟩) h'
  rw [ENNReal.toReal_add (hn u u') hnS,
    ENNReal.toReal_add hnT (hn v' v)] at H
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist, ENNReal.toReal_ofReal
    dist_nonneg, dist_comm v' v, mul_add, add_comm, add_left_comm, add_assoc] using H

/-- The endpoint map is Lipschitz, hence continuous, for every bounded Borel density. -/
theorem lipschitzWith_passageTime {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) {b : ℝ≥0}
    (hb : ∀ x, ρ x ≤ b) :
    LipschitzWith (2 * b) (fun p : E × E => (passageTime ρ p.1 p.2).toReal) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1 := passageTime_endpoint_bound hρ hb p.1 p.2 q.1 q.2
  have h2 := passageTime_endpoint_bound hρ hb q.1 q.2 p.1 p.2
  have hd1 : dist p.1 q.1 ≤ dist p q := le_max_left _ _
  have hd2 := le_max_right (dist p.1 q.1) (dist p.2 q.2)
  change dist p.2 q.2 ≤ dist p q at hd2
  simp only [NNReal.coe_mul, NNReal.coe_ofNat] at *
  rw [dist_comm q.1 p.1, dist_comm q.2 p.2] at h2
  constructor <;> nlinarith [b.coe_nonneg]

end IsotropicVariance.Infra.Measurability
