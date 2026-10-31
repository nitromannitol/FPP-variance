/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Natural
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Preservation of rectifiable cost by constant-speed parametrization -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace IsotropicVariance.RectifiableCurve
open IsotropicVariance.Infra.Curves
variable {E : Type*} [MetricSpace E]

lemma hasConstantSpeed_constantSpeed (γ : RectifiableCurve E) :
    HasConstantSpeedOnWith γ.constantSpeed.toFun (Icc 0 1)
      (Real.toNNReal γ.length.toReal) := by
  intro x hx y hy
  let φ : ℝ → ℝ := fun t => t * γ.length.toReal
  have hm : MonotoneOn φ (Icc 0 1) := by
    intro a _ b _ hab
    exact mul_le_mul_of_nonneg_right hab ENNReal.toReal_nonneg
  have himage : φ '' Icc (0 : ℝ) 1 = Icc 0 γ.length.toReal := by
    simpa [φ] using
      (show Continuous φ by fun_prop).continuousOn.image_Icc_of_monotoneOn zero_le_one hm
  have hmap : MapsTo φ (Icc 0 1) (Icc 0 γ.length.toReal) := by
    rw [← himage]; exact mapsTo_image _ _
  change eVariationOn (γ.natural ∘ φ) (Icc 0 1 ∩ Icc x y) = _
  rw [eVariationOn.comp_inter_Icc_eq_of_monotoneOn γ.natural φ hm hx hy, himage,
    γ.unitSpeed_natural (hmap hx) (hmap hy)]
  congr 1
  simp only [NNReal.coe_one, one_mul, Real.coe_toNNReal _ ENNReal.toReal_nonneg, φ]
  ring

lemma length_constantSpeed (γ : RectifiableCurve E) : γ.constantSpeed.length = γ.length := by
  have hscaled := γ.hasConstantSpeed_constantSpeed
  have h := hscaled (x := 0) (by simp) (y := 1) (by simp)
  simp only [inter_self, Real.coe_toNNReal _ ENNReal.toReal_nonneg, sub_zero, mul_one] at h
  exact h.trans (ENNReal.ofReal_toReal γ.length_ne_top)

/-- Every rectifiable curve has a Lipschitz representative with identical endpoints and cost. -/
theorem cost_constantSpeed [MeasurableSpace E] [BorelSpace E] (γ : RectifiableCurve E)
    {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) : γ.constantSpeed.cost ρ = γ.cost ρ := by
  by_cases hL : γ.length.toReal = 0
  · have hlen : γ.length = 0 := by
      rw [← ENNReal.ofReal_toReal γ.length_ne_top, hL, ENNReal.ofReal_zero]
    have hcost (δ : RectifiableCurve E) (hδ : δ.length = 0) : δ.cost ρ = 0 := by
      apply le_antisymm _ bot_le
      have h := δ.cost_le_mul_length (ρ := ρ) (b := ⊤) (fun _ => le_top)
      simpa [hδ] using h
    rw [hcost γ hlen, hcost γ.constantSpeed (by rw [γ.length_constantSpeed, hlen])]
  · let φ : ℝ → ℝ := fun t => γ.cumulativeLength t / γ.length.toReal
    have hpos : 0 < γ.length.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hL)
    have hc : Continuous φ := γ.continuous_cumulativeLength.div_const _
    have hm : MonotoneOn φ (Icc 0 1) := by
      intro a _ b _ hab
      exact div_le_div_of_nonneg_right (γ.monotone_cumulativeLength hab) hpos.le
    have h0 : φ 0 = 0 := by simp [φ, γ.cumulativeLength_of_nonpos le_rfl]
    have h1 : φ 1 = 1 := by simp [φ, γ.cumulativeLength_of_one_le le_rfl, hL]
    have heq : EqOn (γ.constantSpeed.reparam φ hc hm h0 h1).toFun γ.toFun (Icc 0 1) := by
      intro t ht
      change γ.natural ((γ.cumulativeLength t / γ.length.toReal) * γ.length.toReal) = _
      rw [div_mul_cancel₀ _ hL]
      exact γ.natural_cumulativeLength ht
    exact (γ.constantSpeed.cost_reparam hρ hc hm h0 h1).symm.trans
      (cost_congr_curve heq ρ)

end IsotropicVariance.RectifiableCurve

namespace IsotropicVariance.Infra.Curves
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Lipschitz curves give the same infimum as continuous rectifiable curves. Both sides use
arc-length cost; the derivative-integral cost identity is a separate result. -/
theorem iInf_cost_rectifiable_eq_lipschitz {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) (u v : E) :
    (⨅ γ : RectifiableCurve E, ⨅ (_ : γ.toFun 0 = u), ⨅ (_ : γ.toFun 1 = v), γ.cost ρ) =
      ⨅ γ : LipCurve E u v, γ.toRectifiable.cost ρ := by
  apply le_antisymm
  · apply le_iInf
    intro γ
    exact iInf_le_of_le γ.toRectifiable
      (iInf_le_of_le γ.map_zero (iInf_le_of_le γ.map_one le_rfl))
  · apply le_iInf
    intro γ
    apply le_iInf
    intro h0
    apply le_iInf
    intro h1
    let η : LipCurve E u v :=
      ⟨γ.constantSpeed.toFun, ⟨_, γ.lipschitzOnWith_constantSpeed⟩,
        γ.constantSpeed_start.trans h0, γ.constantSpeed_end.trans h1⟩
    have heq : η.toRectifiable.cost ρ = γ.constantSpeed.cost ρ :=
      RectifiableCurve.cost_congr_curve (fun _ _ => rfl) ρ
    exact (iInf_le (fun δ : LipCurve E u v => δ.toRectifiable.cost ρ) η).trans_eq
      (heq.trans (γ.cost_constantSpeed hρ))

end IsotropicVariance.Infra.Curves
