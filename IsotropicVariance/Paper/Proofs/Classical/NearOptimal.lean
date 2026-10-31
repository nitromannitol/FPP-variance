/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.TimeConstant.Mean

/-! # Near-optimal curves and their subarcs

The geometric length control used by the cube replacement argument comes from
positive density bounds and exact additivity of the literal arc-length cost.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra

/-- Every rectifiable curve has finite cost for the bounded density of a setting. -/
theorem setting_curve_cost_ne_top {m : ℕ} (X : Setting m) (ω : X.Ω)
    (γ : RectifiableCurve (Pt m)) : γ.cost (fun x => ENNReal.ofReal (X.ρ ω x)) ≠ ⊤ := by
  obtain ⟨_a, b, _ha, hab⟩ := X.bounds
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top γ.length_ne_top)
    (γ.cost_le_mul_length (fun x => ENNReal.ofReal_le_ofReal (hab ω x).2))

/-- A curve bounds the real surface passage time between its endpoints. -/
theorem passTime_le_curve_cost {m : ℕ} (X : Setting m) (ω : X.Ω)
    (γ : RectifiableCurve (Pt m)) :
    X.passTime ω (γ.toFun 0) (γ.toFun 1) ≤ (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal := by
  have hh := ENNReal.toReal_mono (setting_curve_cost_ne_top X ω γ)
    (Measurability.passageTime_le_cost (fun x => ENNReal.ofReal (X.ρ ω x)) γ rfl rfl)
  exact hh

/-- Taking the full parameter subarc preserves cost. -/
theorem cost_full_subcurve {E : Type*} [PseudoMetricSpace E] (γ : RectifiableCurve E)
    (ρ : E → ℝ≥0∞) : (γ.subcurve 0 1 le_rfl zero_le_one le_rfl).cost ρ = γ.cost ρ := by
  apply RectifiableCurve.cost_congr_curve
  intro t _ht
  simp only [RectifiableCurve.subcurve, Curves.subParam, Function.comp_apply,
    sub_zero, mul_one, zero_add]

/-- Every subarc of an epsilon-optimal curve is epsilon-optimal, stated for the
actual literal costs and passage times of the paper's setting. -/
theorem nearoptimal_subarc {m : ℕ} (X : Setting m) (ω : X.Ω)
    (γ : RectifiableCurve (Pt m)) {ε : ℝ}
    (hNear : (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal ≤
      X.passTime ω (γ.toFun 0) (γ.toFun 1) + ε)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ((γ.subcurve a b ha hab hb).cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal ≤
      X.passTime ω (γ.toFun a) (γ.toFun b) + ε := by
  let ρ := fun x => ENNReal.ofReal (X.ρ ω x)
  have hρ : Measurable ρ := (X.measurable_ρ.comp measurable_prodMk_left).ennreal_ofReal
  let δ₀ := γ.subcurve 0 a le_rfl ha (hab.trans hb)
  let δ₁ := γ.subcurve a b ha hab hb
  let δ₂ := γ.subcurve b 1 (ha.trans hab) hb le_rfl
  have hSplit : δ₀.cost ρ + δ₁.cost ρ + δ₂.cost ρ = γ.cost ρ := by
    calc
      _ = (γ.subcurve 0 b le_rfl (ha.trans hab) hb).cost ρ + δ₂.cost ρ :=
        congrArg (fun z => z + δ₂.cost ρ) (γ.cost_subcurve_add hρ le_rfl ha hab hb)
      _ = (γ.subcurve 0 1 le_rfl zero_le_one le_rfl).cost ρ :=
        γ.cost_subcurve_add hρ le_rfl (ha.trans hab) hb le_rfl
      _ = _ := cost_full_subcurve γ ρ
  have hReal := congrArg ENNReal.toReal hSplit
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨setting_curve_cost_ne_top X ω δ₀,
    setting_curve_cost_ne_top X ω δ₁⟩) (setting_curve_cost_ne_top X ω δ₂),
    ENNReal.toReal_add (setting_curve_cost_ne_top X ω δ₀) (setting_curve_cost_ne_top X ω δ₁)] at hReal
  have hLeft : X.passTime ω (γ.toFun 0) (γ.toFun a) ≤ (δ₀.cost ρ).toReal := by
    simpa only [δ₀, RectifiableCurve.subcurve_start, RectifiableCurve.subcurve_end] using
      passTime_le_curve_cost X ω δ₀
  have hRight : X.passTime ω (γ.toFun b) (γ.toFun 1) ≤ (δ₂.cost ρ).toReal := by
    simpa only [δ₂, RectifiableCurve.subcurve_start, RectifiableCurve.subcurve_end] using
      passTime_le_curve_cost X ω δ₂
  have hAround := (TimeConstant.setting_passTime_triangle X ω (γ.toFun 0) (γ.toFun a) (γ.toFun 1)).trans
    (add_le_add le_rfl (TimeConstant.setting_passTime_triangle X ω (γ.toFun a) (γ.toFun b) (γ.toFun 1)))
  change (δ₁.cost ρ).toReal ≤ X.passTime ω (γ.toFun a) (γ.toFun b) + ε
  change (γ.cost ρ).toReal ≤ X.passTime ω (γ.toFun 0) (γ.toFun 1) + ε at hNear
  linarith only [hNear, hReal, hLeft, hRight, hAround]

end IsotropicVariance.Paper.Proofs.Classical
