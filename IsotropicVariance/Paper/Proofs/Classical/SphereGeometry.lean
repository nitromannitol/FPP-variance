/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.Approximation
import IsotropicVariance.Paper.Proofs.Profiles.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# Two ordered sphere crossings

The geometric step of the proof of [HN, Lemma 4.1], which the proof of Lemma `lem:classical` cites:
a curve between endpoints at distance at least twice the radius has two
ordered cuts on the endpoint spheres. The costs of its two end pieces are bounded by its total
cost. No geodesic or measurable curve selection is required. The cost splitting follows
`IsotropicVariance.Paper.Proofs.Classical.NearOptimal`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Classical

/-- Ordered points on the two endpoint spheres of a rectifiable curve. -/
theorem exists_ordered_sphere_cuts {E : Type*} [PseudoMetricSpace E]
    (γ : RectifiableCurve E) {r : ℝ} (hr : 0 ≤ r)
    (hD : 2 * r ≤ dist (γ.toFun 0) (γ.toFun 1)) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      dist (γ.toFun 0) (γ.toFun a) = r ∧ dist (γ.toFun 1) (γ.toFun b) = r := by
  have hc₀ : ContinuousOn (fun t => dist (γ.toFun 0) (γ.toFun t)) (Icc (0 : ℝ) 1) :=
    fun t ht => continuousWithinAt_const.dist (γ.continuousOn t ht)
  obtain ⟨a, ha, har⟩ := intermediate_value_Icc zero_le_one hc₀
    (show r ∈ Icc (dist (γ.toFun 0) (γ.toFun 0)) (dist (γ.toFun 0) (γ.toFun 1)) by
      rw [dist_self]
      exact ⟨hr, by linarith only [hD, hr]⟩)
  change dist (γ.toFun 0) (γ.toFun a) = r at har
  have hfar : r ≤ dist (γ.toFun 1) (γ.toFun a) := by
    have hh := dist_triangle (γ.toFun 0) (γ.toFun a) (γ.toFun 1)
    rw [har, dist_comm (γ.toFun a) (γ.toFun 1)] at hh
    linarith only [hD, hh]
  have hc₁ : ContinuousOn (fun t => dist (γ.toFun 1) (γ.toFun t)) (Icc a 1) :=
    fun t ht => continuousWithinAt_const.dist
      ((γ.continuousOn.mono (Icc_subset_Icc ha.1 le_rfl)) t ht)
  obtain ⟨b, hb, hbr⟩ := intermediate_value_Icc' ha.2 hc₁
    (show r ∈ Icc (dist (γ.toFun 1) (γ.toFun 1)) (dist (γ.toFun 1) (γ.toFun a)) by
      rw [dist_self]
      exact ⟨hr, hfar⟩)
  exact ⟨a, b, ha.1, hb.1, hb.2, har, hbr⟩

/-- The passage costs of two ordered end pieces are at most the whole curve cost. -/
theorem end_passTime_sum_le_curve_cost {m : ℕ} (X : Setting m) (ω : X.Ω)
    (γ : RectifiableCurve (Pt m)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    X.passTime ω (γ.toFun 0) (γ.toFun a) + X.passTime ω (γ.toFun b) (γ.toFun 1) ≤
      (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal := by
  let ρ := fun x => ENNReal.ofReal (X.ρ ω x)
  have hρ : Measurable ρ := (X.measurable_ρ.comp measurable_prodMk_left).ennreal_ofReal
  let δ₀ := γ.subcurve 0 a le_rfl ha (hab.trans hb)
  let δ₁ := γ.subcurve a b ha hab hb
  let δ₂ := γ.subcurve b 1 (ha.trans hab) hb le_rfl
  have hsplit : δ₀.cost ρ + δ₁.cost ρ + δ₂.cost ρ = γ.cost ρ := by
    calc
      _ = (γ.subcurve 0 b le_rfl (ha.trans hab) hb).cost ρ + δ₂.cost ρ :=
        congrArg (fun z => z + δ₂.cost ρ) (γ.cost_subcurve_add hρ le_rfl ha hab hb)
      _ = (γ.subcurve 0 1 le_rfl zero_le_one le_rfl).cost ρ :=
        γ.cost_subcurve_add hρ le_rfl (ha.trans hab) hb le_rfl
      _ = _ := cost_full_subcurve γ ρ
  have hreal := congrArg ENNReal.toReal hsplit
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨setting_curve_cost_ne_top X ω δ₀,
    setting_curve_cost_ne_top X ω δ₁⟩) (setting_curve_cost_ne_top X ω δ₂),
    ENNReal.toReal_add (setting_curve_cost_ne_top X ω δ₀) (setting_curve_cost_ne_top X ω δ₁)] at hreal
  have hleft : X.passTime ω (γ.toFun 0) (γ.toFun a) ≤ (δ₀.cost ρ).toReal := by
    simpa only [δ₀, RectifiableCurve.subcurve_start, RectifiableCurve.subcurve_end] using
      passTime_le_curve_cost X ω δ₀
  have hright : X.passTime ω (γ.toFun b) (γ.toFun 1) ≤ (δ₂.cost ρ).toReal := by
    simpa only [δ₂, RectifiableCurve.subcurve_start, RectifiableCurve.subcurve_end] using
      passTime_le_curve_cost X ω δ₂
  have hmiddle := ENNReal.toReal_nonneg (a := δ₁.cost ρ)
  linarith only [hleft, hright, hreal, hmiddle]

/-- Uniform lower bounds for the two endpoint spheres add to a lower bound for passage time. -/
theorem passTime_ge_of_sphere_lower {m : ℕ} (X : Setting m) (ω : X.Ω) (u v : Pt m)
    {r L₀ L₁ : ℝ} (hr : 0 ≤ r) (hD : 2 * r ≤ dist u v)
    (h₀ : ∀ z : Pt m, dist u z = r → L₀ ≤ X.passTime ω u z)
    (h₁ : ∀ z : Pt m, dist v z = r → L₁ ≤ X.passTime ω v z) :
    L₀ + L₁ ≤ X.passTime ω u v := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨γ, hγ₀, hγ₁, hcost⟩ := exists_nearoptimal_curve X ω u v hε
  obtain ⟨a, b, ha, hab, hb, har, hbr⟩ := exists_ordered_sphere_cuts γ hr
    (by simpa only [hγ₀, hγ₁] using hD)
  rw [hγ₀] at har
  rw [hγ₁] at hbr
  have hleft := h₀ (γ.toFun a) har
  have hright := h₁ (γ.toFun b) hbr
  have hcomm : X.passTime ω (γ.toFun b) v = X.passTime ω v (γ.toFun b) := by
    exact Profiles.passTime_comm ω _ _
  have hsum := end_passTime_sum_le_curve_cost X ω γ ha hab hb
  rw [hγ₀, hγ₁, hcomm] at hsum
  linarith only [hleft, hright, hsum, hcost]

end IsotropicVariance.Paper.Proofs.Classical
