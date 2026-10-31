/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.NearOptimal
public import IsotropicVariance.Paper.Defs.Restricted
import IsotropicVariance.Paper.Proofs.Classical.NearOptimal

/-! # Endpoint surgery for a curve whose middle avoids the slab faces

The middle subarc retains its original density cost. The endpoint Lipschitz estimate for the
slab passage time supplies the two straight connectors that replace the end pieces of a
near-geodesic in the proof of Lemma `lem:slab`.
-/

@[expose] public section
open Set MeasureTheory Metric
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

/-- A curve contained in the slab and farther than one from its faces has its original cost. -/
theorem slabTime_le_curve_cost (X : Setting m) (ω : X.Ω) (b : ℝ) (sl : Slab m)
    (γ : IsotropicVariance.RectifiableCurve (Pt m))
    (hinside : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ sl.set)
    (hfar : ∀ t ∈ Icc (0 : ℝ) 1, 1 < infDist (γ.toFun t) sl.faces) :
    X.slabTime b sl ω (γ.toFun 0) (γ.toFun 1) ≤
      (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal := by
  have hcost : γ.cost (fun x => ENNReal.ofReal (sl.density b (X.ρ ω) x)) =
      γ.cost (fun x => ENNReal.ofReal (X.ρ ω x)) := by
    apply γ.cost_congr
    intro t ht
    simp only [Slab.density, ite_eq_right (not_le_of_gt (hfar t ht))]
  have h := Paper.restrictedInf_le_cost (σ := sl.density b (X.ρ ω)) γ rfl rfl hinside
  rw [hcost] at h
  exact ENNReal.toReal_mono (Classical.setting_curve_cost_ne_top X ω γ) h

/-- Surgery at two parameters costs at most the endpoint distances times `b`, plus the
one-unit near-optimality error. The geometric part of the proof supplies `hinside` and `hfar`. -/
theorem slab_comparison_of_middle (X : Setting m) (ω : X.Ω) {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) {u v : Pt m} (hu : u ∈ sl.set) (hv : v ∈ sl.set)
    (γ : IsotropicVariance.RectifiableCurve (Pt m))
    (hγ : IsOneOptimal (X.ρ ω) univ u v γ) {a c : ℝ}
    (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1)
    (hinside : ∀ t ∈ Icc (0 : ℝ) 1, (γ.subcurve a c ha hac hc).toFun t ∈ sl.set)
    (hfar : ∀ t ∈ Icc (0 : ℝ) 1,
      1 < infDist ((γ.subcurve a c ha hac hc).toFun t) sl.faces) :
    X.slabTime b sl ω u v - X.passTime ω u v ≤
      b * (dist u (γ.toFun a) + dist v (γ.toFun c)) + 1 := by
  let δ := γ.subcurve a c ha hac hc
  have hmid := slabTime_le_curve_cost X ω b sl δ hinside hfar
  rw [γ.subcurve_start ha hac hc, γ.subcurve_end ha hac hc] at hmid
  have hLip := Infra.Slab.abs_slabTime_sub_le X hb sl ω hu hv
    (by simpa only [δ, γ.subcurve_start ha hac hc] using hinside 0 (by simp))
    (by simpa only [δ, γ.subcurve_end ha hac hc] using hinside 1 (by simp))
  have hfull := pieceCost_le_passTime_add_one X ω γ hγ (a := 0) (b := 1)
    le_rfl zero_le_one le_rfl
  rw [pieceCost_full, hγ.1, hγ.2.1] at hfull
  have hleft := pieceCost_add X ω γ (a := 0) (b := a) (c := c) le_rfl ha hac hc
  have hright := pieceCost_add X ω γ (a := 0) (b := c) (c := 1)
    le_rfl (ha.trans hac) hc le_rfl
  rw [pieceCost_full] at hright
  have h0 : 0 ≤ pieceCost X ω γ 0 a le_rfl ha (hac.trans hc) := ENNReal.toReal_nonneg
  have h1 : 0 ≤ pieceCost X ω γ c 1 (ha.trans hac) hc le_rfl := ENNReal.toReal_nonneg
  change X.slabTime b sl ω (γ.toFun a) (γ.toFun c) ≤ pieceCost X ω γ a c ha hac hc at hmid
  linarith [(abs_le.mp hLip).2]

end IsotropicVariance.Paper.Proofs.SlabComparison
