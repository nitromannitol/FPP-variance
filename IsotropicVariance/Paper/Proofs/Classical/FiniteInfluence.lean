/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.Approximation
public import IsotropicVariance.Paper.Proofs.Classical.GridFinite

/-! # Deterministic bounded localization of near-optimal competitors -/

@[expose] public section
open Set Metric MeasureTheory
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra IsotropicVariance.Infra.WhiteNoise

/-- The entire curve stays within its length of its initial point. -/
theorem dist_start_le_curve_length {E : Type*} [MetricSpace E]
    (γ : RectifiableCurve E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (γ.toFun t) (γ.toFun 0) ≤ γ.length.toReal := by
  have hh : edist (γ.toFun t) (γ.toFun 0) ≤ γ.length :=
    eVariationOn.edist_le γ.toFun ht (by simp)
  have hh' := ENNReal.toReal_mono γ.length_ne_top hh
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using hh'

/-- Ellipticity confines all competitors with error at most one to a fixed
ball. The ball does not depend on the noise realization. -/
theorem nearoptimal_mem_closedBall {m : ℕ} (X : Setting m) {a b : ℝ} (ha : 0 < a)
    (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b) (ω : X.Ω)
    (γ : RectifiableCurve (Pt m)) {ε : ℝ} (hε : ε ≤ 1)
    (hNear : (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal ≤
      X.passTime ω (γ.toFun 0) (γ.toFun 1) + ε)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    γ.toFun t ∈ closedBall (γ.toFun 0)
      ((b * dist (γ.toFun 0) (γ.toFun 1) + 1) / a) := by
  have hLow := ENNReal.toReal_mono (setting_curve_cost_ne_top X ω γ)
    (γ.mul_length_le_cost (fun x => ENNReal.ofReal_le_ofReal (hBounds ω x).1))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le] at hLow
  have hUp : X.passTime ω (γ.toFun 0) (γ.toFun 1) ≤
      b * dist (γ.toFun 0) (γ.toFun 1) :=
    (TimeConstant.passage_bounds ha.le (hBounds ω) (γ.toFun 0) (γ.toFun 1)).2
  have hLen : γ.length.toReal ≤ (b * dist (γ.toFun 0) (γ.toFun 1) + 1) / a := by
    apply (le_div_iff₀ ha).mpr
    linarith only [hLow, hNear, hUp, hε]
  exact (dist_start_le_curve_length γ ht).trans hLen

/-- Only finitely many enlarged cells can meet any such competitor. -/
theorem finite_nearoptimal_grid_family {m : ℕ} (u : Pt m) (R : ℝ) :
    {z : Coord (Pt m) → ℤ | ∃ x ∈ closedBall u R, x ∈ gridNeighborhood z}.Finite :=
  finite_gridNeighborhood_meets isBounded_closedBall

end IsotropicVariance.Paper.Proofs.Classical
