/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SmallMean.PairEstimate
public import IsotropicVariance.Paper.Proofs.SmallMean.ChainIntegral

/-!
# Lemma `lem:smallmean`: the mean slab passage time

* `integrable_slabTime_of_mem`, `continuousOn_mean_slabTime`: the mean slab passage time is finite
  and continuous in the endpoints.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.SmallMean

open Infra.Slab

variable {m : ℕ}

/-- Slab passage times between points of the slab are integrable. -/
theorem integrable_slabTime_of_mem (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m)
    {u v : Pt m} (hu : u ∈ sl.set) (hv : v ∈ sl.set) :
    Integrable (fun ω => X.slabTime b sl ω u v) X.P := by
  refine Integrable.mono' (integrable_const (b * dist u v))
    (aemeasurable_slabTime X hb _ u v).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (slabTime_nonneg X b _ ω u v)]
  exact slabTime_le_mul_dist X hb _ ω hu hv

/-- The mean slab passage time is continuous on pairs of points of the slab. -/
theorem continuousOn_mean_slabTime (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) :
    ContinuousOn (fun x : Pt m × Pt m => ∫ ω, X.slabTime b sl ω x.1 x.2 ∂X.P)
      (sl.set ×ˢ sl.set) := by
  have hb0 : 0 ≤ b := by
    obtain ⟨ω⟩ : Nonempty X.Ω := nonempty_of_isProbabilityMeasure X.P
    exact upperBound_nonneg X hb ω
  refine (LipschitzOnWith.of_dist_le_mul (K := (2 * b).toNNReal) fun x hx y hy => ?_).continuousOn
  rw [Real.dist_eq, ← integral_sub (integrable_slabTime_of_mem X hb sl hx.1 hx.2)
    (integrable_slabTime_of_mem X hb sl hy.1 hy.2)]
  refine (abs_integral_le_integral_abs).trans ?_
  have hle : ∀ ω, |X.slabTime b sl ω x.1 x.2 - X.slabTime b sl ω y.1 y.2| ≤ 2 * b * dist x y :=
    fun ω => (abs_slabTime_sub_le X hb sl ω hx.1 hx.2 hy.1 hy.2).trans (by
      have h1 : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
      have h2 : dist x.2 y.2 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _
      nlinarith)
  calc ∫ ω, |X.slabTime b sl ω x.1 x.2 - X.slabTime b sl ω y.1 y.2| ∂X.P
      ≤ ∫ _ω, 2 * b * dist x y ∂X.P := integral_mono
        ((integrable_slabTime_of_mem X hb sl hx.1 hx.2).sub
          (integrable_slabTime_of_mem X hb sl hy.1 hy.2)).abs (integrable_const _) hle
    _ = (2 * b).toNNReal * dist x y := by
        rw [integral_const, probReal_univ, one_smul, Real.coe_toNNReal _ (by positivity)]

end IsotropicVariance.Paper.Proofs.SmallMean
