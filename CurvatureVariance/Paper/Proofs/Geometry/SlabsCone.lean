/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.HitsIncrements
public import CurvatureVariance.Paper.Proofs.Geometry.SlabsGood
public import CurvatureVariance.Paper.Proofs.Geometry.SlabsAsymp
public import CurvatureVariance.Paper.Proofs.Geometry.TurningCones
public import CurvatureVariance.Paper.Proofs.Geometry.SupportAngular

/-!
# Lemma `lem:cone` on the events: the slope scale

`rpow_le_rpow_neg_of_sqrt_le`: at the scale `n ≥ √N`, `n^{δ/100−1/4} ≤ N^{-κ}` with
`κ = (1/4 − δ/100)/2`, so slope deviations `‖t − t₀‖ ≤ Cs n^{δ/100−1/4}` are small for `N` large.
Lemma `lem:cone` on the events is `coneStatement_of` (`Proofs.Geometry.Cone`): there the
deterministic cone bounds `cone_exit_bounds` apply with `L = 2 log N`, and the angular bound
centred at `t₀` comes from `SupportStatement` (`angularSupport_of_support`).
-/

@[expose] public section

open InnerProductGeometry
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- The slope bound at the scale `n ≥ √N`: `n^{δ/100−1/4} ≤ N^{-κ}`. -/
theorem rpow_le_rpow_neg_of_sqrt_le {δ : ℝ} (hδ : δ ≤ 1) {n N : ℝ} (hN : 0 < N)
    (hn : Real.sqrt N ≤ n) :
    n ^ (δ / 100 - 1 / 4) ≤ N ^ (-((1 / 4 - δ / 100) / 2)) := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  calc n ^ (δ / 100 - 1 / 4) ≤ Real.sqrt N ^ (δ / 100 - 1 / 4) :=
        Real.rpow_le_rpow_of_nonpos hs hn (by linarith)
    _ = N ^ (-((1 / 4 - δ / 100) / 2)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN.le]
        congr 1
        ring

end CurvatureVariance.Paper.Proofs.Geometry
