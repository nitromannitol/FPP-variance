/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Mean.MeanScales
public import CurvatureVariance.Paper.Contracts.Moments
import Mathlib.Tactic.FieldSimp

/-!
# The rounded row-width margin

The deterministic width hypothesis used by the lower array estimate follows from the first bound
of equation `eq:scales`, uniformly over all lengths in Lemma `lem:smallmean`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

/-- The rounded width is positive and its square dominates `s Q_s`. -/
theorem mean_wInt_bounds {m : ℕ} {M : Model m} (hM : M.Standing)
    {K : ℕ} (hK : 10 ^ 4 ≤ K) {A s : ℝ} (hA : 1 ≤ A) (hs : 1 ≤ s) :
    0 < wInt M K A s ∧ s * Q M K A s ≤ (wInt M K A s : ℝ) ^ 2 := by
  have hQ1 : 1 ≤ Q M K A s :=
    (Real.one_le_rpow hs (by norm_num : (0 : ℝ) ≤ 49 / 100)).trans (mean_Q_lower hM hK hA hs)
  have hW1 : 1 ≤ W M K A s := by
    rw [W, Real.one_le_sqrt]
    exact one_le_mul_of_one_le_of_one_le hs hQ1
  have hw : W M K A s ≤ (wInt M K A s : ℝ) := Nat.le_ceil _
  constructor
  · have hw1 : (1 : ℝ) ≤ wInt M K A s := hW1.trans hw
    have hh : 1 ≤ wInt M K A s := by exact_mod_cast hw1
    omega
  · have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg (s * Q M K A s)) hw 2
    rw [Real.sq_sqrt (mul_nonneg (by linarith only [hs]) (zero_le_one.trans hQ1))] at hsq
    exact hsq

end CurvatureVariance.Paper.Mean
