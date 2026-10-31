/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Mean.MeanNear
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Tactic.FieldSimp

/-!
# The quadratic lower bound for the mean profile

The far bound in the proof of Lemma `lem:smallmean` is the lower half of the
support estimate, equation `eq:support`, rescaled from longitudinal length one to length `s`,
combined with `E T ≥ μ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

/-- The lattice target as a positive multiple of its direction. -/
theorem point_target_eq_smul_slopeVec {m : ℕ} {s : ℕ} (hs : 0 < s)
    {y₀ : Fin m → ℤ} {t : EuclideanSpace ℝ (Fin m)}
    (hst : (s : ℝ) • t = transversePoint y₀) (z : Fin m → ℤ) :
    point ((s : ℤ), y₀ + z) = (s : ℝ) • slopeVec (t + (s : ℝ)⁻¹ • transversePoint z) := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  apply pt_ext
  · change (s : ℝ) = (s : ℝ) * 1
    ring
  · change transversePoint (y₀ + z) = (s : ℝ) • (t + (s : ℝ)⁻¹ • transversePoint z)
    rw [smul_add, hst, smul_inv_smul₀ hs0, transversePoint_add]

end CurvatureVariance.Paper.Mean
