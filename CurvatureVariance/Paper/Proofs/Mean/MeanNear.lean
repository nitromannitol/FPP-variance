/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Mean.MeanExcess
public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Contracts.Geometry
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The modulus of the mean after subtracting its supporting plane

The expectation step in the proof of Lemma `lem:smallmean`: the `L^{8d}`
modulus gives a uniform deterministic modulus for the mean profile on a ball of radius `h W_s`,
with `h` independent of `K`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

/-- The distance between two vertices on the same face is their transverse Euclidean distance. -/
theorem norm_point_same_face_sub {m : ℕ} (s : ℤ) (y z : Fin m → ℤ) :
    ‖point (s, y + z) - point (s, y)‖ = ‖transversePoint z‖ := by
  rw [← point_sub]
  have heq : (s, y + z) - (s, y) = ((0 : ℤ), z) := by ext <;> simp
  rw [heq]
  have hh := norm_point_sq ((0 : ℤ), z)
  simp only [Int.cast_zero, zero_pow two_ne_zero, zero_add] at hh
  nlinarith only [hh, norm_nonneg (point ((0 : ℤ), z)), norm_nonneg (transversePoint z)]

end CurvatureVariance.Paper.Mean
