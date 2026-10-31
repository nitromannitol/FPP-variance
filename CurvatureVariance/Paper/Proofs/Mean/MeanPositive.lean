/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Mean.MeanFar
public import CurvatureVariance.Paper.Proofs.Mean.MeanScales
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp

/-!
# A hypothetical bias gives a uniformly positive mean profile

The deterministic implication in the proof of Lemma `lem:smallmean`, with
the choices of constants and all large-scale thresholds made explicit. The constants precede the
fitting model, `K`, `A`, and `N`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

/-- A supporting plane at the reference direction also touches the corresponding lattice target. -/
theorem inner_target_eq_of_isSubgradient {m : ℕ} {M : Model m} {s : ℕ} (hs : 0 < s)
    {y₀ : Fin m → ℤ} {t : EuclideanSpace ℝ (Fin m)} (hst : (s : ℝ) • t = transversePoint y₀)
    {p : Pt m} (hp : IsSubgradient M.μ (slopeVec t) p) :
    inner ℝ p (point ((s : ℤ), y₀)) = M.μ.1 (point ((s : ℤ), y₀)) := by
  have hpoint := point_target_eq_smul_slopeVec hs hst (0 : Fin m → ℤ)
  simp only [add_zero, transversePoint_zero, smul_zero] at hpoint
  rw [hpoint, inner_smul_right, map_smul_eq_mul,
    Real.norm_of_nonneg (Nat.cast_nonneg _), hp.1]

end CurvatureVariance.Paper.Mean
