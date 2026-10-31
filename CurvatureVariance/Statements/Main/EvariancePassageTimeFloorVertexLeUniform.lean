/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Probability.Moments.Variance
public import CurvatureVariance.Statements.Curvature.AssumptionCWith
public import CurvatureVariance.Statements.Lattice.Config
public import CurvatureVariance.Statements.Lattice.Edge
public import CurvatureVariance.Statements.Lattice.PassageTime
public import CurvatureVariance.Statements.Lattice.Vertex
public import CurvatureVariance.Statements.Space.FloorVertex
public import CurvatureVariance.Statements.Space.Pt
public import CurvatureVariance.Statements.Space.PtNorm
public import CurvatureVariance.Statements.TimeConstant.IsTimeConstant
public import CurvatureVariance.Statements.Weights.AssumptionW
public import CurvatureVariance.Statements.Weights.IsIIDWeights
import CurvatureVariance.Providers.EvariancePassageTimeFloorVertexLeUniform

/-!
# `CurvatureVariance.evariance_passageTime_floorVertex_le_uniform`

A corollary of Theorem `thm:main` of the paper (`CurvatureVariance.lintegral_exp_passageTime_le`),
through the variance bound that follows the theorem, stated with Mathlib and the definitions of this
directory only. Its proof is
`CurvatureVariance.Providers.evariance_passageTime_floorVertex_le_uniform` applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- **A corollary of Theorem `thm:main`: the variance at `⌊nξ⌋`, uniform in the direction.** Let the
weights of first-passage percolation on `ℤ^d`, `d = m + 1 ≥ 2`, be independent with common law `F`
satisfying (W), and let `μ` be the time constant. For all constants `δ ∈ (0, 1]`, `r > 0`, `M ≥ 0`
and `c > 0` there are `ε > 0` and `n₀` such that, for every unit direction `ξ` at which (Curv) holds
with these constants, `Var T(0, ⌊nξ⌋) ≤ n^{1-ε}` for every integer `n ≥ n₀`. The exponent and the
threshold depend only on `d`, `F`, `δ`, `r`, `M` and `c`, not on the direction. The paper writes `Λ`
for `M` and `λ` for `c` (`AssumptionCWith`). -/
theorem evariance_passageTime_floorVertex_le_uniform {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (P : Measure (Config m))
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) (μ : PtNorm m) (hμ : IsTimeConstant P μ)
    (δ r M c : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ ξ : Pt m, ‖ξ‖ = 1 → AssumptionCWith μ ξ δ r M c →
      ∀ n : ℕ, n₀ ≤ n →
        evariance (fun ω => (passageTime ω 0 (floorVertex ((n : ℝ) • ξ)) : ℝ)) P ≤
          ENNReal.ofReal ((n : ℝ) ^ (1 - ε)) :=
  by exact CurvatureVariance.Providers.evariance_passageTime_floorVertex_le_uniform hm F hW P hP μ hμ δ r M c hδ hδ₁ hr hM hc

end CurvatureVariance
