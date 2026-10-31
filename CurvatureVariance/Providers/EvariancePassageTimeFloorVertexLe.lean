/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Probability.Moments.Variance
public import CurvatureVariance.Statements.Curvature.AssumptionCAt
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
import CurvatureVariance.Paper.Closing.Main

/-!
# Provider of `CurvatureVariance.evariance_passageTime_floorVertex_le`

The provider of the theorem at one direction
`CurvatureVariance.evariance_passageTime_floorVertex_le` (not in the paper):
`CurvatureVariance.Providers.evariance_passageTime_floorVertex_le` has exactly its type, and its
proof is `CurvatureVariance.Paper.Closing.evariance_passageTime_floorVertex_le` applied to the
binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- **The variance bound at one direction** (not in the paper). Let the weights of first-passage
percolation on `ℤ^d`, `d = m + 1 ≥ 2`, be independent with common law `F` (law `P` of the
configuration), and assume (W). Let `μ` be the time constant, `ξ ∈ ℝ^d` a nonzero direction and `H`
a linear hyperplane transverse to it, `ℝ^d = ℝξ ⊕ H`, and assume the expansion `AssumptionCAt` of
`μ` at `ξ` along `H`. Then there are `ε > 0` and `n₀`, depending on the direction, such that
`Var T(0, ⌊nξ⌋) ≤ n^{1-ε}` for every integer `n ≥ n₀`, where `⌊nξ⌋` is the coordinatewise floor. A
unit `ξ` at which (Curv) holds satisfies these hypotheses with `H = ξ^⊥`. The results the paper
cites are proved in this library. -/
theorem evariance_passageTime_floorVertex_le {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (P : Measure (Config m))
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) (μ : PtNorm m) (hμ : IsTimeConstant P μ)
    (ξ : Pt m) (hξ : ξ ≠ 0) (H : Submodule ℝ (Pt m)) (hH : IsCompl (Submodule.span ℝ {ξ}) H)
    (hC : AssumptionCAt μ ξ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      evariance (fun ω => (passageTime ω 0 (floorVertex ((n : ℝ) • ξ)) : ℝ)) P ≤
        ENNReal.ofReal ((n : ℝ) ^ (1 - ε)) :=
  CurvatureVariance.Paper.Closing.evariance_passageTime_floorVertex_le
    hm F hW P hP μ hμ ξ hξ H hH hC

end CurvatureVariance.Providers
