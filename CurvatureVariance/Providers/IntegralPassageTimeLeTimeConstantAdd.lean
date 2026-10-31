/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.SetBernoulli
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import CurvatureVariance.Statements.Lattice.Config
public import CurvatureVariance.Statements.Lattice.Edge
public import CurvatureVariance.Statements.Lattice.PassageTime
public import CurvatureVariance.Statements.Lattice.Vertex
public import CurvatureVariance.Statements.Space.Point
public import CurvatureVariance.Statements.Space.Pt
public import CurvatureVariance.Statements.Space.PtNorm
public import CurvatureVariance.Statements.TimeConstant.IsTimeConstant
public import CurvatureVariance.Statements.Weights.AssumptionW
public import CurvatureVariance.Statements.Weights.IsIIDWeights
import CurvatureVariance.Infra.FPP.Statements

/-!
# Provider of `CurvatureVariance.integral_passageTime_le_timeConstant_add`

Proves `CurvatureVariance.Providers.integral_passageTime_le_timeConstant_add` with exactly the type
of the statement `CurvatureVariance.Statements.Inputs.IntegralPassageTimeLeTimeConstantAdd`, from
`Infra.FPP.integral_passageTime_le_timeConstant_add`. The statement is proved by `by exact` of this
theorem applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- **[ADH, Theorem 3.33]**, specialized to (W) (cited in Section `sec:prelim` for the second bound
of equation `eq:classical`): there is `C = C(F, d)` such that
`µ(x) ≤ E T(0,x) ≤ µ(x) + C (|x| log |x|)^{1/2}` for all `x ∈ ℤ^d` with `|x| > 1`, `|x|` the
Euclidean norm. -/
theorem integral_passageTime_le_timeConstant_add {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Config m)) [IsProbabilityMeasure P],
      IsIIDWeights P F → ∀ μ : PtNorm m, IsTimeConstant P μ → ∀ x : Vertex m, 1 < ‖point x‖ →
        μ.1 (point x) ≤ ∫ ω, (passageTime ω 0 x : ℝ) ∂P ∧
          ∫ ω, (passageTime ω 0 x : ℝ) ∂P ≤
            μ.1 (point x) + C * √(‖point x‖ * Real.log ‖point x‖) :=
  Infra.FPP.integral_passageTime_le_timeConstant_add hm F hW

end CurvatureVariance.Providers
