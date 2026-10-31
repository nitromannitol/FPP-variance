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
public import CurvatureVariance.Statements.Lattice.LatticeGraph
public import CurvatureVariance.Statements.Lattice.Vertex
public import CurvatureVariance.Statements.Lattice.WalkCost
public import CurvatureVariance.Statements.Percolation.BondCriticalProb
public import CurvatureVariance.Statements.Weights.IsIIDWeights
import CurvatureVariance.Infra.Kesten.Estimate

/-!
# Provider of `CurvatureVariance.measure_exists_isPath_walkCost_lt_le`

Proves `CurvatureVariance.Providers.measure_exists_isPath_walkCost_lt_le` with exactly the type of
the statement `CurvatureVariance.Statements.Inputs.MeasureExistsIsPathWalkCostLtLe`, from
`Infra.Kesten.measure_exists_isPath_walkCost_lt_le`. The statement is proved by `by exact` of this
theorem applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- **Kesten's estimate**, [Kes86, Proposition 5.8] (cited in Section `sec:prelim`), in the form of
[ADH, Theorem 4.6, in its proof, p. 77]: if `F(0) < p_c`, there are `a, C₉ > 0` such that for all
`n ≥ 1`,
`P(∃ self-avoiding γ starting at 0 with #γ ≥ n but with T(γ) < an) ≤ e^{−C₉ n}`. The constants
depend only on `d` and the law `F`. -/
theorem measure_exists_isPath_walkCost_lt_le {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (h0 : F {0} < ENNReal.ofReal (bondCriticalProb m)) :
    ∃ a C₉ : ℝ, 0 < a ∧ 0 < C₉ ∧ ∀ (P : Measure (Config m)) [IsProbabilityMeasure P],
      IsIIDWeights P F → ∀ n : ℕ, 1 ≤ n →
        P {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk 0 v),
            γ.IsPath ∧ n ≤ γ.length ∧ (walkCost ω γ : ℝ) < a * n} ≤
          ENNReal.ofReal (Real.exp (-(C₉ * n))) :=
  Infra.Kesten.measure_exists_isPath_walkCost_lt_le hm F h0

end CurvatureVariance.Providers
