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
public import CurvatureVariance.Statements.Lattice.PassageTime
public import CurvatureVariance.Statements.Lattice.Vertex
public import CurvatureVariance.Statements.Lattice.WalkCost
public import CurvatureVariance.Statements.Percolation.BondCriticalProb
public import CurvatureVariance.Statements.Weights.IsIIDWeights
import CurvatureVariance.Infra.Geodesics.Basic

/-!
# Provider of `CurvatureVariance.ae_exists_isPath_walkCost_eq_passageTime`

Proves `CurvatureVariance.Providers.ae_exists_isPath_walkCost_eq_passageTime` with exactly the type
of the statement `CurvatureVariance.Statements.Inputs.AeExistsIsPathWalkCostEqPassageTime`, from
`Infra.Geodesics.ae_exists_isPath_walkCost_eq_passageTime`. The statement is proved by `by exact` of
this theorem applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- **[ADH, Proposition 4.4]** (cited in Section `sec:prelim`), in the combined form of parts 1
and 2: if `F(0) < p_c`, then almost surely, for all `u, v ∈ ℤ^d`, a geodesic from `u` to `v`
exists, a simple path whose passage time is `T(u, v)`. -/
theorem ae_exists_isPath_walkCost_eq_passageTime {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (h0 : F {0} < ENNReal.ofReal (bondCriticalProb m))
    (P : Measure (Config m)) [IsProbabilityMeasure P] (hP : IsIIDWeights P F) :
    ∀ᵐ ω ∂P, ∀ u v : Vertex m, ∃ γ : (latticeGraph m).Walk u v,
      γ.IsPath ∧ walkCost ω γ = passageTime ω u v :=
  Infra.Geodesics.ae_exists_isPath_walkCost_eq_passageTime hm F h0 P hP

end CurvatureVariance.Providers
