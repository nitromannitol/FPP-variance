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
public import CurvatureVariance.Statements.Percolation.BondCriticalProb
import CurvatureVariance.Infra.Percolation.LatticeSharpness

/-!
# Provider of `CurvatureVariance.bondCriticalProb_pos`

Proves `CurvatureVariance.Providers.bondCriticalProb_pos` with exactly the type of the statement
`CurvatureVariance.Statements.Companions.BondCriticalProbPos`, from
`Infra.Percolation.bondCriticalProb_pos`. The statement is proved by `by exact` of this theorem
applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- The critical probability of bond percolation on `ℤ^d`, `d ≥ 2`, is positive, so (W) is
satisfiable (for example by the law `δ_1`). -/
theorem bondCriticalProb_pos {m : ℕ} (hm : 1 ≤ m) : 0 < bondCriticalProb m :=
  Infra.Percolation.bondCriticalProb_pos hm

end CurvatureVariance.Providers
