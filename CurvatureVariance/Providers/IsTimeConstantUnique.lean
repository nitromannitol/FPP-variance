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
public import CurvatureVariance.Statements.Space.PtNorm
public import CurvatureVariance.Statements.TimeConstant.IsTimeConstant
import CurvatureVariance.Infra.FPP.TimeConstant

/-!
# Provider of `CurvatureVariance.IsTimeConstant.unique`

Proves `CurvatureVariance.Providers.IsTimeConstant.unique` with exactly the type of the statement
`CurvatureVariance.Statements.Companions.IsTimeConstantUnique`, from `Infra.FPP.isTimeConstant_unique`.
The statement is proved by `by exact` of this theorem applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- The time constant is unique: for every probability measure `P`, two norms with the
almost-sure limits of `T(0, nx)/n` at every `x ∈ ℤ^d` are equal. -/
theorem IsTimeConstant.unique {m : ℕ} {P : Measure (Config m)} [IsProbabilityMeasure P]
    {μ μ' : PtNorm m} (hμ : IsTimeConstant P μ) (hμ' : IsTimeConstant P μ') : μ = μ' :=
  Infra.FPP.isTimeConstant_unique hμ hμ'

end CurvatureVariance.Providers
