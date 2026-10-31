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
import CurvatureVariance.Providers.IsTimeConstantUnique

/-!
# `CurvatureVariance.IsTimeConstant.unique`

A companion of the main theorem `CurvatureVariance.lintegral_exp_passageTime_le` (Theorem
`thm:main`), stated with Mathlib and the definitions of this directory only: it shows that a
hypothesis of the main theorem can be met, or that an object the hypotheses characterize is unique.
Its proof is `CurvatureVariance.Providers.IsTimeConstant.unique` applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- The time constant is unique: for every probability measure `P`, two norms with the
almost-sure limits of `T(0, nx)/n` at every `x ∈ ℤ^d` are equal. -/
theorem IsTimeConstant.unique {m : ℕ} {P : Measure (Config m)} [IsProbabilityMeasure P]
    {μ μ' : PtNorm m} (hμ : IsTimeConstant P μ) (hμ' : IsTimeConstant P μ') : μ = μ' :=
  by exact CurvatureVariance.Providers.IsTimeConstant.unique hμ hμ'

end CurvatureVariance
