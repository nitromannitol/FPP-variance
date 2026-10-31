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
public import CurvatureVariance.Statements.Weights.IsIIDWeights
import CurvatureVariance.Providers.IsIIDWeightsUnique

/-!
# `CurvatureVariance.IsIIDWeights.unique`

A companion of the main theorem `CurvatureVariance.lintegral_exp_passageTime_le` (Theorem
`thm:main`), stated with Mathlib and the definitions of this directory only: it shows that a
hypothesis of the main theorem can be met, or that an object the hypotheses characterize is unique.
Its proof is `CurvatureVariance.Providers.IsIIDWeights.unique` applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- The weights determine their joint law: two laws of independent weights with the same law `F`
are equal. -/
theorem IsIIDWeights.unique {m : ℕ} {F : Measure ℝ≥0} {P P' : Measure (Config m)}
    (hP : IsIIDWeights P F) (hP' : IsIIDWeights P' F) : P = P' :=
  by exact CurvatureVariance.Providers.IsIIDWeights.unique hP hP'

end CurvatureVariance
