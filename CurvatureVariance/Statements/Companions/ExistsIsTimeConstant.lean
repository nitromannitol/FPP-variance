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
public import CurvatureVariance.Statements.Weights.AssumptionW
public import CurvatureVariance.Statements.Weights.IsIIDWeights
import CurvatureVariance.Providers.ExistsIsTimeConstant

/-!
# `CurvatureVariance.exists_isTimeConstant`

A companion of the main theorem `CurvatureVariance.lintegral_exp_passageTime_le` (Theorem
`thm:main`), stated with Mathlib and the definitions of this directory only: it shows that a
hypothesis of the main theorem can be met, or that an object the hypotheses characterize is unique.
Its proof is `CurvatureVariance.Providers.exists_isTimeConstant` applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- **The time constant exists and is a norm** ([ADH, Theorems 2.1, 2.5 and 2.6, pp. 8–11], cited
in the introduction). Under (W), for first-passage percolation on `ℤ^d`,
`d = m + 1 ≥ 2`, the limit `T(0, nx)/n` exists almost surely for every `x ∈ ℤ^d` and extends to a
norm on `ℝ^d`. -/
theorem exists_isTimeConstant {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hW : AssumptionW m F) (P : Measure (Config m)) [IsProbabilityMeasure P]
    (hP : IsIIDWeights P F) :
    ∃ μ : PtNorm m, IsTimeConstant P μ :=
  by exact CurvatureVariance.Providers.exists_isTimeConstant hm F hW P hP

end CurvatureVariance
