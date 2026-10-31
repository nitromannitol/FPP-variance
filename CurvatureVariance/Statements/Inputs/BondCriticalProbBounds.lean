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
import CurvatureVariance.Providers.BondCriticalProbBounds

/-!
# `CurvatureVariance.bondCriticalProb_bounds`

A result the paper cites, stated with Mathlib and the definitions of this directory only, and proved
in this library: its proof is `CurvatureVariance.Providers.bondCriticalProb_bounds` applied to its
binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- Bounds on the critical probability of bond percolation on `ℤ^d`, `d = m + 1`:
`1/(2d) ≤ p_c(d) ≤ 1` (`φ_p({0}) = 2dp` [Duminil-Copin and Tassion, Remark 4], or path
counting). It makes (W) satisfiable for every `d`, for example by the law `δ_1`. -/
theorem bondCriticalProb_bounds (m : ℕ) :
    (2 * ((m : ℝ) + 1))⁻¹ ≤ bondCriticalProb m ∧ bondCriticalProb m ≤ 1 :=
  by exact CurvatureVariance.Providers.bondCriticalProb_bounds m

end CurvatureVariance
