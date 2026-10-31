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
public import CurvatureVariance.Statements.Weights.AssumptionW
public import CurvatureVariance.Statements.Weights.IsIIDWeights
import CurvatureVariance.Providers.TimeConstantPos

/-!
# `CurvatureVariance.timeConstant_pos`

A result the paper cites, stated with Mathlib and the definitions of this directory only, and proved
in this library: its proof is `CurvatureVariance.Providers.timeConstant_pos` applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- **[ADH, Theorem 2.5]**, specialized to (W) and to the direction `e₁`: if `F(0) < p_c(d)`, the
time constant `µ(e₁)` is positive. -/
theorem timeConstant_pos {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hW : AssumptionW m F) (P : Measure (Config m)) [IsProbabilityMeasure P]
    (hP : IsIIDWeights P F) (μ₁ : ℝ)
    (hμ₁ : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (passageTime ω 0 ((n : ℤ), 0) : ℝ) / n) atTop (𝓝 μ₁)) :
    0 < μ₁ :=
  by exact CurvatureVariance.Providers.timeConstant_pos hm F hW P hP μ₁ hμ₁

end CurvatureVariance
