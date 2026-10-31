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
import CurvatureVariance.Infra.FPP.Statements

/-!
# Provider of `CurvatureVariance.exists_tendsto_passageTime_div`

Proves `CurvatureVariance.Providers.exists_tendsto_passageTime_div` with exactly the type of the
statement `CurvatureVariance.Statements.Inputs.ExistsTendstoPassageTimeDiv`, from
`Infra.FPP.exists_tendsto_passageTime_div`. The statement is proved by `by exact` of this theorem
applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- **[ADH, Theorem 2.1]**, specialized to (W): there is a constant `µ(e₁) ∈ [0, ∞)`, the
time constant, such that `T(0, ne₁)/n → µ(e₁)` almost surely and in `L¹`. -/
theorem exists_tendsto_passageTime_div {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (P : Measure (Config m))
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) :
    ∃ μ₁ : ℝ, 0 ≤ μ₁ ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (passageTime ω 0 ((n : ℤ), 0) : ℝ) / n) atTop (𝓝 μ₁)) ∧
      Tendsto (fun n : ℕ => ∫ ω, |(passageTime ω 0 ((n : ℤ), 0) : ℝ) / n - μ₁| ∂P) atTop
        (𝓝 0) :=
  Infra.FPP.exists_tendsto_passageTime_div hm F hW P hP

end CurvatureVariance.Providers
