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
import CurvatureVariance.Infra.FPP.Model

/-!
# Provider of `CurvatureVariance.exists_isIIDWeights`

Proves `CurvatureVariance.Providers.exists_isIIDWeights` with exactly the type of the statement
`CurvatureVariance.Statements.Companions.ExistsIsIIDWeights`, from `Infra.FPP.isIIDWeights_infinitePi`
(the product law). The statement is proved by `by exact` of this theorem applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- The weights exist: for every law `F` on `[0, ∞)` there is a law of the configuration under
which the weights are independent with law `F`. -/
theorem exists_isIIDWeights (m : ℕ) (F : Measure ℝ≥0) [IsProbabilityMeasure F] :
    ∃ P : Measure (Config m), IsProbabilityMeasure P ∧ IsIIDWeights P F :=
  ⟨Measure.infinitePi fun _ : Edge m => F, inferInstance, Infra.FPP.isIIDWeights_infinitePi F⟩

end CurvatureVariance.Providers
