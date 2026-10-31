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
import CurvatureVariance.Infra.Percolation.Lattice

/-!
# Provider of `CurvatureVariance.IsIIDWeights.unique`

Proves `CurvatureVariance.Providers.IsIIDWeights.unique` with exactly the type of the statement
`CurvatureVariance.Statements.Companions.IsIIDWeightsUnique`, from
`Infra.FPP.IsIIDWeights.eq_infinitePi` (both laws are the product law; the probability instances
come from independence and from the law of one edge). The statement is proved by `by exact` of this
theorem applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- The weights determine their joint law: two laws of independent weights with the same law `F`
are equal. -/
theorem IsIIDWeights.unique {m : ℕ} {F : Measure ℝ≥0} {P P' : Measure (Config m)}
    (hP : IsIIDWeights P F) (hP' : IsIIDWeights P' F) : P = P' := by
  have hPp : IsProbabilityMeasure P := hP.1.isProbabilityMeasure
  have hP'p : IsProbabilityMeasure P' := hP'.1.isProbabilityMeasure
  have hadj : (latticeGraph m).Adj 0 (0 + Infra.Percolation.unitStep none true) :=
    Infra.Percolation.latticeGraph_adj_iff.2 ⟨none, true, rfl⟩
  have hF : IsProbabilityMeasure F := by
    rw [← (hP.2 ⟨s(0, _), hadj⟩).map_eq]
    infer_instance
  rw [Infra.FPP.IsIIDWeights.eq_infinitePi hP, Infra.FPP.IsIIDWeights.eq_infinitePi hP']

end CurvatureVariance.Providers
