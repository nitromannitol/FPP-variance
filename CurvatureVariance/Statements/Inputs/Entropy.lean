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

/-!
# `CurvatureVariance.entropy`

One of the definitions in which the statements of this library are written: the main theorem
`CurvatureVariance.lintegral_exp_passageTime_le` (Theorem `thm:main`), its corollary
`CurvatureVariance.evariance_passageTime_floorVertex_le_uniform`, the theorem at one direction
`CurvatureVariance.evariance_passageTime_floorVertex_le`, the results the paper cites and their
companions. Each statement and each definition is in a file of its own, and depends only on Mathlib
and on these definitions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- The entropy `Ent_μ(g) = ∫ g log g dμ − (∫ g dμ) log (∫ g dμ)` of a function `g` (meant to be
nonnegative), with `0 log 0 = 0` ([BR, p. 546]). -/
noncomputable def entropy {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) : ℝ :=
  ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

end CurvatureVariance
