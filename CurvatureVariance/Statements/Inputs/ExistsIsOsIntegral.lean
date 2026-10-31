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
public import CurvatureVariance.Statements.Inputs.IsOs
import CurvatureVariance.Providers.ExistsIsOsIntegral

/-!
# `CurvatureVariance.exists_isOs_integral`

A result the paper cites, stated with Mathlib and the definitions of this directory only, and proved
in this library: its proof is `CurvatureVariance.Providers.exists_isOs_integral` applied to its
binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- **[AKM, Lemma A.4]**: for each `s ∈ (0, ∞)` there is `C_s < ∞`, with `C_s = 1` for `s ≥ 1`,
such that for a measure `ν` on a measurable space `E`, a measurable `θ : E → (0, ∞)` and a jointly
measurable family `(X(x))_{x∈E}` of nonnegative random variables with `X(x) ≤ O_s(θ(x))` for every
`x`, `∫ X dν ≤ O_s(C_s ∫ θ dν)`. The scale `∫ θ dν` is finite ([AKM]'s proof: "without loss of
generality `∫ θ dµ < ∞`"; for an infinite scale the statement is empty). -/
theorem exists_isOs_integral {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ (1 ≤ s → C = 1) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {E : Type*} [MeasurableSpace E] (ν : Measure E) (θ : E → ℝ),
        (∀ x, 0 < θ x) → Measurable θ → Integrable θ ν → ∀ X : E → Ω → ℝ,
        Measurable (Function.uncurry X) → (∀ x ω, 0 ≤ X x ω) → (∀ x, IsOs P s (θ x) (X x)) →
        IsOs P s (C * ∫ x, θ x ∂ν) (fun ω => ∫ x, X x ω ∂ν) :=
  by exact CurvatureVariance.Providers.exists_isOs_integral hs

end CurvatureVariance
