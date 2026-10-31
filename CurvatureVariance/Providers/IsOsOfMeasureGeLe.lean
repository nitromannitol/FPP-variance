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
import CurvatureVariance.Infra.Os.Tail

/-!
# Provider of `CurvatureVariance.isOs_of_measure_ge_le`

Proves `CurvatureVariance.Providers.isOs_of_measure_ge_le` with exactly the type of the statement
`CurvatureVariance.Statements.Inputs.IsOsOfMeasureGeLe`, from `Infra.Os.isOs_of_tail`. The statement is
proved by `by exact` of this theorem applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- **[AKM, Lemma A.1], second implication**: for a random variable `X` and `s, θ ∈ (0, ∞)`, if
`P[X ≥ θx] ≤ exp(−x^s)` for all `x ≥ 0`, then `X ≤ O_s(2^{1/s} θ)`. -/
theorem isOs_of_measure_ge_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s θ : ℝ} {X : Ω → ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (hXm : AEMeasurable X P)
    (hX : ∀ x : ℝ, 0 ≤ x → P {ω | θ * x ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-(x ^ s)))) :
    IsOs P s ((2 : ℝ) ^ (1 / s) * θ) X :=
  Infra.Os.isOs_of_tail hs hθ hXm hX

end CurvatureVariance.Providers
