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
import CurvatureVariance.Providers.IsOsMeasureGeLe

/-!
# `CurvatureVariance.IsOs.measure_ge_le`

A result the paper cites, stated with Mathlib and the definitions of this directory only, and proved
in this library: its proof is `CurvatureVariance.Providers.IsOs.measure_ge_le` applied to its
binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- **[AKM, Lemma A.1], first implication** (cited through [AB26, Section 1.3] in Section
`ssec:notation`): for a random variable `X` and `s, θ ∈ (0, ∞)`, `X ≤ O_s(θ)` implies
`P[X ≥ θx] ≤ 2 exp(−x^s)` for all `x ≥ 0`. -/
theorem IsOs.measure_ge_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s θ : ℝ} {X : Ω → ℝ} (hX : IsOs P s θ X) (hs : 0 < s) (hθ : 0 < θ)
    {x : ℝ} (hx : 0 ≤ x) :
    P {ω | θ * x ≤ X ω} ≤ ENNReal.ofReal (2 * Real.exp (-(x ^ s))) :=
  by exact CurvatureVariance.Providers.IsOs.measure_ge_le hX hs hθ hx

end CurvatureVariance
