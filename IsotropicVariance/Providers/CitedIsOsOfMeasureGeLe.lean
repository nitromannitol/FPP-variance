/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import IsotropicVariance.Statements.Cited.IsOs
import IsotropicVariance.Infra.Os.Tail

/-!
# Proof of `IsotropicVariance.Cited.isOs_of_measure_ge_le`

Proves `IsotropicVariance.Providers.Cited.isOs_of_measure_ge_le`, with exactly the type of the
theorem `IsotropicVariance.Cited.isOs_of_measure_ge_le` stated in
`IsotropicVariance.Statements.Cited.IsOsOfMeasureGeLe`. The statement module proves its theorem from
this one and is not imported here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance.Providers
open IsotropicVariance.Cited

/-- [AKM, Lemma A.1 (Tail probability), p. 456], second implication: if
`P[X ≥ θx] ≤ exp(−x^s)` for every `x ≥ 0`, then `X ≤ O_s(2^{1/s} θ)`. -/
theorem Cited.isOs_of_measure_ge_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s θ : ℝ} (hs : 0 < s) (hθ : 0 < θ) {X : Ω → ℝ}
    (hX : AEMeasurable X P)
    (h : ∀ x : ℝ, 0 ≤ x → P {ω | θ * x ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-(x ^ s)))) :
    IsOs P s ((2 : ℝ) ^ (1 / s) * θ) X :=
  Infra.Os.isOs_of_tail hs hθ hX h

end IsotropicVariance.Providers
