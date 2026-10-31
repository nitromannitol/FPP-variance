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
import IsotropicVariance.Infra.Os.IntegralIntegrable

/-!
# Proof of `IsotropicVariance.Cited.isOs_integral_of_one_le`

Proves `IsotropicVariance.Providers.Cited.isOs_integral_of_one_le`, with exactly the type of the
theorem `IsotropicVariance.Cited.isOs_integral_of_one_le` stated in
`IsotropicVariance.Statements.Cited.IsOsIntegralOfOneLe`. The statement module proves its theorem from
this one and is not imported here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance.Providers
open IsotropicVariance.Cited

/-- [AKM, Lemma A.4, p. 457], second part: for `s ≥ 1` the constant is `C_s = 1` (the sum rule
for `s ≥ 1`, cited in Section `ssec:notation`). -/
theorem Cited.isOs_integral_of_one_le {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure E) {s : ℝ} (hs : 1 ≤ s) (θ : E → ℝ)
    (hθ : ∀ x, 0 < θ x) (hθm : Measurable θ) (hθi : Integrable θ μ) (X : E → Ω → ℝ)
    (hXm : Measurable (Function.uncurry X)) (hX0 : ∀ x ω, 0 ≤ X x ω)
    (hX : ∀ x, IsOs P s (θ x) (X x)) :
    (∀ᵐ ω ∂P, Integrable (fun x => X x ω) μ) ∧
      IsOs P s (∫ x, θ x ∂μ) (fun ω => ∫ x, X x ω ∂μ) :=
  by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have h := Infra.Os.isOs_integral P μ hs0 θ hθ hθm hθi X hXm hX0 hX
  simp only [Infra.Os.sumConstant, ite_eq_left hs, one_mul] at h
  exact ⟨Infra.Os.ae_integrable_of_isOs P μ hs0 θ hθ hθm hθi X hXm hX0 hX, h⟩

end IsotropicVariance.Providers
