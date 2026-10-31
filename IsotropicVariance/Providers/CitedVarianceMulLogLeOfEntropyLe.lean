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
public import IsotropicVariance.Statements.Cited.CoordDiff
public import IsotropicVariance.Statements.Cited.Entropy
import IsotropicVariance.Infra.Entropy.Instance

/-!
# Proof of `IsotropicVariance.Cited.variance_mul_log_le_of_entropy_le`

Proves `IsotropicVariance.Providers.Cited.variance_mul_log_le_of_entropy_le`, with exactly the type
of the theorem `IsotropicVariance.Cited.variance_mul_log_le_of_entropy_le` stated in
`IsotropicVariance.Statements.Cited.VarianceMulLogLeOfEntropyLe`. The statement module proves its
theorem from this one and is not imported here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance.Providers
open IsotropicVariance.Cited

/-- **[BR, Proposition 2.1]**, the instance the paper applies (cited in the proof of Proposition
`prop:gain`): countably many independent coordinates with values in finite sets, `Aᵢ = L²(µᵢ)` and
`Rᵢ = √c (Id − Eᵢ)`. If every `µᵢ` satisfies `Ent_{µᵢ}(g²) ≤ c Var_{µᵢ}(g)` (that is, `Ent_{µᵢ}(g²)
≤ E_{µᵢ}(Rᵢ g)²`), then for every measurable `f ∈ L²(µ^I)` with `∑ᵢ ‖Δᵢ f‖₂² < ∞`,
`Var(f) log (Var(f) / ∑ᵢ ‖Δᵢ f‖₁²) ≤ c ∑ᵢ ‖Δᵢ f‖₂²`, which is `∑ᵢ E(Rᵢ f)²`.
Every premise of [BR] holds for these operators: they vanish on constants and commute with
integration over the other coordinates. -/
theorem Cited.variance_mul_log_le_of_entropy_le {ι : Type*} [Countable ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, MeasurableSingletonClass (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] {c : ℝ} (hc : 0 ≤ c)
    (hLSI : ∀ i (g : X i → ℝ), entropy (μ i) (fun y => g y ^ 2) ≤ c * variance g (μ i))
    {f : (∀ i, X i) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (Measure.infinitePi μ))
    (hA : Summable fun i => ∫ x, coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ) :
    variance f (Measure.infinitePi μ) *
        Real.log (variance f (Measure.infinitePi μ) /
          ∑' i, (∫ x, |coordDiff μ i f x| ∂Measure.infinitePi μ) ^ 2) ≤
      c * ∑' i, ∫ x, coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ :=
  Infra.Entropy.br_instance_of_coordinate_lsi (μ := μ) hc hLSI hfm hf hA

end IsotropicVariance.Providers
