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
import IsotropicVariance.Providers.CitedVarianceMulLogLeOfEntropyLe

/-!
# `IsotropicVariance.Cited.variance_mul_log_le_of_entropy_le`

One declaration of the statements of this formalization (`IsotropicVariance.Statements`): the
definitions, the results cited from the literature and the main theorems, one per file.

This file states a result from the literature, in the form the paper uses; its proof is
`IsotropicVariance.Providers.Cited.variance_mul_log_le_of_entropy_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance
namespace Cited

/-- **[BR, Proposition 2.1]**, the instance the paper applies (in the proof of Proposition
`prop:gain`): countably many independent coordinates with values in finite
sets, `Aᵢ = L²(µᵢ)` and `Rᵢ = √c (Id − Eᵢ)`. If every `µᵢ` satisfies
`Ent_{µᵢ}(g²) ≤ c Var_{µᵢ}(g)` (that is, `Ent_{µᵢ}(g²) ≤ E_{µᵢ}(Rᵢ g)²`), then for every
measurable `f ∈ L²(µ^I)` with `∑ᵢ ‖Δᵢ f‖₂² < ∞`,
`Var(f) log (Var(f) / ∑ᵢ ‖Δᵢ f‖₁²) ≤ c ∑ᵢ ‖Δᵢ f‖₂²`, which is `∑ᵢ E(Rᵢ f)²`.
Every premise of [BR] holds for these operators: they vanish on constants and commute with
integration over the other coordinates. -/
theorem variance_mul_log_le_of_entropy_le {ι : Type*} [Countable ι] [DecidableEq ι]
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
  by exact IsotropicVariance.Providers.Cited.variance_mul_log_le_of_entropy_le μ hc hLSI hfm hf hA

end Cited
end IsotropicVariance
