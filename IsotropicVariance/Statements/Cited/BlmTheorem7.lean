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
public import IsotropicVariance.Statements.Cited.VPlus
import IsotropicVariance.Providers.CitedBlmTheorem7

/-!
# `IsotropicVariance.Cited.blm_theorem7`

One declaration of the statements of this formalization (`IsotropicVariance.Statements`): the
definitions, the results cited from the literature and the main theorems, one per file.

This file states a result from the literature, in the form the paper uses; its proof is
`IsotropicVariance.Providers.Cited.blm_theorem7`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance
namespace Cited

/-- [BLM, Theorem 7, p. 1587] (used in the proof of Lemma `lem:classical`), in a form sufficient for
the paper, which does not specify `K`: `K = 1`, where `ψ(1)/1² = e − 1` ([BLM, Proposition 10, p.
1588]: `ψ(x) = x(eˣ − 1)`), and a nonnegative nondecreasing `g` (in BLM, `V₊ ≤ g(Z)` holds in the
reals and `V₊ ≥ 0`). If `V₊ ≤ g(Z)` almost surely and `|Z − Z^{(i)}| ≤ 1` for every value of `X` and
of the copy, then for all `λ ∈ [0, 1)`, `log E exp(−λ(Z − EZ)) ≤ λ² (e − 1) E g(Z)` (the exponential
moment being finite), and for all `0 < t ≤ (e − 1) E g(Z)`,
`P[Z < EZ − t] ≤ exp(−t²/(4(e − 1) E g(Z)))`. BLM state the first bound for all `K > 0` and
`λ ∈ [0, 1/K)`; this statement is the case `K = 1`, the case the paper uses. -/
theorem blm_theorem7 {n : ℕ} {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Fin n → Measure 𝒳)
    [∀ i, IsProbabilityMeasure (μ i)] (f : (Fin n → 𝒳) → ℝ) (hf : Measurable f)
    (hfi : Integrable f (Measure.pi μ)) (g : ℝ → ℝ) (hg : Monotone g) (hg0 : ∀ z, 0 ≤ g z)
    (hgi : Integrable (fun x => g (f x)) (Measure.pi μ))
    (hV : ∀ᵐ x ∂Measure.pi μ, vPlus μ f x ≤ ENNReal.ofReal (g (f x)))
    (hdiff : ∀ (x : Fin n → 𝒳) (i : Fin n) (y : 𝒳), |f x - f (Function.update x i y)| ≤ 1) :
    (∀ l : ℝ, 0 ≤ l → l < 1 →
        Integrable (fun x => Real.exp (-l * (f x - ∫ z, f z ∂Measure.pi μ)))
          (Measure.pi μ) ∧
        Real.log (∫ x, Real.exp (-l * (f x - ∫ z, f z ∂Measure.pi μ)) ∂Measure.pi μ) ≤
          l ^ 2 * (Real.exp 1 - 1) * ∫ x, g (f x) ∂Measure.pi μ) ∧
      ∀ t : ℝ, 0 < t → t ≤ (Real.exp 1 - 1) * ∫ x, g (f x) ∂Measure.pi μ →
        Measure.pi μ {x | f x < (∫ z, f z ∂Measure.pi μ) - t} ≤
          ENNReal.ofReal (Real.exp (-(t ^ 2 /
            (4 * (Real.exp 1 - 1) * ∫ x, g (f x) ∂Measure.pi μ)))) :=
  by exact IsotropicVariance.Providers.Cited.blm_theorem7 μ f hf hfi g hg hg0 hgi hV hdiff

end Cited
end IsotropicVariance
