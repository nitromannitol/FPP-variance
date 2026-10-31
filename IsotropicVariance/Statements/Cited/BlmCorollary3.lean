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
public import IsotropicVariance.Statements.Cited.VMinus
public import IsotropicVariance.Statements.Cited.VPlus
import IsotropicVariance.Providers.CitedBlmCorollary3

/-!
# `IsotropicVariance.Cited.blm_corollary3`

One declaration of the statements of this formalization (`IsotropicVariance.Statements`): the
definitions, the results cited from the literature and the main theorems, one per file.

This file states a result from the literature, in the form the paper uses; its proof is
`IsotropicVariance.Providers.Cited.blm_corollary3`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance
namespace Cited

/-- [BLM, Corollary 3, p. 1585] (used in the proof of Lemma `lem:classical`): for
`Z = f(X₁, …, X_n)` with independent coordinates, if `V₊ ≤ c` almost surely then
`P[Z > EZ + t] ≤ e^{−t²/4c}` for every `t > 0`; if `V₋ ≤ c` almost surely then
`P[Z < EZ − t] ≤ e^{−t²/4c}`. (`f` is measurable, and integrable since `EZ` appears.) -/
theorem blm_corollary3 {n : ℕ} {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Fin n → Measure 𝒳)
    [∀ i, IsProbabilityMeasure (μ i)] (f : (Fin n → 𝒳) → ℝ) (hf : Measurable f)
    (hfi : Integrable f (Measure.pi μ)) (c : ℝ) (hc : 0 < c) :
    ((∀ᵐ x ∂Measure.pi μ, vPlus μ f x ≤ ENNReal.ofReal c) → ∀ t : ℝ, 0 < t →
        Measure.pi μ {x | (∫ z, f z ∂Measure.pi μ) + t < f x} ≤
          ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * c))))) ∧
      ((∀ᵐ x ∂Measure.pi μ, vMinus μ f x ≤ ENNReal.ofReal c) → ∀ t : ℝ, 0 < t →
        Measure.pi μ {x | f x < (∫ z, f z ∂Measure.pi μ) - t} ≤
          ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * c))))) :=
  by exact IsotropicVariance.Providers.Cited.blm_corollary3 μ f hf hfi c hc

end Cited
end IsotropicVariance
