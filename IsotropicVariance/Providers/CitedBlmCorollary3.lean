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
import IsotropicVariance.Infra.Concentration.Corollary3

/-!
# Proof of `IsotropicVariance.Cited.blm_corollary3`

Proves `IsotropicVariance.Providers.Cited.blm_corollary3`, with exactly the type of the theorem
`IsotropicVariance.Cited.blm_corollary3` stated in `IsotropicVariance.Statements.Cited.BlmCorollary3`.
The statement module proves its theorem from this one and is not imported here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance.Providers
open IsotropicVariance.Cited

/-- [BLM, Corollary 3, p. 1585] (cited in the proof of Lemma `lem:classical`): for
`Z = f(X₁, …, X_n)` with independent coordinates, if `V₊ ≤ c` almost surely then
`P[Z > EZ + t] ≤ e^{−t²/4c}` for every `t > 0`; if `V₋ ≤ c` almost surely then
`P[Z < EZ − t] ≤ e^{−t²/4c}`. (`f` is measurable, and integrable since `EZ` appears.) -/
theorem Cited.blm_corollary3 {n : ℕ} {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Fin n → Measure 𝒳)
    [∀ i, IsProbabilityMeasure (μ i)] (f : (Fin n → 𝒳) → ℝ) (hf : Measurable f)
    (hfi : Integrable f (Measure.pi μ)) (c : ℝ) (hc : 0 < c) :
    ((∀ᵐ x ∂Measure.pi μ, vPlus μ f x ≤ ENNReal.ofReal c) → ∀ t : ℝ, 0 < t →
        Measure.pi μ {x | (∫ z, f z ∂Measure.pi μ) + t < f x} ≤
          ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * c))))) ∧
      ((∀ᵐ x ∂Measure.pi μ, vMinus μ f x ≤ ENNReal.ofReal c) → ∀ t : ℝ, 0 < t →
        Measure.pi μ {x | f x < (∫ z, f z ∂Measure.pi μ) - t} ≤
          ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * c))))) :=
  Infra.Concentration.blm_corollary3 μ f hf hfi c hc

end IsotropicVariance.Providers
