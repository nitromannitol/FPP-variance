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
import CurvatureVariance.Infra.Os.Product

/-!
# Provider of `CurvatureVariance.IsOs.mul`

Proves `CurvatureVariance.Providers.IsOs.mul` with exactly the type of the statement
`CurvatureVariance.Statements.Inputs.IsOsMul`, from `Infra.Os.isOs_mul_nonneg` (which asks the nonnegativity
almost everywhere). The statement is proved by `by exact` of this theorem applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- **[AKM, Lemma A.3(ii)]**: if `0 ≤ Xᵢ ≤ O_{sᵢ}(θᵢ)` for `i ∈ {1, 2}`, then
`X₁ X₂ ≤ O_{s₁s₂/(s₁+s₂)}(θ₁θ₂)`. -/
theorem IsOs.mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {s₁ s₂ θ₁ θ₂ : ℝ}
    {X₁ X₂ : Ω → ℝ} (hX₁ : IsOs P s₁ θ₁ X₁) (hX₂ : IsOs P s₂ θ₂ X₂) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hX₁0 : ∀ ω, 0 ≤ X₁ ω) (hX₂0 : ∀ ω, 0 ≤ X₂ ω) :
    IsOs P (s₁ * s₂ / (s₁ + s₂)) (θ₁ * θ₂) (fun ω => X₁ ω * X₂ ω) :=
  Infra.Os.isOs_mul_nonneg hX₁ hX₂ hs₁ hs₂ hθ₁ hθ₂ (Filter.Eventually.of_forall hX₁0)
    (Filter.Eventually.of_forall hX₂0)

end CurvatureVariance.Providers
