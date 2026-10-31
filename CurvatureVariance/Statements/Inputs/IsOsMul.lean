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
import CurvatureVariance.Providers.IsOsMul

/-!
# `CurvatureVariance.IsOs.mul`

A result the paper cites, stated with Mathlib and the definitions of this directory only, and proved
in this library: its proof is `CurvatureVariance.Providers.IsOs.mul` applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- **[AKM, Lemma A.3(ii)]**: if `0 ≤ Xᵢ ≤ O_{sᵢ}(θᵢ)` for `i ∈ {1, 2}`, then
`X₁ X₂ ≤ O_{s₁s₂/(s₁+s₂)}(θ₁θ₂)`. -/
theorem IsOs.mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {s₁ s₂ θ₁ θ₂ : ℝ}
    {X₁ X₂ : Ω → ℝ} (hX₁ : IsOs P s₁ θ₁ X₁) (hX₂ : IsOs P s₂ θ₂ X₂) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hX₁0 : ∀ ω, 0 ≤ X₁ ω) (hX₂0 : ∀ ω, 0 ≤ X₂ ω) :
    IsOs P (s₁ * s₂ / (s₁ + s₂)) (θ₁ * θ₂) (fun ω => X₁ ω * X₂ ω) :=
  by exact CurvatureVariance.Providers.IsOs.mul hX₁ hX₂ hs₁ hs₂ hθ₁ hθ₂ hX₁0 hX₂0

end CurvatureVariance
