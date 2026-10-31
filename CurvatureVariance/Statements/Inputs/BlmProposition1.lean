/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance
import CurvatureVariance.Providers.BlmProposition1

/-!
# `CurvatureVariance.blm_proposition1`

A result from the literature that the paper uses through the proof of [AB26, Lemma 6.3], stated with
Mathlib and the definitions of this directory only, and proved in this library: its proof is
`CurvatureVariance.Providers.blm_proposition1` applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- **[BLM03, Proposition 1, p. 1584]** (the Efron–Stein inequality, used in the proof of
[AB26, Lemma 6.3], which the proof of Lemma `lem:residual` applies). Let `X₁, …, X_n` be independent
random variables taking values in a measurable space `𝒳`, let `X₁', …, X_n'` be independent copies
of them, and let `f : 𝒳ⁿ → ℝ` be a measurable function. With `Z = f(X₁, …, X_n)` and
`Z⁽ⁱ⁾ = f(X₁, …, X_{i−1}, X_i', X_{i+1}, …, X_n)`, we have
`Var(Z) ≤ ½ E[∑_{i=1}^n (Z − Z⁽ⁱ⁾)²]`.

There is no moment hypothesis, as in [BLM03]: the bound is in `[0, ∞]`, which covers infinite
variance. `Function.update x i y` is `(X₁, …, X_i', …, X_n)`, with `X_i'` drawn from `μ i`.
`E[∑_{i=1}^n …]` is the sum of the iterated integrals, by additivity of the integral on
nonnegative measurable functions and Tonelli's theorem, `X_i'` being independent of
`X₁, …, X_n`. The coordinates take values in spaces `𝒳 i`, not one space `𝒳`, which is the same
theorem: the case of one space is the constant family, and a family is covered by BLM's
statement on the disjoint union. -/
theorem blm_proposition1 (n : ℕ) {𝒳 : Fin n → Type*} [∀ i, MeasurableSpace (𝒳 i)]
    (μ : ∀ i, Measure (𝒳 i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, 𝒳 i) → ℝ) (hf : Measurable f) :
    evariance f (Measure.pi μ) ≤
      (1 / 2 : ℝ≥0∞) * ∑ i, ∫⁻ x, ∫⁻ y, ‖f x - f (Function.update x i y)‖ₑ ^ 2 ∂μ i
        ∂Measure.pi μ :=
  by exact CurvatureVariance.Providers.blm_proposition1 n μ f hf

end CurvatureVariance
