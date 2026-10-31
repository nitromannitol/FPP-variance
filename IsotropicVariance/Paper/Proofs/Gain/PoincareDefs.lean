/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Moments.Variance

/-!
# The label energy on a product space

The form of the left side of equation `eq:residual` on a product space (Section `sec:gain`).

`Z` is a square-integrable function of countably many independent variables `X_G`. They are
realized as the coordinates of the product `Measure.infinitePi μ` of their laws. Each `X_G` carries
a finite label `ℓ_G (X_G)`.

`Z^{G,ℓ}` replaces `X_G` by a draw of the conditional law `ℒ(X_G | ℓ_G)`, independent of the old
vector given `ℓ_G`. Its pair law is the integral over the old vector `x` of the conditioned law
`μ_G[|ℓ_G = ℓ_G (x_G)]`. `labelReplacementEnergy μ ℓ Z` is `ℛ_Z = ½ ∑_G E (Z - Z^{G,ℓ})²`.

The energy takes values in `ℝ≥0∞`. A label value of probability zero is never drawn: there,
`μ_G[|·]` is the zero measure, on a null set of `x`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Gain

universe u v w

section Energies

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- `ℛ_Z = ½ ∑_G E (Z - Z^{G,ℓ})²`, the left side of equation `eq:residual` for a function of
independent coordinates. `Z^{G,ℓ} = Z (x[G ↦ y])`, where `y` is drawn from
`ℒ(X_G | ℓ_G) = μ_G[|ℓ_G = ℓ_G (x_G)]`, independently of the old vector `x` given the label. -/
noncomputable def labelReplacementEnergy (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] {Λ : ι → Type*}
    (ℓ : ∀ i, X i → Λ i) (Z : (∀ i, X i) → ℝ) : ℝ≥0∞ :=
  (∑' i, ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((Z x - Z (Function.update x i y)) ^ 2)
    ∂(μ i)[|ℓ i ⁻¹' {ℓ i (x i)}] ∂Measure.infinitePi μ) / 2

end Energies

end IsotropicVariance.Paper.Proofs.Gain
