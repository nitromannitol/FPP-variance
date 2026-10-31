/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Entropy.ModifiedPoincare
public import CurvatureVariance.Infra.Entropy.CoordinateBound

/-!
# Coordinate operators for finitely-valued coordinates

The operators on functions of one coordinate with values in a finite set, and their extensions to
the product, for the logarithmic Sobolev inequalities of [BR, Proposition 2.1]: the mean `coordMean`
of a function of one coordinate, and the scaled difference `scaledDiff c i`, `c (g - E g)`, whose
extension to the product is `c` times the coordinate difference (`extendCoord_scaledDiff`).
-/

@[expose] public section

open MeasureTheory Real

namespace CurvatureVariance.Infra.Entropy

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
  {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]

variable (μ) in
/-- The average over the coordinate `i`, as a linear map of functions on a finite set. -/
noncomputable def coordMean (i : ι) : (X i → ℝ) →ₗ[ℝ] (X i → ℝ) where
  toFun g := fun _ => ∫ y, g y ∂μ i
  map_add' g h := by
    funext _
    exact integral_add Integrable.of_finite Integrable.of_finite
  map_smul' c g := by
    funext _
    simp [integral_const_mul]

variable (μ) in
/-- The operator `c D_i`, `D_i g = g - ∫ g dμ_i`. -/
noncomputable def scaledDiff (c : ℝ) (i : ι) : (X i → ℝ) →ₗ[ℝ] (X i → ℝ) :=
  c • (LinearMap.id - coordMean μ i)

omit [DecidableEq ι] in
theorem scaledDiff_apply (c : ℝ) (i : ι) (g : X i → ℝ) (y : X i) :
    scaledDiff μ c i g y = c * (g y - ∫ z, g z ∂μ i) := by
  simp [scaledDiff, coordMean]

theorem extendCoord_scaledDiff (c : ℝ) (i : ι) (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    extendCoord i (scaledDiff μ c i) f x = c * coordDiff μ i f x := by
  simp [extendCoord, scaledDiff_apply, coordDiff, coordAvg]

end CurvatureVariance.Infra.Entropy
