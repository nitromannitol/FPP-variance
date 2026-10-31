/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Entropy.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Laws on a finite type

For a probability measure `σ` on a finite type, three facts that the elementary entropy bound of
`CurvatureVariance.Infra.Entropy.Atoms` uses:

* `ae_of_atoms`: a property of every atom of positive mass holds almost everywhere;
* `sq_le_div_of_atom`: if the nonzero atoms have mass at least `p₀`, then `h² ≤ E h² / p₀` on them;
* `integral_sub_mean_sq`: the variance identity `∫ (h - E h)² = E h² - (E h)²`.
-/

@[expose] public section

open MeasureTheory Real ProbabilityTheory

namespace CurvatureVariance.Infra.Entropy

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

omit [MeasurableSingletonClass X] in
/-- A property holding at every atom of positive mass holds almost everywhere. -/
theorem ae_of_atoms (σ : Measure X) [IsFiniteMeasure σ] {P : X → Prop}
    (h : ∀ x, 0 < σ.real {x} → P x) : ∀ᵐ x ∂σ, P x := by
  rw [ae_iff_of_countable]
  intro x hx
  exact h x (ENNReal.toReal_pos hx (measure_ne_top _ _))

/-- On an atom, `h² ≤ E h² / p₀`. -/
theorem sq_le_div_of_atom (σ : Measure X) [IsProbabilityMeasure σ] {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hatom : ∀ x, 0 < σ.real {x} → p₀ ≤ σ.real {x}) (h : X → ℝ) {x : X}
    (hx : 0 < σ.real {x}) : h x ^ 2 ≤ (∫ y, h y ^ 2 ∂σ) / p₀ := by
  have hint : ∫ y, h y ^ 2 ∂σ = ∑ y, σ.real {y} • h y ^ 2 :=
    integral_fintype Integrable.of_finite
  have h1 : σ.real {x} • h x ^ 2 ≤ ∑ y, σ.real {y} • h y ^ 2 :=
    Finset.single_le_sum (f := fun y => σ.real {y} • h y ^ 2)
      (fun y _ => smul_nonneg measureReal_nonneg (sq_nonneg _)) (Finset.mem_univ x)
  rw [le_div_iff₀ hp₀, hint, mul_comm]
  have h2 := mul_le_mul_of_nonneg_right (hatom x hx) (sq_nonneg (h x))
  rw [smul_eq_mul] at h1
  linarith

/-- The variance identity `∫ (h - a)² = E h² - a²`. -/
theorem integral_sub_mean_sq (σ : Measure X) [IsProbabilityMeasure σ] (h : X → ℝ) :
    ∫ x, (h x - ∫ y, h y ∂σ) ^ 2 ∂σ = ∫ x, h x ^ 2 ∂σ - (∫ y, h y ∂σ) ^ 2 := by
  have hi : Integrable h σ := Integrable.of_finite
  have hi2 : Integrable (fun x => h x ^ 2) σ := Integrable.of_finite
  set a := ∫ y, h y ∂σ
  have : (fun x => (h x - a) ^ 2) = fun x => (h x ^ 2 - (2 * a) * h x) + a ^ 2 := by
    funext x; ring
  have e1 : ∫ x, (h x ^ 2 - (2 * a) * h x + a ^ 2) ∂σ =
      ∫ x, (h x ^ 2 - (2 * a) * h x) ∂σ + ∫ _x, a ^ 2 ∂σ :=
    integral_add (hi2.sub (hi.const_mul _)) (integrable_const _)
  have e2 : ∫ x, (h x ^ 2 - (2 * a) * h x) ∂σ =
      ∫ x, h x ^ 2 ∂σ - ∫ x, (2 * a) * h x ∂σ := integral_sub hi2 (hi.const_mul _)
  rw [this, e1, e2, integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  ring

end CurvatureVariance.Infra.Entropy
