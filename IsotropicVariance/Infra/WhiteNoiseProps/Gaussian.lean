/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoiseProps.Basic

/-!
# Joint Gaussianity from distributional linearity

Every scalar projection of a finite evaluation vector is the evaluation at a linear
combination of test functions. The one-dimensional white-noise axiom therefore implies the
Gaussian law of the full vector.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Distributions ENNReal BigOperators

namespace IsotropicVariance.Infra.WhiteNoiseProps

open Example

/-- A real linear functional on a finite coordinate space is its coordinate linear combination. -/
theorem dual_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    L x = ∑ i, x i * L (Pi.single i 1) := by
  classical
  calc
    L x = L (∑ i, x i • Pi.single i 1) := by
      congr 1
      ext j
      simp [Pi.single_apply]
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

/-- Every finite vector of white-noise evaluations has a Gaussian law. -/
theorem hasGaussianLaw_family {E Ω ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [MeasurableSpace Ω] [Fintype ι]
    {W : Ω → WhiteNoiseConfig E} {P : Measure Ω} (h : IsWhiteNoise W P)
    (φ : ι → 𝓓((⊤ : Opens E), ℝ)) :
    HasGaussianLaw (fun ω i => W ω (φ i)) P := by
  classical
  have hm : Measurable (fun ω i => W ω (φ i)) :=
    Measurable.of_eval fun i => measurable_eval h (φ i)
  refine ⟨hm.aemeasurable, isGaussian_of_isGaussian_map (fun L => ?_)⟩
  rw [Measure.map_map L.continuous.measurable hm]
  let ψ : 𝓓((⊤ : Opens E), ℝ) := ∑ i, L (Pi.single i 1) • φ i
  have heq : L ∘ (fun ω i => W ω (φ i)) = (fun ω => W ω ψ) := by
    funext ω
    rw [Function.comp_apply, dual_apply_eq_sum]
    simp only [ψ, map_sum, map_smul, smul_eq_mul, mul_comm]
  rw [heq]
  exact (hasGaussianLaw_eval h ψ).isGaussian_map

/-- The full test-function-indexed white noise is a Gaussian process. -/
theorem isGaussianProcess {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [MeasurableSpace Ω] {W : Ω → WhiteNoiseConfig E} {P : Measure Ω}
    (h : IsWhiteNoise W P) : IsGaussianProcess (fun φ ω => W ω φ) P := by
  constructor
  intro I
  simpa only [Finset.restrict_def] using hasGaussianLaw_family h (fun φ : I => φ.val)

end IsotropicVariance.Infra.WhiteNoiseProps
