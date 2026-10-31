/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Example.Translation
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# The convolution density satisfies the local-density assumption

Joint measurability follows from the LF continuity proved in `Translation` and the literal
cylinder sigma algebra on distributions.
-/

@[expose] public section
open Set MeasureTheory TopologicalSpace
open scoped Distributions
namespace IsotropicVariance.Infra.Example

/-- The support of `y ↦ χ(x − y)` lies in the closed unit ball around `x`. -/
theorem tsupport_reflectTranslate_subset {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (x : Pt m) :
    tsupport ⇑(TestFunction.reflectTranslate χ x) ⊆ Metric.closedBall x 1 := by
  intro y hy
  have h : ⇑(TestFunction.reflectTranslate χ x) = ⇑χ ∘ (Homeomorph.subLeft x) := rfl
  rw [h, tsupport_comp_eq_preimage] at hy
  have := hχ hy
  simpa [dist_eq_norm, norm_sub_rev] using this

/-- The example density `ψ(χ∗ω)` satisfies Assumption `ass:local` (1) with the closed unit ball. -/
theorem convolutionDensity_determined {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (x : Pt m)
    (ν ν' : WhiteNoiseConfig (Pt m))
    (h : WhiteNoiseConfig.AgreeOn (Metric.closedBall x 1) ν ν') :
    convolutionDensity χ ψ ν x = convolutionDensity χ ψ ν' x := by
  simp only [convolutionDensity, h _ (tsupport_reflectTranslate_subset χ hχ x)]

/-- The example density satisfies Assumption `ass:local` (2). -/
theorem convolutionDensity_bounds {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ)) (ψ : ℝ → ℝ)
    (a b : ℝ) (ha : 0 < a) (hψ : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ a b : ℝ, 0 < a ∧ ∀ ν x, a ≤ convolutionDensity χ ψ ν x ∧ convolutionDensity χ ψ ν x ≤ b :=
  ⟨a, b, ha, fun _ _ => hψ _⟩

/-- The example density satisfies Assumption `ass:local` (3), for every rigid motion (proper
or not): the orientation of `IsMovedBy` is the right one. -/
theorem convolutionDensity_covariant {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y) (ψ : ℝ → ℝ) (g : Pt m ≃ᵃⁱ[ℝ] Pt m)
    (ν ν' : WhiteNoiseConfig (Pt m)) (h : WhiteNoiseConfig.IsMovedBy g ν ν') (x : Pt m) :
    convolutionDensity χ ψ ν' (g x) = convolutionDensity χ ψ ν x := by
  simp only [convolutionDensity]
  rw [h (TestFunction.reflectTranslate χ (g x)) (TestFunction.reflectTranslate χ x)]
  funext y
  simp only [Function.comp_apply]
  change χ (x - y) = χ (g x - g y)
  apply hχ
  rw [← dist_eq_norm, ← dist_eq_norm, g.dist_map]


/-- Evaluation at a fixed test function is measurable for the cylinder sigma algebra. -/
lemma measurable_whiteNoise_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : 𝓓((⊤ : Opens E), ℝ)) : Measurable (fun ν : WhiteNoiseConfig E => ν φ) := by
  apply Measurable.of_comap_le
  exact le_iSup (fun ψ : 𝓓((⊤ : Opens E), ℝ) =>
    (inferInstance : MeasurableSpace ℝ).comap (fun ν : WhiteNoiseConfig E => ν ψ)) φ

/-- Convolution with a test function is continuous in the spatial variable for every
individual distribution, with no almost-everywhere exception. -/
theorem continuous_convolution {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ν : WhiteNoiseConfig (Pt m)) :
    Continuous (fun x => ν (TestFunction.reflectTranslate χ x)) :=
  ν.continuous.comp (continuous_reflectTranslate χ hχ)

/-- Convolution is jointly measurable in the distribution and the spatial point. -/
theorem measurable_convolution {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ : tsupport ⇑χ ⊆ Metric.closedBall 0 1) :
    Measurable (fun p : WhiteNoiseConfig (Pt m) × Pt m =>
      p.1 (TestFunction.reflectTranslate χ p.2)) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (continuous_convolution χ hχ) (fun x => measurable_whiteNoise_eval
      (TestFunction.reflectTranslate χ x))
  exact h.comp measurable_swap

/-- A continuous scalar transform preserves joint measurability of the convolution. -/
theorem measurable_convolutionDensity {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    Measurable (Function.uncurry (convolutionDensity χ ψ)) :=
  hψ.measurable.comp (measurable_convolution χ hχ)

/-- The white-noise convolution example satisfies all of Assumption `ass:local`, for the literal
definitions of the model. No probabilistic property of the configuration is needed. -/
theorem isLocalDensity_convolutionDensity {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (a b : ℝ) (ha : 0 < a)
    (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy
      (convolutionDensity χ ψ) where
  measurable := measurable_convolutionDensity χ hχ_support ψ hψ
  determined := convolutionDensity_determined χ hχ_support ψ
  bounds := convolutionDensity_bounds χ ψ a b ha hψ_bounds
  covariant g _ ν ν' h x := convolutionDensity_covariant χ hχ_radial ψ g ν ν' h x

end IsotropicVariance.Infra.Example
