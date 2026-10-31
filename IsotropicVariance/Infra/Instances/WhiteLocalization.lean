/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Model
public import IsotropicVariance.Infra.WhiteNoiseProps.Motion

/-!
# Exact smooth localization of white-noise configurations

Multiplication by a fixed smooth cutoff defines an everywhere continuous-linear operation on
distributions. It is measurable from regional information when the cutoff is supported there,
and preserves a local density at every center whose closed unit ball lies in its plateau.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace IsotropicVariance.Infra.Instances

/-- Multiply tests by a fixed smooth function. -/
noncomputable def multiplyTest {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ)) :
    𝓓((⊤ : Opens (Pt m)), ℝ) →L[ℝ] 𝓓((⊤ : Opens (Pt m)), ℝ) :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) χ.contDiff

/-- Smooth localization of a distribution, defined on every configuration. -/
noncomputable def localizeWhite {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (ν : WhiteNoiseConfig (Pt m)) : WhiteNoiseConfig (Pt m) := ν.comp (multiplyTest χ)

/-- The localized test is supported in the cutoff's topological support. -/
theorem tsupport_multiplyTest_subset {m : ℕ} (χ φ : 𝓓((⊤ : Opens (Pt m)), ℝ)) :
    tsupport ⇑(multiplyTest χ φ) ⊆ tsupport ⇑χ := by
  change tsupport (fun x => φ x * χ x) ⊆ tsupport ⇑χ
  exact tsupport_mul_subset_right

/-- Localization uses only the regional information containing the cutoff support. -/
theorem measurable_localizeWhite {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    {U : Set (Pt m)} (hχ : tsupport ⇑χ ⊆ U) :
    Measurable[Paper.Noise.info Paper.Noise.white U] (localizeWhite χ) := by
  apply @WhiteNoiseProps.measurable_of_evaluations (Pt m) (WhiteNoiseConfig (Pt m)) _ _
    (Paper.Noise.info Paper.Noise.white U) (localizeWhite χ)
  intro φ
  change Measurable[Paper.Noise.info Paper.Noise.white U]
    (fun ν : WhiteNoiseConfig (Pt m) => ν (multiplyTest χ φ))
  apply Measurable.of_comap_le
  exact le_iSup_of_le (multiplyTest χ φ)
    (le_iSup_of_le ((tsupport_multiplyTest_subset χ φ).trans hχ) le_rfl)

/-- Localization is invisible to all tests supported in a region on which the cutoff is one. -/
theorem agreeOn_localizeWhite {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (ν : WhiteNoiseConfig (Pt m)) {S : Set (Pt m)} (hχ : Set.EqOn χ 1 S) :
    WhiteNoiseConfig.AgreeOn S ν (localizeWhite χ ν) := by
  intro φ hφ
  have heq : multiplyTest χ φ = φ := by
    ext x
    change φ x * χ x = φ x
    by_cases hx : φ x = 0
    · rw [hx, zero_mul]
    · rw [hχ (hφ (subset_tsupport _ hx)), Pi.one_apply, mul_one]
  change ν φ = ν (multiplyTest χ φ)
  rw [heq]

/-- Exact density locality is preserved at centers whose closed unit balls lie in the plateau. -/
theorem white_density_localize_eq {m : ℕ}
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ)
    (χ : 𝓓((⊤ : Opens (Pt m)), ℝ)) (ν : WhiteNoiseConfig (Pt m)) (x : Pt m)
    (hχ : Set.EqOn χ 1 (Metric.closedBall x 1)) : ρ ν x = ρ (localizeWhite χ ν) x :=
  hρ.determined x ν (localizeWhite χ ν) (agreeOn_localizeWhite χ ν hχ)

end IsotropicVariance.Infra.Instances
