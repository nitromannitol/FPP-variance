/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.Integral
import IsotropicVariance.Infra.Os.Moments

/-!
# Almost-sure integrability in AKM Lemma A.4

In the measured-family form of [AKM, Lemma A.4] (`isOs_integral`), almost every realization of
the family is integrable against the index measure, so that the integral in the conclusion is a
genuine integral and not Lean's junk value. The proof bounds the first moment of `X x / θ x`
uniformly ([AKM, Lemma A.1] through `IsOs.lintegral_pos_rpow_le`) and integrates it against the
finite measure `θ μ` by Tonelli. No finiteness assumption on `μ` is needed beyond the
integrability of the positive scale `θ`. This is used in the proof of the theorem
`IsotropicVariance.Cited.isOs_integral_of_one_le`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace IsotropicVariance.Infra.Os

open Cited

/-- In AKM A.4, almost every realization `x ↦ X x ω` of the family is integrable against the index
measure `μ`. -/
theorem ae_integrable_of_isOs {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (μ : Measure E) [IsProbabilityMeasure P]
    {s : ℝ} (hs : 0 < s) (θ : E → ℝ) (hθ : ∀ x, 0 < θ x)
    (hθm : Measurable θ) (hθi : Integrable θ μ)
    (X : E → Ω → ℝ) (hXm : Measurable (Function.uncurry X))
    (hX0 : ∀ x ω, 0 ≤ X x ω) (hX : ∀ x, IsOs P s (θ x) (X x)) :
    ∀ᵐ ω ∂P, Integrable (fun x => X x ω) μ := by
  -- the finite measure `θ μ`, against which `Y = X / θ` has a uniformly bounded mean
  let f : E → ℝ≥0∞ := fun x => ENNReal.ofReal (θ x)
  have hfm : Measurable f := hθm.ennreal_ofReal
  let ν := μ.withDensity f
  have hν : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (hθ x).le)).mp
      hθi.hasFiniteIntegral).ne
  let Y : E → Ω → ℝ := fun x ω => X x ω / θ x
  have hYm : Measurable (Function.uncurry Y) := hXm.div (hθm.comp measurable_fst)
  let M : ℝ≥0∞ := ENNReal.ofReal (2 * (1 + ((Nat.ceil (1 / s)).factorial : ℝ)))
  have hYb (x : E) : ∫⁻ ω, ENNReal.ofReal (Y x ω) ∂P ≤ M := by
    have hY : IsOs P s 1 (Y x) := (isOs_div_iff (hθ x)).mpr (hX x)
    have h := hY.lintegral_pos_rpow_le hs zero_lt_one zero_le_one
    have hmax : (fun ω => ENNReal.ofReal (max (Y x ω) 0 ^ (1 : ℝ))) =
        fun ω => ENNReal.ofReal (Y x ω) := by
      funext ω
      rw [Real.rpow_one, max_eq_left (div_nonneg (hX0 x ω) (hθ x).le)]
    simpa only [hmax, Real.one_rpow, mul_one] using h
  have hFm : Measurable (Function.uncurry fun ω x => ENNReal.ofReal (Y x ω)) :=
    hYm.ennreal_ofReal.comp measurable_swap
  have hswap : ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (Y x ω) ∂ν ∂P ≤ M * ν univ := by
    rw [lintegral_lintegral_swap hFm.aemeasurable]
    calc
      _ ≤ ∫⁻ _, M ∂ν := lintegral_mono hYb
      _ = M * ν univ := lintegral_const M
  have hfin : ∀ᵐ ω ∂P, ∫⁻ x, ENNReal.ofReal (Y x ω) ∂ν < ∞ :=
    ae_lt_top' hFm.lintegral_prod_right'.aemeasurable
      (hswap.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν univ))).ne
  filter_upwards [hfin] with ω hω
  have hXωm : Measurable fun x => X x ω := hXm.comp (measurable_id.prodMk measurable_const)
  refine ⟨hXωm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => hX0 x ω)).mpr ?_⟩
  have heq : ∫⁻ x, ENNReal.ofReal (Y x ω) ∂ν = ∫⁻ x, ENNReal.ofReal (X x ω) ∂μ := by
    have hgm : Measurable fun x => ENNReal.ofReal (Y x ω) :=
      (hYm.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal
    rw [lintegral_withDensity_eq_lintegral_mul _ hfm hgm]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply, f, Y, ← ENNReal.ofReal_mul (hθ x).le]
    rw [mul_div_cancel₀ _ (hθ x).ne']
  exact heq ▸ hω

end IsotropicVariance.Infra.Os
