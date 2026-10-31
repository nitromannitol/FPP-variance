/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoiseProps.Gaussian
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Uniqueness of the white-noise configuration law

Linearity turns equality of the prescribed scalar marginals into equality of finite joint laws.
The cylinder sigma-algebra then determines the full distribution-valued law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Distributions ENNReal BigOperators

namespace IsotropicVariance.Infra.WhiteNoiseProps

open Example

variable {E Ω Ω' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [MeasurableSpace Ω] [MeasurableSpace Ω'] {W : Ω → WhiteNoiseConfig E}
  {V : Ω' → WhiteNoiseConfig E} {P : Measure Ω} {Q : Measure Ω'}

/-- Finite evaluation laws of white noises are equal, on possibly different sample spaces. -/
theorem map_family_eq (hW : IsWhiteNoise W P) (hV : IsWhiteNoise V Q)
    {ι : Type*} [Fintype ι] (φ : ι → 𝓓((⊤ : Opens E), ℝ)) :
    P.map (fun ω i => W ω (φ i)) = Q.map (fun ω i => V ω (φ i)) := by
  classical
  have := isProbabilityMeasure hW
  have := isProbabilityMeasure hV
  have hmW : Measurable (fun ω i => W ω (φ i)) := Measurable.of_eval fun i => measurable_eval hW (φ i)
  have hmV : Measurable (fun ω i => V ω (φ i)) := Measurable.of_eval fun i => measurable_eval hV (φ i)
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  congr 1
  rw [Measure.map_map L.continuous.measurable hmW, Measure.map_map L.continuous.measurable hmV]
  let ψ : 𝓓((⊤ : Opens E), ℝ) := ∑ i, L (Pi.single i 1) • φ i
  have hWψ : L ∘ (fun ω i => W ω (φ i)) = (fun ω => W ω ψ) := by
    funext ω
    rw [Function.comp_apply, dual_apply_eq_sum]
    simp only [ψ, map_sum, map_smul, smul_eq_mul, mul_comm]
  have hVψ : L ∘ (fun ω i => V ω (φ i)) = (fun ω => V ω ψ) := by
    funext ω
    rw [Function.comp_apply, dual_apply_eq_sum]
    simp only [ψ, map_sum, map_smul, smul_eq_mul, mul_comm]
  rw [hWψ, hVψ, (hW.2 ψ).map_eq, (hV.2 ψ).map_eq]

/-- The full configuration law of white noise is unique. -/
theorem law_eq (hW : IsWhiteNoise W P) (hV : IsWhiteNoise V Q) : P.map W = Q.map V := by
  have := isProbabilityMeasure hW
  have := isProbabilityMeasure hV
  let evals : WhiteNoiseConfig E → 𝓓((⊤ : Opens E), ℝ) → ℝ := fun ν φ => ν φ
  have hm : Measurable evals := Measurable.of_eval fun φ => Example.measurable_whiteNoise_eval φ
  have hmW : Measurable (fun ω => evals (W ω)) := hm.comp hW.1
  have hmV : Measurable (fun ω => evals (V ω)) := hm.comp hV.1
  have heq : P.map (fun ω => evals (W ω)) = Q.map (fun ω => evals (V ω)) := by
    have hfin (I : Finset 𝓓((⊤ : Opens E), ℝ)) :
        P.map (fun ω => I.restrict (evals (W ω))) = Q.map (fun ω => I.restrict (evals (V ω))) := by
      simpa only [evals, Finset.restrict_def] using map_family_eq hW hV (fun φ : I => φ.val)
    have hp : IsProjectiveLimit (P.map (fun ω => evals (W ω)))
        (fun I => Q.map (fun ω => I.restrict (evals (V ω)))) := by
      intro I
      rw [Measure.map_map (Finset.measurable_restrict I) hmW]
      exact hfin I
    exact hp.unique (isProjectiveLimit_map (hmV.aemeasurable (μ := Q)))
  have hgen : (inferInstance : MeasurableSpace (WhiteNoiseConfig E)) =
      MeasurableSpace.comap evals inferInstance := by
    simp only [WhiteNoiseConfig.instMeasurableSpace, MeasurableSpace.pi,
      MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, Function.comp_def, evals]
  ext A hA
  have hA' : MeasurableSet[MeasurableSpace.comap evals inferInstance] A := by
    rw [← hgen]
    exact hA
  obtain ⟨B, hB, rfl⟩ := hA'
  rw [Measure.map_apply hW.1 (hm hB), Measure.map_apply hV.1 (hm hB)]
  have hh := congrArg (fun μ : Measure (𝓓((⊤ : Opens E), ℝ) → ℝ) => μ B) heq
  rw [Measure.map_apply hmW hB, Measure.map_apply hmV hB] at hh
  convert hh using 1 <;> congr 1

end IsotropicVariance.Infra.WhiteNoiseProps
