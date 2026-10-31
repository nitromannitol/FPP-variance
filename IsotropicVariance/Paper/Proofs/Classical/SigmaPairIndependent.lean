/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.IndependentRefresh

/-! # Independence of the refreshed information from the whole old sample -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.Resampling

/-- Integrating the conditional noise kernel recovers the noise law. -/
theorem sigmaKernel_comp_map {Ω : Type*} [M : MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {G : MeasurableSpace Ω} (hG : G ≤ M) :
    sigmaKernel (mΩ := M) G P ∘ₘ (@Measure.map Ω Ω M G id P) = P := by
  let _ : MeasurableSpace Ω := M
  have hid : @Measurable Ω Ω M G id := measurable_id'' hG
  have hidAE : @AEMeasurable Ω Ω G M id P := ⟨id, hid, Filter.EventuallyEq.rfl⟩
  have hh := condDistrib_comp_map (mβ := G) (μ := P) hidAE
    (aemeasurable_id : @AEMeasurable Ω Ω M M id P)
  simpa only [sigmaKernel, labelKernel, Measure.map_id] using hh

/-- Under conditional resampling, an event in information independent of the
retained sigma algebra is independent of every event of the old sample. -/
theorem sigmaPairLaw_prod_eq_of_indep {Ω : Type*} [M : MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {G H : MeasurableSpace Ω} (hG : G ≤ M) (hH : H ≤ M) (hInd : Indep H G P)
    {A B : Set Ω} (hA : @MeasurableSet Ω M A) (hB : MeasurableSet[H] B) :
    sigmaPairLaw (mΩ := M) G P (A ×ˢ B) = P A * P B := by
  let _ : MeasurableSpace Ω := M
  let κ := sigmaKernel (mΩ := M) G P
  let Q : @Measure Ω G := @Measure.map Ω Ω M G id P
  have hBm : @MeasurableSet Ω M B := hH _ hB
  have : IsMarkovKernel κ := by unfold κ sigmaKernel; infer_instance
  have hid : @Measurable Ω Ω M G id := measurable_id'' hG
  have hidAE : @AEMeasurable Ω Ω G M id P := ⟨id, hid, Filter.EventuallyEq.rfl⟩
  have hConst : ∀ᵐ ω ∂Q, κ ω B = P B := by
    apply (ae_map_iff (mβ := G) hidAE ?_).mpr
    · exact sigmaKernel_apply_eq_of_indep P hG hH hInd hB
    · exact measurableSet_eq_fun (κ.measurable_coe hBm) measurable_const
  have hMarg : κ ∘ₘ Q = P := sigmaKernel_comp_map P hG
  calc
    _ = ∫⁻ ω, κ ω A * κ ω B ∂Q := by
      change ((κ ×ₖ κ) ∘ₘ Q) (A ×ˢ B) = _
      rw [Measure.bind_apply (hA.prod hBm) ((κ ×ₖ κ).aemeasurable (μ := Q))]
      simp only [Kernel.prod_apply_prod]
    _ = ∫⁻ ω, κ ω A * P B ∂Q := lintegral_congr_ae (hConst.mono fun ω hω => congrArg (fun r => κ ω A * r) hω)
    _ = (∫⁻ ω, κ ω A ∂Q) * P B := lintegral_mul_const _ (κ.measurable_coe hA)
    _ = _ := by rw [← Measure.bind_apply hA κ.aemeasurable, hMarg]

end IsotropicVariance.Paper.Proofs.Classical
