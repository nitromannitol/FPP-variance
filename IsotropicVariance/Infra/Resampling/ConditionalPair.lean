/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Resampling.LabelPair
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-! # Marginals and unchanged information under conditional resampling -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
namespace IsotropicVariance.Infra.Resampling
variable {E Λ : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
  [MeasurableSpace Λ] (μ : Measure E) [IsProbabilityMeasure μ] (π : E → Λ)

instance : IsProbabilityMeasure (labelPairLaw μ π) := by
  unfold labelPairLaw
  infer_instance

/-- Old noise has the original law. -/
theorem labelPairLaw_map_fst (hπ : Measurable π) :
    (labelPairLaw μ π).map Prod.fst = μ := by
  rw [labelPairLaw, Measure.map_comp _ _ measurable_fst, ← Kernel.fst_eq, Kernel.fst_prod]
  rw [labelKernel, condDistrib_comp_map hπ.aemeasurable aemeasurable_id, Measure.map_id]

/-- New noise has the original law. -/
theorem labelPairLaw_map_snd (hπ : Measurable π) :
    (labelPairLaw μ π).map Prod.snd = μ := by
  rw [labelPairLaw, Measure.map_comp _ _ measurable_snd, ← Kernel.snd_eq, Kernel.snd_prod]
  rw [labelKernel, condDistrib_comp_map hπ.aemeasurable aemeasurable_id, Measure.map_id]

/-- Even when the label space is not standard Borel, every measurable real observable of
that label is preserved by a conditional draw. This permits conditioning on a sub-sigma
algebra directly, without assuming that it is countably generated. -/
theorem ae_labelKernel_real_eq (hπ : Measurable π) {f : Λ → ℝ} (hf : Measurable f) :
    ∀ᵐ l ∂μ.map π, ∀ᵐ x ∂labelKernel μ π l, f (π x) = f l := by
  have hmap := condDistrib_comp (X := π) (Y := id) hπ.aemeasurable
    (aemeasurable_id (μ := μ)) (hf.comp hπ)
  have hdir := condDistrib_comp_self (μ := μ) hπ.aemeasurable hf
  simp only [Function.comp_def, id_eq] at hmap hdir
  filter_upwards [hmap, hdir] with l hl hd
  have heq : (labelKernel μ π l).map (fun x => f (π x)) = Measure.dirac (f l) := by
    rw [Kernel.map_apply _ (show Measurable (fun x => f (π x)) from hf.comp hπ)] at hl
    exact hl.symm.trans hd
  have h : ∀ᵐ r ∂(labelKernel μ π l).map (fun x => f (π x)), r = f l := by
    rw [heq]
    simp
  exact ae_of_ae_map (hf.comp hπ).aemeasurable h

/-- Conditional resampling preserves every real observable of the retained information,
without a standard-Borel assumption on the label space. -/
theorem labelPairLaw_ae_real_eq (hπ : Measurable π) {f : Λ → ℝ} (hf : Measurable f) :
    ∀ᵐ p ∂labelPairLaw μ π, f (π p.1) = f (π p.2) := by
  apply Measure.ae_comp_of_ae_ae
    (measurableSet_eq_fun ((hf.comp hπ).comp measurable_fst)
      ((hf.comp hπ).comp measurable_snd))
  filter_upwards [ae_labelKernel_real_eq μ π hπ hf] with l hl
  rw [Kernel.prod_apply]
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun ((hf.comp hπ).comp measurable_fst)
      ((hf.comp hπ).comp measurable_snd))).mpr
  filter_upwards [hl] with x hx
  filter_upwards [hl] with y hy
  exact hx.trans hy.symm

end IsotropicVariance.Infra.Resampling
