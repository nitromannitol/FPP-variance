/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Resampling.ConditionalPair
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# Conditional resampling given a sub-sigma algebra

The conditioning space is the same set equipped with the smaller measurable space. It need
not itself be standard Borel: the resampled variable takes values in the original standard
Borel space. Agreement is stated for every measurable real observable of the retained
information, rather than as equality of points in a nonseparated label space.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace IsotropicVariance.Infra.Resampling
variable {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] [Nonempty Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Conditional distribution of the noise given the smaller sigma algebra. -/
noncomputable def sigmaKernel : @Kernel Ω Ω m mΩ :=
  @labelKernel Ω Ω mΩ inferInstance inferInstance m P inferInstance id

/-- Two independent draws given one value of the retained information. -/
noncomputable def sigmaPairLaw : @Measure (Ω × Ω) (@Prod.instMeasurableSpace Ω Ω mΩ mΩ) :=
  @labelPairLaw Ω Ω mΩ inferInstance inferInstance m P inferInstance id

instance : IsProbabilityMeasure (sigmaPairLaw m P) := by
  unfold sigmaPairLaw
  infer_instance

/-- The original sample has law `P`. -/
theorem sigmaPairLaw_map_fst (hm : m ≤ mΩ) : (sigmaPairLaw m P).map Prod.fst = P := by
  apply @labelPairLaw_map_fst Ω Ω mΩ inferInstance inferInstance m P inferInstance id
  exact Measurable.of_comap_le (by simpa only [MeasurableSpace.comap_id] using hm)

/-- The conditionally resampled noise also has law `P`. -/
theorem sigmaPairLaw_map_snd (hm : m ≤ mΩ) : (sigmaPairLaw m P).map Prod.snd = P := by
  apply @labelPairLaw_map_snd Ω Ω mΩ inferInstance inferInstance m P inferInstance id
  exact Measurable.of_comap_le (by simpa only [MeasurableSpace.comap_id] using hm)

/-- Every real observable of the retained sigma algebra is unchanged almost surely. For
resampling in `S`, take `m = info Sᶜ`; this is equality of the outside information. -/
theorem sigmaPairLaw_ae_eq (hm : m ≤ mΩ) {F : Ω → ℝ} (hF : Measurable[m] F) :
    ∀ᵐ p ∂sigmaPairLaw m P, F p.1 = F p.2 := by
  exact @labelPairLaw_ae_real_eq Ω Ω mΩ inferInstance inferInstance m P inferInstance id
    (Measurable.of_comap_le (by simpa only [MeasurableSpace.comap_id] using hm)) F hF

/-- Integrating against the conditional kernel computes conditional expectation. -/
theorem sigmaKernel_condExp (hm : m ≤ mΩ) {F : Ω → ℝ} (hF : Integrable F P) :
    P[F | m] =ᵐ[P] fun ω => ∫ x, F x ∂sigmaKernel m P ω := by
  have h := condExp_ae_eq_integral_condDistrib_id (mβ := m) (X := id) (μ := P)
    (measurable_id'' hm) hF
  simpa only [MeasurableSpace.comap_id, sigmaKernel, labelKernel, id_eq] using h

/-- A retained variable with values in any standard Borel space agrees on the two draws.
The embedding into the reals gives one full-measure event for the entire variable. -/
theorem sigmaPairLaw_ae_variable_eq {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    (hm : m ≤ mΩ) {F : Ω → Z} (hF : Measurable[m] F) :
    ∀ᵐ p ∂sigmaPairLaw m P, F p.1 = F p.2 := by
  have h := sigmaPairLaw_ae_eq m P hm ((measurable_embeddingReal Z).comp hF)
  exact h.mono fun _ hp => (measurableEmbedding_embeddingReal Z).injective hp

end IsotropicVariance.Infra.Resampling
