/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Concentration.Truncation

/-!
# BLM Corollary 3 for integrable functions

Boucheron, Lugosi and Massart (2003), Corollary 3, printed p. 1585.
Truncation removes every exponential-moment assumption from the entropy proof.
The strict inequalities in the source allow passage to the limit pointwise.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal
namespace IsotropicVariance.Infra.Concentration

/-- The integrable-function upper tail in BLM Corollary 3. -/
theorem measure_upper_tail_le_of_vPlus_le_integrable {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) (hfi : Integrable f (Measure.pi μ))
    {c : ℝ} (hc : 0 < c) (hV : ∀ᵐ x ∂Measure.pi μ, vPlus μ f x ≤ ENNReal.ofReal c)
    {t : ℝ} (ht : 0 < t) :
    Measure.pi μ {x | (∫ z, f z ∂Measure.pi μ) + t < f x} ≤
      ENNReal.ofReal (exp (-(t ^ 2 / (4 * c)))) := by
  apply measure_le_of_eventually_mem (S := fun k : ℕ =>
    {x | (∫ z, clip k (f z) ∂Measure.pi μ) + t < clip k (f x)})
  · intro x hx
    exact ((tendsto_integral_clip (Measure.pi μ) hf hfi).add_const t).eventually_lt
      (tendsto_clip (f x)) hx
  · intro k
    apply measure_upper_tail_le_of_vPlus_le μ (fun x => clip k (f x))
      ((measurable_clip k).comp hf) hc
    · exact hV.mono fun x hx => (vPlus_clip_le μ f k x).trans hx
    · exact integrable_exp_clip (Measure.pi μ) hf (Nat.cast_nonneg k)
    · exact ht

/-- [BLM, Corollary 3, p. 1585]: bounded positive or negative conditional refresh
variance implies the corresponding Gaussian tail, with denominator `4*c`.
The binders and conclusions are those of the theorem `IsotropicVariance.Cited.blm_corollary3`. -/
theorem blm_corollary3 {n : ℕ} {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Fin n → Measure 𝒳)
    [∀ i, IsProbabilityMeasure (μ i)] (f : (Fin n → 𝒳) → ℝ) (hf : Measurable f)
    (hfi : Integrable f (Measure.pi μ)) (c : ℝ) (hc : 0 < c) :
    ((∀ᵐ x ∂Measure.pi μ, vPlus μ f x ≤ ENNReal.ofReal c) → ∀ t : ℝ, 0 < t →
        Measure.pi μ {x | (∫ z, f z ∂Measure.pi μ) + t < f x} ≤
          ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * c))))) ∧
      ((∀ᵐ x ∂Measure.pi μ, vMinus μ f x ≤ ENNReal.ofReal c) → ∀ t : ℝ, 0 < t →
        Measure.pi μ {x | f x < (∫ z, f z ∂Measure.pi μ) - t} ≤
          ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * c))))) := by
  constructor
  · intro hV t ht
    exact measure_upper_tail_le_of_vPlus_le_integrable μ f hf hfi hc hV ht
  · intro hV t ht
    have h := measure_upper_tail_le_of_vPlus_le_integrable μ (fun x => -f x) hf.neg hfi.neg hc
      (by simpa only [vPlus_neg] using hV) ht
    have heq : {x | (∫ z, -f z ∂Measure.pi μ) + t < -f x} =
        {x | f x < (∫ z, f z ∂Measure.pi μ) - t} := by
      ext x
      simp only [integral_neg, mem_ofPred_eq]
      constructor <;> intro hx <;> linarith
    rwa [heq] at h

end IsotropicVariance.Infra.Concentration
