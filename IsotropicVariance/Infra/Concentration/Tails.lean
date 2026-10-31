/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Concentration.ProductEntropy
public import IsotropicVariance.Infra.Concentration.Herbst
import Mathlib.Tactic.FieldSimp

/-!
# Gaussian tails from the positive variance proxy

This is the entropy-to-tail step of BLM Corollary 3 (p. 1585). The helper assumes
all exponential moments. The full integrable-function statement additionally
requires truncation and passage to the limit; that extension is not asserted here.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
namespace IsotropicVariance.Infra.Concentration

/-- The upper half of BLM Corollary 3 for functions with all exponential moments. -/
theorem measure_upper_tail_le_of_vPlus_le {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) {c : ℝ} (hc : 0 < c)
    (hV : ∀ᵐ x ∂Measure.pi μ, vPlus μ f x ≤ ENNReal.ofReal c)
    (hExp : ∀ θ : ℝ, Integrable (fun x => exp (θ * f x)) (Measure.pi μ))
    {t : ℝ} (ht : 0 < t) :
    Measure.pi μ {x | (∫ z, f z ∂Measure.pi μ) + t < f x} ≤
      ENNReal.ofReal (exp (-(t ^ 2 / (4 * c)))) := by
  have hSet : integrableExpSet f (Measure.pi μ) = univ := by
    ext θ
    simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true]
    exact hExp θ
  have hmgf := mgf_sub_integral_le_of_eentropy_le (θ₀ := t / (2 * c)) hc.le hf
    (by rw [hSet, interior_univ]; exact subset_univ _)
    (fun θ hθ => eentropy_exp_le_of_vPlus_le μ f hf hc.le hθ.1.le hV (hExp θ))
  have hTail := measure_integral_add_le_of_mgf_le hc (by positivity : 0 < t / (2 * c))
    (fun θ _ => hExp θ) hmgf ht.le
  have heq : t / (2 * c) * t / 2 = t ^ 2 / (4 * c) := by field_simp; ring
  rw [heq, min_self] at hTail
  refine (measure_mono ?_).trans hTail
  intro x hx
  change (∫ z, f z ∂Measure.pi μ) + t ≤ f x
  exact le_of_lt hx

end IsotropicVariance.Infra.Concentration
