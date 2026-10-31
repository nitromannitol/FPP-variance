/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Concentration.UnitDifferenceVersion
import IsotropicVariance.Statements.Cited.BlmTheorem7

/-! # BLM lower tail with almost-sure coordinate differences

The codes of the noise satisfy the unit-difference hypothesis of [BLM03, Theorem 7] only almost
surely, since coded configurations off the support of the noise carry no information. The theorem
`IsotropicVariance.Cited.blm_theorem7` applies to a version of the code function with unit
differences at every point, `exists_version_abs_sub_update_le`, with the constant `g = c`. The tail
and the proxy `V₊` do not see the change on a null set.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.Concentration

/-- The lower Gaussian tail up to the constant-proxy threshold, from
`IsotropicVariance.Cited.blm_theorem7`. -/
theorem lower_tail_le_of_ae_unit_diff {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) {c : ℝ} (hc : 0 < c)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (hV : ∀ᵐ x ∂Measure.pi μ, vPlus μ f x ≤ ENNReal.ofReal c)
    (hDiff : ∀ i, ∀ᵐ p : (Fin n → A) × A ∂(Measure.pi μ).prod (μ i),
      |f p.1 - f (Function.update p.1 i p.2)| ≤ 1)
    {t : ℝ} (ht : 0 < t) (htA : t ≤ (exp 1 - 1) * c) :
    Measure.pi μ {x | f x < (∫ z, f z ∂Measure.pi μ) - t} ≤
      ENNReal.ofReal (exp (-(t ^ 2 / (4 * ((exp 1 - 1) * c))))) := by
  let P := Measure.pi μ
  obtain ⟨g, hg, hgf, hgd⟩ := exists_version_abs_sub_update_le μ hf hB hDiff
  have hfi : Integrable f P :=
    Integrable.of_bound hf.aestronglyMeasurable B (Eventually.of_forall hB)
  have hVg : ∀ᵐ x ∂P, vPlus μ g x ≤ ENNReal.ofReal ((fun _ : ℝ => c) (g x)) := by
    filter_upwards [hV, ae_vPlus_eq_of_ae_eq μ hgf] with x hx hxg
    rw [hxg]
    exact hx
  have hConst : ∫ x, (fun _ : ℝ => c) (g x) ∂P = c := by
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hTail := (Cited.blm_theorem7 μ g hg (hfi.congr hgf.symm) (fun _ => c) monotone_const
    (fun _ => hc.le) (integrable_const c) hVg hgd).2 t ht (by
      change t ≤ (Real.exp 1 - 1) * ∫ x, (fun _ : ℝ => c) (g x) ∂P
      rwa [hConst])
  change P {x | g x < (∫ z, g z ∂P) - t} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 /
    (4 * (Real.exp 1 - 1) * ∫ x, (fun _ : ℝ => c) (g x) ∂P)))) at hTail
  rw [hConst, integral_congr_ae hgf] at hTail
  have hSet : {x | f x < (∫ z, f z ∂P) - t} =ᵐ[P] {x | g x < (∫ z, f z ∂P) - t} := by
    filter_upwards [hgf] with x hx
    exact propext (by rw [hx])
  rw [measure_congr hSet]
  simpa only [mul_assoc] using hTail

end IsotropicVariance.Paper.Proofs.Classical
