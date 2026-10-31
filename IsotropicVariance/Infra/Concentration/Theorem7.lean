/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Concentration.NegativeEntropy
public import IsotropicVariance.Infra.Concentration.Herbst

/-! # BLM Theorem 7 in the `K = 1` form

Boucheron, Lugosi and Massart (2003), Theorem 7, printed p. 1587; proof on
p. 1592. This is the statement of the theorem `IsotropicVariance.Cited.blm_theorem7`:
nonnegative monotone `g`, and the parameter range `[0,1)`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal
namespace IsotropicVariance.Infra.Concentration

/-- [BLM, Theorem 7, p. 1587], in the `K = 1` form, which suffices for the paper.
The statement is that of the theorem `IsotropicVariance.Cited.blm_theorem7`. -/
theorem blm_theorem7 {n : ℕ} {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Fin n → Measure 𝒳)
    [∀ i, IsProbabilityMeasure (μ i)] (f : (Fin n → 𝒳) → ℝ) (hf : Measurable f)
    (hfi : Integrable f (Measure.pi μ)) (g : ℝ → ℝ) (hg : Monotone g) (hg0 : ∀ z, 0 ≤ g z)
    (hgi : Integrable (fun x => g (f x)) (Measure.pi μ))
    (hV : ∀ᵐ x ∂Measure.pi μ, vPlus μ f x ≤ ENNReal.ofReal (g (f x)))
    (hdiff : ∀ (x : Fin n → 𝒳) (i : Fin n) (y : 𝒳), |f x - f (Function.update x i y)| ≤ 1) :
    (∀ l : ℝ, 0 ≤ l → l < 1 →
        Integrable (fun x => Real.exp (-l * (f x - ∫ z, f z ∂Measure.pi μ)))
          (Measure.pi μ) ∧
        Real.log (∫ x, Real.exp (-l * (f x - ∫ z, f z ∂Measure.pi μ)) ∂Measure.pi μ) ≤
          l ^ 2 * (Real.exp 1 - 1) * ∫ x, g (f x) ∂Measure.pi μ) ∧
      ∀ t : ℝ, 0 < t → t ≤ (Real.exp 1 - 1) * ∫ x, g (f x) ∂Measure.pi μ →
        Measure.pi μ {x | f x < (∫ z, f z ∂Measure.pi μ) - t} ≤
          ENNReal.ofReal (Real.exp (-(t ^ 2 /
            (4 * (Real.exp 1 - 1) * ∫ x, g (f x) ∂Measure.pi μ)))) := by
  let P := Measure.pi μ
  let A := (exp 1 - 1) * ∫ x, g (f x) ∂P
  have hA : 0 ≤ A := mul_nonneg (by
    have he : 1 < exp 1 := one_lt_exp_iff.mpr zero_lt_one
    exact sub_nonneg.mpr he.le) (integral_nonneg fun x => hg0 (f x))
  obtain ⟨B, hB⟩ := exists_abs_le_of_update_le μ f hdiff
  have hExp (θ : ℝ) : Integrable (fun x => exp (θ * f x)) P :=
    integrable_exp_of_abs_le P hf hB θ
  have hSet : integrableExpSet f P = univ := by
    ext θ
    simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true]
    exact hExp θ
  have hMg : ∀ θ ∈ Icc (-1) 0, mgf (fun x => f x - ∫ z, f z ∂P) P θ ≤ exp (A * θ ^ 2) :=
    mgf_sub_integral_le_of_eentropy_le_neg hA hf
      (by rw [hSet, interior_univ]; exact subset_univ _)
      (fun θ hθ => eentropy_exp_le_of_monotone_vPlus_bound μ f hf g hg hg0 hgi hV hdiff
        ⟨hθ.1, hθ.2.le⟩)
  constructor
  · intro l hl hl1
    have hInt : Integrable (fun x => exp (-l * (f x - ∫ z, f z ∂P))) P := by
      have hh := (hExp (-l)).const_mul (exp (l * ∫ z, f z ∂P))
      have hEq : (fun x => exp (l * ∫ z, f z ∂P) * exp (-l * f x)) =ᵐ[P]
          (fun x => exp (-l * (f x - ∫ z, f z ∂P))) := by
        apply Eventually.of_forall
        intro x
        dsimp only
        rw [← exp_add]
        congr 1
        ring
      exact ⟨((hfi.sub (integrable_const (∫ z, f z ∂P))).aestronglyMeasurable.const_mul (-l)).aemeasurable.exp.aestronglyMeasurable,
        (hh.congr hEq).hasFiniteIntegral⟩
    refine ⟨hInt, ?_⟩
    have hh := hMg (-l) ⟨by linarith only [hl1], neg_nonpos.mpr hl⟩
    have hLog := (log_le_iff_le_exp (mgf_pos hInt)).mpr hh
    simpa only [mgf, neg_sq, A, P, mul_assoc, mul_left_comm, mul_comm] using hLog
  · intro t ht htA
    change t ≤ A at htA
    have hApos : 0 < A := ht.trans_le htA
    have hExpNeg (θ : ℝ) : Integrable (fun x => exp (θ * (-f x))) P := by
      simpa only [mul_neg, neg_mul] using hExp (-θ)
    have hMgNeg : ∀ θ ∈ Icc (0 : ℝ) 1,
        mgf (fun x => -f x - ∫ z, -f z ∂P) P θ ≤ exp (A * θ ^ 2) := by
      intro θ hθ
      have heq : (fun x => -f x - ∫ z, -f z ∂P) = -(fun x => f x - ∫ z, f z ∂P) := by
        funext x
        simp only [integral_neg, Pi.neg_apply]
        ring
      rw [heq, mgf_neg]
      simpa only [neg_sq] using hMg (-θ) ⟨by linarith only [hθ.2], neg_nonpos.mpr hθ.1⟩
    have hTail := measure_integral_add_le_of_mgf_le (Z := fun x => -f x) hApos
      zero_lt_one (fun θ _ => hExpNeg θ) hMgNeg ht.le
    have hSmall : t ^ 2 / (4 * A) ≤ 1 * t / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * A)).mpr
      have hh := mul_le_mul_of_nonneg_left htA ht.le
      nlinarith only [hh, mul_pos hApos ht]
    rw [min_eq_left hSmall] at hTail
    have hSub : {x | f x < (∫ z, f z ∂P) - t} ⊆
        {x | (∫ z, -f z ∂P) + t ≤ -f x} := by
      intro x hx
      change (∫ z, -f z ∂P) + t ≤ -f x
      rw [integral_neg]
      change f x < (∫ z, f z ∂P) - t at hx
      linarith only [hx]
    simpa only [A, P, mul_assoc] using (measure_mono hSub).trans hTail

end IsotropicVariance.Infra.Concentration
