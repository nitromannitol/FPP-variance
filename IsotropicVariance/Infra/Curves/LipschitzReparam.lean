/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Lipschitz
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Lipschitz curves: reparametrization, reversal, additivity

Invariance of the arc integral `∫ G(γ s) ‖γ' s‖ ds` under affine reparametrization
(`lintegral_comp_affine`), the consequences for `subcurve` and `reverse`, and additivity over
adjacent intervals and finite subdivisions. No measurability of the weight `G` is needed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace IsotropicVariance.Infra.Curves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Chain rule for an affine reparametrization with nonzero slope. -/
theorem deriv_comp_affine (f : ℝ → E) (a c t : ℝ) (hc : c ≠ 0) :
    deriv (fun t => f (a + t * c)) t = c • deriv f (a + t * c) := by
  have hg : HasDerivAt (fun t : ℝ => a + t * c) c t := by
    simpa using ((hasDerivAt_id t).mul_const c).const_add a
  by_cases h : DifferentiableAt ℝ f (a + t * c)
  · exact (h.hasDerivAt.scomp t hg).deriv
  · rw [deriv_zero_of_not_differentiableAt h, smul_zero]
    apply deriv_zero_of_not_differentiableAt
    intro hd
    apply h
    have h2 : HasDerivAt (fun s : ℝ => (s - a) / c) c⁻¹ (a + t * c) := by
      simpa using ((hasDerivAt_id (a + t * c)).sub_const a).div_const c
    have h3 : DifferentiableAt ℝ (fun s : ℝ => (fun t => f (a + t * c)) ((s - a) / c))
        (a + t * c) := by
      refine DifferentiableAt.comp (a + t * c) (g := fun t => f (a + t * c)) ?_ h2.differentiableAt
      have : (a + t * c - a) / c = t := by field_simp; ring
      rw [this]; exact hd
    convert h3 using 1
    ext s
    simp only
    congr 1
    field_simp; ring

/-- The image of `[p, q]` under `t ↦ a + t c`, `c ≠ 0`, is the interval between the endpoint
images. -/
theorem image_affine_Icc (a c p q : ℝ) (hc : c ≠ 0) (hpq : p ≤ q) :
    (fun t : ℝ => a + t * c) '' Icc p q = uIcc (a + p * c) (a + q * c) := by
  rcases lt_or_gt_of_ne hc with h | h
  · rw [uIcc_of_ge (by nlinarith)]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩
    · intro hx
      refine ⟨(x - a) / c, ⟨?_, ?_⟩, by field_simp; ring⟩
      · rw [le_div_iff_of_neg h]; linarith [hx.2]
      · rw [div_le_iff_of_neg h]; linarith [hx.1]
  · rw [uIcc_of_le (by nlinarith)]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    · intro hx
      refine ⟨(x - a) / c, ⟨?_, ?_⟩, by field_simp; ring⟩
      · rw [le_div_iff₀ h]; linarith [hx.1]
      · rw [div_le_iff₀ h]; linarith [hx.2]

/-- Invariance of the arc integral under an affine reparametrization, increasing or decreasing. -/
theorem lintegral_comp_affine (f : ℝ → E) (G : E → ℝ≥0∞) (a c p q : ℝ) (hc : c ≠ 0)
    (hpq : p ≤ q) :
    ∫⁻ t in Icc p q, G (f (a + t * c)) * ‖deriv (fun t => f (a + t * c)) t‖ₑ
      = ∫⁻ s in uIcc (a + p * c) (a + q * c), G (f s) * ‖deriv f s‖ₑ := by
  rw [← image_affine_Icc a c p q hc hpq,
    lintegral_image_eq_lintegral_abs_deriv_mul (f := fun t : ℝ => a + t * c)
      (f' := fun _ => c) measurableSet_Icc
      (fun x _ => by simpa using (((hasDerivAt_id x).mul_const c).const_add a).hasDerivWithinAt)
      (fun x _ y _ hxy => by simpa [hc] using hxy)]
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [deriv_comp_affine f a c t hc, enorm_smul, Real.enorm_eq_ofReal_abs]
  ring

namespace LipCurve

/-- Reversal maps the arc `[a, b]` to the arc `[1 - b, 1 - a]`. -/
theorem arcIntegral_reverse {u v : E} (γ : LipCurve E u v) (G : E → ℝ≥0∞) {a b : ℝ}
    (hab : a ≤ b) : γ.reverse.arcIntegral G a b = γ.arcIntegral G (1 - b) (1 - a) := by
  have hf : γ.reverse.toFun = fun t => γ.toFun (1 + t * (-1)) := by
    ext t; simp [reverse, sub_eq_add_neg]
  have := lintegral_comp_affine γ.toFun G 1 (-1) a b (by norm_num) hab
  rw [uIcc_of_ge (by linarith)] at this
  unfold arcIntegral
  rw [hf]
  simpa [sub_eq_add_neg] using this

/-- Reversal preserves the cost. -/
theorem cost_reverse {u v : E} (γ : LipCurve E u v) (ρ : E → ℝ≥0) :
    γ.reverse.cost ρ = γ.cost ρ := by
  unfold cost arcCost
  rw [arcIntegral_reverse _ _ zero_le_one]
  norm_num

end LipCurve

end IsotropicVariance.Infra.Curves
