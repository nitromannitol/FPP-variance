/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.GaussianMoment
public import IsotropicVariance.Paper.Proofs.Classical.LowerTailAE
public import IsotropicVariance.Statements.Cited.IsOs
import IsotropicVariance.Statements.Cited.BlmCorollary3

/-! # The finite-product BLM step in the classical concentration proof

Both tails of the first bound of Lemma `lem:classical` follow from [BLM03, Corollary 3] and
[BLM03, Theorem 7] (proof of Lemma `lem:classical`). Here both are applied to one function `Z`
with `V₊(Z) ≤ c`, which `IsotropicVariance.Paper.Proofs.Classical.PassageConcentration` takes to
be `-T_t / r`. BLM's Corollary 3 bounds the upper tail of `Z`, which is the lower tail of `T_t`.
BLM's Theorem 7 in its `K = 1` form bounds the lower tail of `Z`, which is the upper tail of `T_t`.
For this `Z`, `V₊(Z)` is the sum over the coordinates of the squared increases of `T_t / r` under
resampling.

The coordinate differences hold only almost surely, since `Z` is a function of codes of the noise.
BLM's Theorem 7 asks for them at every point, so `lower_tail_le_of_ae_unit_diff` applies it to a
version of `Z` with this property.
The geometry must supply the one-sided positive refresh proxy and the
oscillation bound. The two strict Gaussian tails give the absolute-centered `O_2` estimate.
-/

@[expose] public section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.Concentration
open IsotropicVariance.Infra

/-- BLM's constant-proxy application, including the bounded-range argument that
extends the restricted lower tail to every positive threshold. -/
theorem isOs_abs_centered_of_ae_bounded_positive_proxy {n : ℕ} {E : Type*} [MeasurableSpace E]
    (μ : Fin n → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → E) → ℝ) (hf : Measurable f) (hfi : Integrable f (Measure.pi μ))
    {c : ℝ} (hc : 0 < c) (hV : ∀ᵐ x ∂Measure.pi μ, vPlus μ f x ≤ ENNReal.ofReal c)
    (hdiff : ∀ i, ∀ᵐ p : (Fin n → E) × E ∂(Measure.pi μ).prod (μ i),
      |f p.1 - f (Function.update p.1 i p.2)| ≤ 1)
    (hRange : ∀ x, |f x - ∫ z, f z ∂Measure.pi μ| ≤ (exp 1 - 1) * c) :
    Cited.IsOs (Measure.pi μ) 2
      (2 * ((2 : ℝ) ^ (1 / 2 : ℝ) * (4 * sqrt ((exp 1 - 1) * c))))
      (fun x => |f x - ∫ z, f z ∂Measure.pi μ|) := by
  let P := Measure.pi μ
  let m := ∫ z, f z ∂P
  let A := (exp 1 - 1) * c
  have he : 1 ≤ exp 1 - 1 := by linarith only [add_one_le_exp (1 : ℝ)]
  have hcA : c ≤ A := by
    have hh := mul_le_mul_of_nonneg_right he hc.le
    simpa only [one_mul] using hh
  have hA : 0 < A := hc.trans_le hcA
  have hB (x : Fin n → E) : |f x| ≤ A + |m| := by
    have hh := abs_add_le (f x - m) m
    rw [sub_add_cancel] at hh
    linarith only [hh, hRange x]
  have hUpper := (Cited.blm_corollary3 μ f hf hfi c hc).1 hV
  have hUp (r : ℝ) (hr : 0 < r) : P {x | r < f x - m} ≤
      ENNReal.ofReal (exp (-(r ^ 2 / (4 * A)))) := by
    have hSet : {x | r < f x - m} = {x | m + r < f x} := by
      ext x
      simp only [mem_ofPred_eq]
      constructor <;> intro hx <;> linarith only [hx]
    rw [hSet]
    refine (hUpper r hr).trans (ENNReal.ofReal_le_ofReal (exp_le_exp.mpr (neg_le_neg ?_)))
    exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity : 0 < 4 * c)
      (mul_le_mul_of_nonneg_left hcA (by norm_num : (0 : ℝ) ≤ 4))
  have hDown (r : ℝ) (hr : 0 < r) : P {x | r < -(f x - m)} ≤
      ENNReal.ofReal (exp (-(r ^ 2 / (4 * A)))) := by
    by_cases hSmall : r ≤ A
    · have hSet : {x | r < -(f x - m)} = {x | f x < m - r} := by
        ext x
        simp only [mem_ofPred_eq]
        constructor <;> intro hx <;> linarith only [hx]
      rw [hSet]
      simpa only [P, m, A, mul_assoc] using
        lower_tail_le_of_ae_unit_diff μ f hf hc hB hV hdiff hr hSmall
    · have hEmpty : {x | r < -(f x - m)} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        change r < -(f x - m) at hx
        have hh := (neg_le_abs (f x - m)).trans (hRange x)
        exact hSmall (hx.le.trans hh)
      rw [hEmpty, measure_empty]
      exact zero_le
  have hh := isOs_abs_of_gaussian_tails P (hf.aemeasurable.sub aemeasurable_const) hA hUp hDown
  exact hh

end IsotropicVariance.Paper.Proofs.Classical
