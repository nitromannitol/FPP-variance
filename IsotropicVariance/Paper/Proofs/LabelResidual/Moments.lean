/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.ProfileError
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import IsotropicVariance.Paper.Proofs.Responses.MomentTools

/-!
# Moments of core errors and penalized reward tails

The far-pair estimate in the proof of Lemma `lem:residual` is the elementary
inequality `E (Y-c)_+^p ≤ E Y^(4p)/c^(3p)`, proved here in extended values, together with a
conversion between integer and real moments. The final lemma applies the conversion to the
actual old/new profile error.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.LabelResidual

/-- A positive penalty turns a `4p` moment into a `p` moment of the excess. -/
theorem lintegral_tsub_pow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (p : ℕ) :
    ∫⁻ x, (f x - c) ^ p ∂μ ≤ (∫⁻ x, f x ^ (4 * p) ∂μ) / c ^ (3 * p) := by
  have hcp0 : c ^ (3 * p) ≠ 0 := pow_ne_zero _ hc0
  have hcpt : c ^ (3 * p) ≠ ⊤ := ENNReal.pow_ne_top hct
  rw [div_eq_mul_inv, ← lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hcp0)]
  refine lintegral_mono fun x => ?_
  set a := f x
  rw [← div_eq_mul_inv]
  rw [ENNReal.le_div_iff_mul_le (Or.inl hcp0) (Or.inl hcpt)]
  by_cases hac : a ≤ c
  · rw [tsub_eq_zero_of_le hac]
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · simp [zero_pow hp.ne']
  · rw [not_le] at hac
    calc (a - c) ^ p * c ^ (3 * p) ≤ a ^ p * a ^ (3 * p) := by
          gcongr
          · exact tsub_le_self
      _ = a ^ (4 * p) := by rw [← pow_add]; ring_nf

/-- The real-constant version of the penalized tail bound. -/
theorem lintegral_sub_pow_le_far {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (p : ℕ)
    (h4p : ∫⁻ x, f x ^ (4 * p) ∂μ ≤ ENNReal.ofReal M ^ (4 * p)) :
    ∫⁻ x, (f x - ENNReal.ofReal c) ^ p ∂μ ≤ ENNReal.ofReal (M ^ (4 * p) / c ^ (3 * p)) := by
  have hc0 : ENNReal.ofReal c ≠ 0 := by simpa using hc
  refine (lintegral_tsub_pow_le hc0 ENNReal.ofReal_ne_top p).trans ?_
  rw [ENNReal.ofReal_div_of_pos (pow_pos hc _), ENNReal.ofReal_pow hM, ENNReal.ofReal_pow hc.le]
  exact ENNReal.div_le_div_right h4p _

universe u

/-- The sum of the two profile errors has `8d`-th moment at most `(2ε)^(8d)`.
This uses only the stated profile approximation and the actual coupling marginals. -/
theorem lintegral_profileError_pair_pow_le_of_measurePreserving {m : ℕ} {X : Setting.{u} m}
    {Λ : X.LabelFamily} {b A ℓ ε : ℝ} {K L i : ℕ} {z : Fin m → ℤ}
    (hε : 0 ≤ ε) (h : Gain.LabelProfileBound X b K A ℓ L Λ ε) (hi : i < K)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (hold : MeasurePreserving old P' X.P) (hnew : MeasurePreserving new P' X.P) :
    ∫⁻ ω, (profileError Λ b K A ℓ L i z (new ω) +
      profileError Λ b K A ℓ L i z (old ω)) ^ (8 * (m + 1)) ∂P' ≤
      ENNReal.ofReal ((2 * ε) ^ (8 * (m + 1))) := by
  have hf := aestronglyMeasurable_profileError h hi (z := z)
  have hm := (hf.comp_measurePreserving
      hnew).add
    (hf.comp_measurePreserving hold)
  apply Responses.lintegral_pow_le_of_eLpNorm_le hm.aemeasurable (by omega) (by positivity)
  rw [show (profileError Λ b K A ℓ L i z ∘ new +
      profileError Λ b K A ℓ L i z ∘ old) = (fun ω =>
      profileError Λ b K A ℓ L i z (new ω) +
      profileError Λ b K A ℓ L i z (old ω)) from rfl]
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
    ENNReal.ofReal_add (Nat.cast_nonneg m) zero_le_one, ENNReal.ofReal_natCast,
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using eLpNorm_profileError_pair_le_of_measurePreserving h hi hold hnew

end IsotropicVariance.Paper.Proofs.LabelResidual
