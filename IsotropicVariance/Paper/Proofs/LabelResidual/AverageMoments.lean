/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.OffsetAverage
import Mathlib.Tactic.Ring

/-!
# Near-pair moments averaged over the offsets

The good-offset moment is small off a localization event. The other offsets have only the
coarse moment bound. Averaging their exceptional-event probabilities before taking the
Holder power gives the boundary and localization contribution required in the proof of Lemma
`lem:residual`.
-/

@[expose] public section

open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.LabelResidual

/-- A uniform finite average preserves a common upper bound. -/
theorem average_le_const {I : Type*} [Fintype I] [Nonempty I]
    {x : I → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ i, x i ≤ a) :
    (Fintype.card I : ℝ≥0∞)⁻¹ * ∑ i, x i ≤ a := by
  calc
    _ ≤ (Fintype.card I : ℝ≥0∞)⁻¹ * ∑ _i : I, a :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => h i)
    _ = a := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp), one_mul]

/-- Average a uniform small term plus the `3/4` power of exceptional probabilities. -/
theorem sum_mul_le_of_three_quarters_bound {I : Type*} [Fintype I]
    (w x q : I → ℝ≥0∞) (hw : ∑ i, w i = 1) {a M : ℝ≥0∞}
    (h : ∀ i, x i ≤ a + M * q i ^ (3 / 4 : ℝ)) :
    ∑ i, w i * x i ≤ a + M * (∑ i, w i * q i) ^ (3 / 4 : ℝ) := by
  calc
    _ ≤ ∑ i, w i * (a + M * q i ^ (3 / 4 : ℝ)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (h i)
    _ = a + M * ∑ i, w i * q i ^ (3 / 4 : ℝ) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl
      (sum_mul_three_quarters_rpow_le w q hw))

/-- The coarse moment on bad offsets and the small moment on good offsets combine with
only the total bad-offset weight. The localization bound is uniform in the offset. -/
theorem sum_mul_le_of_good_offsets {I : Type*} [Fintype I]
    (w x : I → ℝ≥0∞) (hw : ∑ i, w i = 1) (bad : Finset I) {a M δ : ℝ≥0∞}
    (hbad : ∀ i ∈ bad, x i ≤ M)
    (hgood : ∀ i ∉ bad, x i ≤ a + M * δ ^ (3 / 4 : ℝ)) :
    ∑ i, w i * x i ≤ a + M * (δ + ∑ i ∈ bad, w i) ^ (3 / 4 : ℝ) := by
  classical
  let q : I → ℝ≥0∞ := fun i => if i ∈ bad then 1 else δ
  have hq (i : I) : x i ≤ a + M * q i ^ (3 / 4 : ℝ) := by
    by_cases hi : i ∈ bad
    · simpa only [q, ite_eq_left hi, ENNReal.one_rpow, mul_one] using
        (hbad i hi).trans (le_add_left le_rfl : M ≤ a + M)
    · simpa only [q, ite_eq_right hi] using hgood i hi
  refine (sum_mul_le_of_three_quarters_bound w x q hw hq).trans ?_
  gcongr
  calc
    ∑ i, w i * q i ≤ ∑ i, w i * (δ + if i ∈ bad then 1 else 0) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul' le_rfl
      by_cases hi : i ∈ bad <;> simp [q, hi]
    _ = δ + ∑ i ∈ bad, w i := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
      simp

/-- Uniform-offset version with the bad offset count divided by the number of offsets. -/
theorem average_le_of_good_offsets {I : Type*} [Fintype I] [Nonempty I]
    (x : I → ℝ≥0∞) (bad : Finset I) {a M δ : ℝ≥0∞}
    (hbad : ∀ i ∈ bad, x i ≤ M)
    (hgood : ∀ i ∉ bad, x i ≤ a + M * δ ^ (3 / 4 : ℝ)) :
    (Fintype.card I : ℝ≥0∞)⁻¹ * ∑ i, x i ≤
      a + M * (δ + (bad.card : ℝ≥0∞) / Fintype.card I) ^ (3 / 4 : ℝ) := by
  have hw : ∑ _i : I, (Fintype.card I : ℝ≥0∞)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)]
  have h := sum_mul_le_of_good_offsets (fun _ : I => (Fintype.card I : ℝ≥0∞)⁻¹)
    x hw bad hbad hgood
  simpa only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using h

end IsotropicVariance.Paper.Proofs.LabelResidual
