/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Scales
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The scales `Q_s = A s^{1/2 − 1/K}` and `W_s = √(s Q_s)`

Elementary facts used throughout Section `sec:exponential` (where the scales are recalled from the
introduction): the exponent `α = 1/2 − 1/K` lies in `[2/5, 1/2)` for `K ≥ 10`, `Q` is positive and
nondecreasing, `Q_s ≥ 1` for `A ≥ 1`, `s ≥ 1`, `Q_r ≤ (r/t)^{2/5} Q_t` for `r ≤ t`
(used in the proof of Lemma `lem:tree`), `Q_t ≤ (t/r)^{1/2} Q_r`
for `r ≤ t`, and `W_s² = s Q_s`.
-/

@[expose] public section

namespace IsotropicVariance.Paper.Proofs.Profiles

/-- The exponent `α = 1/2 − 1/K` of `Q_s = A s^α`. -/
noncomputable def qExp (K : ℕ) : ℝ := 1 / 2 - 1 / (K : ℝ)

lemma qExp_ge {K : ℕ} (hK : 10 ≤ K) : 2 / 5 ≤ qExp K := by
  have hK' : (10 : ℝ) ≤ K := by exact_mod_cast hK
  unfold qExp
  have : 1 / (K : ℝ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hK'
  linarith

lemma qExp_le {K : ℕ} : qExp K ≤ 1 / 2 := by
  unfold qExp
  have : 0 ≤ 1 / (K : ℝ) := by positivity
  linarith

lemma qExp_pos {K : ℕ} (hK : 10 ≤ K) : 0 < qExp K := lt_of_lt_of_le (by norm_num) (qExp_ge hK)

lemma Q_eq (K : ℕ) (A s : ℝ) : Q K A s = A * s ^ qExp K := rfl

lemma Q_pos {K : ℕ} {A s : ℝ} (hA : 0 < A) (hs : 0 < s) : 0 < Q K A s :=
  mul_pos hA (Real.rpow_pos_of_pos hs _)

lemma Q_nonneg {K : ℕ} {A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) : 0 ≤ Q K A s :=
  mul_nonneg hA (Real.rpow_nonneg hs _)

lemma one_le_Q {K : ℕ} (hK : 10 ≤ K) {A s : ℝ} (hA : 1 ≤ A) (hs : 1 ≤ s) : 1 ≤ Q K A s := by
  rw [Q_eq]
  have : 1 ≤ s ^ qExp K := Real.one_le_rpow hs (qExp_pos hK).le
  nlinarith

lemma Q_mono {K : ℕ} (hK : 10 ≤ K) {A r s : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r) (hrs : r ≤ s) :
    Q K A r ≤ Q K A s :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr hrs (qExp_pos hK).le) hA

/-- `Q_{λ s} = λ^α Q_s`. -/
lemma Q_mul {K : ℕ} {A l s : ℝ} (hl : 0 ≤ l) (hs : 0 ≤ s) :
    Q K A (l * s) = l ^ qExp K * Q K A s := by
  rw [Q_eq, Q_eq, Real.mul_rpow hl hs]; ring

/-- `Q_r ≤ λ^{2/5} Q_t` if `r ≤ λ t`, `0 < λ ≤ 1` (the proof of Lemma `lem:tree`). -/
lemma Q_le_rpow_mul {K : ℕ} (hK : 10 ≤ K) {A r t l : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hl : 0 < l) (hl1 : l ≤ 1) (hrt : r ≤ l * t) : Q K A r ≤ l ^ (2 / 5 : ℝ) * Q K A t := by
  calc Q K A r ≤ Q K A (l * t) := Q_mono hK hA hr hrt
    _ = l ^ qExp K * Q K A t := Q_mul hl.le ht
    _ ≤ l ^ (2 / 5 : ℝ) * Q K A t :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hl hl1 (qExp_ge hK))
          (Q_nonneg hA ht)

/-- `Q_t ≤ (t/r)^{1/2} Q_r` if `0 < r ≤ t`. -/
lemma Q_le_sqrt_mul {K : ℕ} {A r t : ℝ} (hA : 0 ≤ A) (hr : 0 < r) (hrt : r ≤ t) :
    Q K A t ≤ (t / r) ^ (1 / 2 : ℝ) * Q K A r := by
  have hl : 1 ≤ t / r := by rw [le_div_iff₀ hr]; linarith
  have ht : t = (t / r) * r := by field_simp
  calc Q K A t = Q K A ((t / r) * r) := by rw [← ht]
    _ = (t / r) ^ qExp K * Q K A r := Q_mul (by positivity) hr.le
    _ ≤ (t / r) ^ (1 / 2 : ℝ) * Q K A r :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hl qExp_le)
          (Q_nonneg hA hr.le)

lemma W_sq {K : ℕ} {A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) : W K A s ^ 2 = s * Q K A s :=
  Real.sq_sqrt (mul_nonneg hs (Q_nonneg hA hs))

lemma W_nonneg (K : ℕ) (A s : ℝ) : 0 ≤ W K A s := Real.sqrt_nonneg _

/-- `1 ≤ log(2 + r)` for `r ≥ 1`. -/
lemma one_le_log_two_add {r : ℝ} (hr : 1 ≤ r) : 1 ≤ Real.log (2 + r) :=
  (Real.le_log_iff_exp_le (by linarith only [hr])).mpr
    (Real.exp_one_lt_three.le.trans (by linarith only [hr]))

end IsotropicVariance.Paper.Proofs.Profiles
