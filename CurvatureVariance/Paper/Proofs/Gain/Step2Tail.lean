/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Truncating the rewards at `η |j − k|²`

The proof of Lemma `lem:residual` (the second paragraph of the proof of [AB26, Lemma 6.3]): "If
`|j − k| ≥ 1`, then" the first bound of equation `eq:rewardmoment` "gives
`E[(Y_i(j,k) − η|j − k|²)₊^{4d}]^{1/(4d)} ≤ Cη^{−3}|j − k|^{−2}`".
With `p = 4d`: pointwise `(Y − b)₊^p ≤ Y^{4p}/b^{3p}`, so a moment `E Y^{4p} ≤ (C(1 + a))^{4p}`
gives `E (Y − η a²)₊^p ≤ (16 C⁴ η^{−3} a^{−2})^p` for `a ≥ 1` (`lintegral_tsub_pow_le`).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

/-- Pointwise: `(y − b)^p ≤ y^{4p} / b^{3p}` for `0 < b < ∞` (truncated subtraction). -/
theorem tsub_pow_le_pow_div {y b : ℝ≥0∞} (hb0 : b ≠ 0) (hbt : b ≠ ⊤) (p : ℕ) :
    (y - b) ^ p ≤ y ^ (4 * p) / b ^ (3 * p) := by
  rcases le_or_gt y b with hyb | hyb
  · rw [tsub_eq_zero_of_le hyb]
    rcases Nat.eq_zero_or_pos p with hp | hp
    · simp [hp]
    · rw [zero_pow hp.ne']
      exact zero_le
  · rw [ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero _ hb0))
      (Or.inl (ENNReal.pow_ne_top hbt))]
    calc (y - b) ^ p * b ^ (3 * p) ≤ y ^ p * y ^ (3 * p) :=
          mul_le_mul' (pow_le_pow_left' tsub_le_self p) (pow_le_pow_left' hyb.le _)
      _ = y ^ (4 * p) := by rw [← pow_add]; ring_nf

/-- **The truncated rewards** (the proof of Lemma `lem:residual`): if
`E Y^{4p} ≤ (C(1 + a))^{4p}` with `C ≥ 0`, `a ≥ 1`, then `E (Y − η a²)₊^p ≤ (16 C⁴ η^{−3} a^{−2})^p`
for every `η > 0`. -/
theorem lintegral_tsub_pow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ≥0∞} {C a η : ℝ} (hC : 0 ≤ C) (ha : 1 ≤ a) (hη : 0 < η) (p : ℕ)
    (hmom : ∫⁻ ω, Y ω ^ (4 * p) ∂μ ≤ ENNReal.ofReal ((C * (1 + a)) ^ (4 * p))) :
    ∫⁻ ω, (Y ω - ENNReal.ofReal (η * a ^ 2)) ^ p ∂μ ≤
      ENNReal.ofReal ((16 * C ^ 4 / (η ^ 3 * a ^ 2)) ^ p) := by
  have ha0 : 0 < a := by linarith
  have hb : 0 < η * a ^ 2 := by positivity
  set b : ℝ≥0∞ := ENNReal.ofReal (η * a ^ 2)
  have hb0 : b ≠ 0 := by simp [b, hb]
  have hbt : b ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbp : b ^ (3 * p) ≠ 0 := pow_ne_zero _ hb0
  calc ∫⁻ ω, (Y ω - b) ^ p ∂μ ≤ ∫⁻ ω, Y ω ^ (4 * p) * (b ^ (3 * p))⁻¹ ∂μ :=
        lintegral_mono fun ω => (tsub_pow_le_pow_div hb0 hbt p).trans_eq (div_eq_mul_inv _ _)
    _ = (∫⁻ ω, Y ω ^ (4 * p) ∂μ) * (b ^ (3 * p))⁻¹ :=
        lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hbp)
    _ ≤ ENNReal.ofReal ((C * (1 + a)) ^ (4 * p)) * (b ^ (3 * p))⁻¹ := by gcongr
    _ = ENNReal.ofReal ((C * (1 + a)) ^ (4 * p) / (η * a ^ 2) ^ (3 * p)) := by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hb.le,
          ENNReal.ofReal_inv_of_pos (by positivity)]
    _ ≤ ENNReal.ofReal ((16 * C ^ 4 / (η ^ 3 * a ^ 2)) ^ p) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1a : 1 + a ≤ 2 * a := by linarith
        have h4 : C ^ 4 * (1 + a) ^ 4 ≤ 16 * C ^ 4 * a ^ 4 := by
          calc C ^ 4 * (1 + a) ^ 4 ≤ C ^ 4 * (2 * a) ^ 4 :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h1a 4) (by positivity)
            _ = 16 * C ^ 4 * a ^ 4 := by ring
        have hnum : (C * (1 + a)) ^ (4 * p) ≤ (16 * C ^ 4 * a ^ 4) ^ p := by
          rw [pow_mul, show (C * (1 + a)) ^ 4 = C ^ 4 * (1 + a) ^ 4 by ring]
          exact pow_le_pow_left₀ (by positivity) h4 p
        have hden : (η * a ^ 2) ^ (3 * p) = (η ^ 3 * a ^ 6) ^ p := by
          rw [pow_mul]; ring
        have heq : 16 * C ^ 4 * a ^ 4 / (η ^ 3 * a ^ 6) = 16 * C ^ 4 / (η ^ 3 * a ^ 2) := by
          field_simp
        calc (C * (1 + a)) ^ (4 * p) / (η * a ^ 2) ^ (3 * p)
            = (C * (1 + a)) ^ (4 * p) / (η ^ 3 * a ^ 6) ^ p := by rw [hden]
          _ ≤ (16 * C ^ 4 * a ^ 4) ^ p / (η ^ 3 * a ^ 6) ^ p :=
              div_le_div_of_nonneg_right hnum (by positivity)
          _ = (16 * C ^ 4 / (η ^ 3 * a ^ 2)) ^ p := by rw [← div_pow, heq]

end CurvatureVariance.Paper.Gain
