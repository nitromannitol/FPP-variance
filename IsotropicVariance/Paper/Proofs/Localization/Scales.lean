/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Scales
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import IsotropicVariance.Paper.Proofs.Profiles.Scales

/-!
# The scales `Q_s` and `W_s`

`Q_s = A s^{1/2 − 1/K}` and `W_s = √(s Q_s)` (the introduction): the ratios at comparable lengths,
for the proof of Lemma `lem:localization`. The other facts are in
`IsotropicVariance.Paper.Proofs.Profiles.Scales`.
-/

@[expose] public section

open Real

open IsotropicVariance.Paper.Proofs.Profiles (Q_nonneg qExp qExp_le)
namespace IsotropicVariance.Paper.Proofs.Localization

variable {K : ℕ} {A s t c : ℝ}

lemma Q_mul_le (hA : 0 ≤ A) (hc : 1 ≤ c) (hs : 0 ≤ s) :
    Q K A (c * s) ≤ Real.sqrt c * Q K A s := by
  rw [Profiles.Q_mul (by linarith) hs, sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_right (rpow_le_rpow_of_exponent_le hc qExp_le) (Q_nonneg hA hs)

lemma one_le_W (hK : 10 ≤ K) (hA : 1 ≤ A) (hs : 1 ≤ s) : 1 ≤ W K A s := by
  unfold W
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (by nlinarith [Profiles.one_le_Q hK hA hs])

lemma W_div_sixteen (hA : 0 ≤ A) (hs : 0 ≤ s) :
    W K A s / 8 ≤ W K A (s / 16) := by
  have h16 : s / 16 = (1 / 16) * s := by ring
  have hQ : Q K A s / 4 ≤ Q K A (s / 16) := by
    rw [h16, Profiles.Q_mul (by norm_num) hs]
    have h1 : (1 / 16 : ℝ) ^ ((1 : ℝ) / 2) ≤ (1 / 16) ^ qExp K :=
      rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) qExp_le
    have h2 : (1 / 16 : ℝ) ^ ((1 : ℝ) / 2) = 1 / 4 := by
      rw [← sqrt_eq_rpow, show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, sqrt_sq (by norm_num)]
    nlinarith [Q_nonneg (K := K) hA hs]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
  unfold W
  rw [show (8 : ℝ) = Real.sqrt 64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, sqrt_sq (by norm_num)],
    ← Real.sqrt_mul' _ (by norm_num : (0 : ℝ) ≤ 64)]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [Q_nonneg (K := K) hA hs]

end IsotropicVariance.Paper.Proofs.Localization
