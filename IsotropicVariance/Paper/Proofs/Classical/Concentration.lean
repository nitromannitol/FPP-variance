/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.PassageConcentration

/-! # The concentration half of Lemma `lem:classical`

The first bound of `eq:classical`, whose two tails follow from [BLM03, Corollary 3] and
[BLM03, Theorem 7] (proof of Lemma `lem:classical`). This supplies precisely the
concentration input of `meanBound_of_concentration`. It requires only the setting; normalization
is needed for the mean half, but not for concentration.
-/

@[expose] public section
open MeasureTheory Real Set
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra

/-- The centered passage time has an `O₂(C√t)` bound on every real scale t≥1. -/
theorem classicalConcentration_holds {m : ℕ} (X : Setting m) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      Cited.IsOs X.P 2 (C * sqrt t) (fun ω => |X.TRV t ω - X.mean t|) := by
  obtain ⟨a, b, ha, hBounds⟩ := X.bounds
  obtain ⟨C, hC, hAll⟩ := exists_passage_concentration_constant X ha hBounds
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hd : dist (0 : Pt m) (t • e₁) = t := by
    simpa only [zero_smul, zero_sub, abs_neg, abs_of_nonneg ht0] using
      TimeConstant.dist_smul_e₁ (m := m) 0 t
  have hOs : Cited.IsOs X.P 2 (C * sqrt (dist (0 : Pt m) (t • e₁) + 1))
      (fun ω => |X.passTime ω 0 (t • e₁) - ∫ η, X.passTime η 0 (t • e₁) ∂X.P|) :=
    hAll 0 (t • e₁)
  rw [hd] at hOs
  have hSqrt : sqrt (t + 1) ≤ 2 * sqrt t := by
    calc
      sqrt (t + 1) ≤ sqrt (4 * t) := sqrt_le_sqrt (by linarith only [ht])
      _ = _ := by
        have h4 : sqrt (4 : ℝ) = 2 := by
          nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4), sqrt_nonneg (4 : ℝ)]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
  have hScale : C * sqrt (t + 1) ≤ (2 * C) * sqrt t := by
    calc
      _ ≤ C * (2 * sqrt t) := mul_le_mul_of_nonneg_left hSqrt hC.le
      _ = _ := by ring
  have hFinal := hOs.mono_scale (by norm_num : (0 : ℝ) ≤ 2)
    (mul_pos hC (sqrt_pos.mpr (by linarith only [ht] : (0 : ℝ) < t + 1))) hScale
  change Cited.IsOs X.P 2 ((2 * C) * sqrt t)
    (fun ω => |X.passTime ω 0 (t • e₁) - ∫ η, X.passTime η 0 (t • e₁) ∂X.P|)
  exact hFinal

end IsotropicVariance.Paper.Proofs.Classical
