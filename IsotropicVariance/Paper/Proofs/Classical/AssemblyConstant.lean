/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.Concentration

/-! # Choosing a common constant for the two halves of the classical bound

This is only the algebraic assembly for one setting. The proof of
`classicalBoundsStatement_holds` instantiates its mean input with `meanBound_of_concentration`.
-/

@[expose] public section
open MeasureTheory Real
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra

/-- Increase the concentration and mean constants to their common maximum. -/
theorem exists_common_classical_constant {m : ℕ} (X : Setting m)
    (hMean : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      0 ≤ X.mean t - t ∧ X.mean t - t ≤ C * sqrt (t * log (2 + t))) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      Cited.IsOs X.P 2 (C * sqrt t) (fun ω => |X.TRV t ω - X.mean t|) ∧
      0 ≤ X.mean t - t ∧ X.mean t - t ≤ C * sqrt (t * log (2 + t)) := by
  obtain ⟨C₁, hC₁, hConc⟩ := classicalConcentration_holds X
  obtain ⟨C₂, hC₂, hMean⟩ := hMean
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _), ?_⟩
  intro t ht
  obtain ⟨hLow, hUp⟩ := hMean t ht
  have hOs : Cited.IsOs X.P 2 (C₁ * sqrt t) (fun ω => |X.TRV t ω - X.mean t|) := hConc t ht
  have hOs' := hOs.mono_scale (by norm_num : (0 : ℝ) ≤ 2)
    (mul_pos hC₁ (sqrt_pos.mpr (zero_lt_one.trans_le ht)))
    (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (sqrt_nonneg t))
  refine ⟨hOs', hLow, hUp.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (sqrt_nonneg _)

end IsotropicVariance.Paper.Proofs.Classical
