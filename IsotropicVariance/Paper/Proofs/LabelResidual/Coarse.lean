/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.CommonCouplings
public import IsotropicVariance.Paper.Proofs.Gain.Steps
public import IsotropicVariance.Paper.Contracts.Blocks

/-!
# A uniform coarse bound on the label energy

Every label resampling is a block coupling. The second bound in equation `eq:rewardmoment` therefore
gives a uniform bound on the offset-averaged label energy. This is the finite coarse bound used when
choosing the two-parameter modulus in the proof of Lemma `lem:residual`; it is not the small
residual estimate, equation `eq:residual`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.LabelResidual

open Contracts Gain

/-- Averaging constants over the `K` independent uniform offsets changes nothing. -/
theorem average_offsets_le {m K L : ℕ} (hL : 1 ≤ L)
    (f : (Fin K → Fin m → Fin L) → ℝ≥0∞) {c : ℝ≥0∞} (h : ∀ o, f o ≤ c) :
    ((L : ℝ≥0∞) ^ (m * K))⁻¹ * ∑ o, f o ≤ c := by
  have hcard : (Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞) =
      (L : ℝ≥0∞) ^ (m * K) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_fin, ← pow_mul, Nat.cast_pow]
  calc
    _ ≤ ((L : ℝ≥0∞) ^ (m * K))⁻¹ * ∑ _o : Fin K → Fin m → Fin L, c :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun o _ => h o)
    _ = c := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← mul_assoc,
        ENNReal.inv_mul_cancel (by exact_mod_cast (pow_ne_zero _ (by omega : L ≠ 0)))
          (ENNReal.pow_ne_top (by simp)), one_mul]

end IsotropicVariance.Paper.Proofs.LabelResidual
