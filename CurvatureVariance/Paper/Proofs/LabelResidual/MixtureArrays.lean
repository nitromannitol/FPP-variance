/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.LabelResidual.Mixture
public import CurvatureVariance.Paper.Proofs.Gain.RRTuples
public import CurvatureVariance.Paper.Proofs.ReplacementResponses.Arrays

/-!
# The average over independent uniform offsets

The first paragraph of [AB26, proof of Lemma 6.3], which the proof of Lemma `lem:residual`
follows: with independent uniform offsets, equation `eq:chainsum` (from [AB26, Lemma 2.4] and
equation `eq:rowenergy`), applied to the arrays `Y_i/η`, gives `E ∑ᵢ Y_i(J_{i−1}, J_i) ≤ C η K`.
That step is `Proofs.Residual.offsetAvg_iSup_reward_le`, on the mixture over uniform offsets
(`offsetMixture`, under which the reward arrays are independent over the slabs,
`iIndepFun_offsetMixture`). This file has the average `offsetAvg` over the offset families
`σ : Fin K → Fin m → Fin L` and its bound by a constant (`offsetAvg_le_const`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain.LabelResidual

open CurvatureVariance.Paper CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-- The average over the offset families `σ : Fin K → Fin m → Fin L`. -/
noncomputable def offsetAvg {K L : ℕ} (E : (Fin K → Fin m → Fin L) → ℝ≥0∞) : ℝ≥0∞ :=
  ((Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞))⁻¹ * ∑ σ, E σ

/-- The average over offset families of a constant bound. -/
theorem offsetAvg_le_const {K L : ℕ} (hL : 1 ≤ L) {E : (Fin K → Fin m → Fin L) → ℝ≥0∞}
    {c : ℝ≥0∞} (h : ∀ σ, E σ ≤ c) : offsetAvg E ≤ c := by
  unfold offsetAvg
  have hne : Nonempty (Fin m → Fin L) := ⟨fun _ => ⟨0, by omega⟩⟩
  have : Nonempty (Fin K → Fin m → Fin L) := ⟨fun _ => hne.some⟩
  have hcard : (Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc ((Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞))⁻¹ * ∑ σ, E σ
      ≤ ((Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞))⁻¹ * ∑ _σ : Fin K → Fin m → Fin L, c := by
        gcongr with σ; exact h σ
    _ = c := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel hcard (ENNReal.natCast_ne_top _), one_mul]

end CurvatureVariance.Paper.Gain.LabelResidual
