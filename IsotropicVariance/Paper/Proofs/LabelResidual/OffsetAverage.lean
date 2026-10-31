/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.Offsets
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Averaging the exceptional-event contribution over offsets

Holder's `3/4` power in the near-pair moment estimate is concave. Its average over offsets
is bounded by the same power of the average exceptional probability. The deterministic
part of that probability is controlled by the literal offset count in `Offsets`.
-/

@[expose] public section

open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.LabelResidual

/-- Concavity of the `3/4` power for finite extended-valued probability averages. -/
theorem sum_mul_three_quarters_rpow_le {I : Type*} [Fintype I]
    (w a : I → ℝ≥0∞) (hw : ∑ i, w i = 1) :
    ∑ i, w i * a i ^ (3 / 4 : ℝ) ≤ (∑ i, w i * a i) ^ (3 / 4 : ℝ) := by
  have h := ENNReal.rpow_arith_mean_le_arith_mean_rpow (s := Finset.univ)
    w (fun i => a i ^ (3 / 4 : ℝ)) hw (by norm_num : (1 : ℝ) ≤ 4 / 3)
  have h' := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 3 / 4)
  simpa only [← ENNReal.rpow_mul, show (3 / 4 : ℝ) * (4 / 3) = 1 by norm_num,
    show (4 / 3 : ℝ) * (3 / 4) = 1 by norm_num, ENNReal.rpow_one] using h'

/-- The fraction of bad offsets, as an extended real, has the same explicit bound. -/
theorem average_badOffsets_le {m : ℕ} (L : ℕ+) {margin diam : ℝ}
    (hm : 0 ≤ margin) (hd : 0 ≤ diam) (a : Fin m → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (hS : ∀ y ∈ S, ∀ k, a k ≤ y k ∧ y k ≤ a k + diam) :
    ((OffsetGeometry.badOffsets L margin S).card : ℝ≥0∞) /
      (Fintype.card (Fin m → Fin (L : ℕ)) : ℝ≥0∞) ≤
      ENNReal.ofReal ((m : ℝ) * (diam + 2 * margin + 2) / (L : ℝ)) := by
  let _ : Nonempty (Fin m → Fin (L : ℕ)) := ⟨fun _ => ⟨0,L.pos⟩⟩
  have hc : (0 : ℝ) < Fintype.card (Fin m → Fin (L : ℕ)) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have h := OffsetGeometry.badOffsets_probability_le L hm hd a S hS
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos hc]
  exact ENNReal.ofReal_le_ofReal h

end IsotropicVariance.Paper.Proofs.LabelResidual
