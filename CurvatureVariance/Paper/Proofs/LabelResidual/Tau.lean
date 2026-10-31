/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Real
import CurvatureVariance.Paper.Proofs.Gain.Step2Tail
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The proof of Lemma `lem:residual`: averages over the offsets of one slab

In the second paragraph of [AB26, proof of Lemma 6.3], with equation `eq:rewardmoment` in place
of [AB26, (6.2)], the reward is bounded off and on the event `E`, the offsets being random
(`Proofs.Residual.offsetAvg_reward_pow_le`). The bound on the probability of `E`
(`Proofs.Residual.measure_residualEvent_le`) counts the offsets of one slab for which a ball lies
in the core of no block; `avg_comp_eval` reduces the average over the offset families of a function
of the offset of one slab to its average over the offsets of that slab.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain.LabelResidual

variable {m : ℕ}

/-- The average over the offset families of a function of the offset of one slab is its average
over the offsets of that slab. -/
theorem avg_comp_eval {K L : ℕ} (hL : 1 ≤ L) (i : Fin K) (g : (Fin m → Fin L) → ℝ≥0∞) :
    ((Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞))⁻¹ * ∑ σ : Fin K → Fin m → Fin L, g (σ i) =
      ((Fintype.card (Fin m → Fin L) : ℝ≥0∞))⁻¹ * ∑ s, g s := by
  classical
  have hne : Nonempty (Fin m → Fin L) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hsum : ∑ σ : Fin K → Fin m → Fin L, g (σ i) =
      (Fintype.card ({j : Fin K // j ≠ i} → Fin m → Fin L) : ℝ≥0∞) * ∑ s, g s := by
    rw [← (Equiv.piSplitAt i (fun _ : Fin K => Fin m → Fin L)).symm.sum_comp,
      Fintype.sum_prod_type]
    simp [Equiv.piSplitAt_symm_apply, Finset.mul_sum]
  have hcard : Fintype.card (Fin K → Fin m → Fin L) =
      Fintype.card (Fin m → Fin L) * Fintype.card ({j : Fin K // j ≠ i} → Fin m → Fin L) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr (Equiv.piSplitAt i (fun _ : Fin K => Fin m → Fin L))
  have hS0 : (Fintype.card (Fin m → Fin L) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hR0 : (Fintype.card ({j : Fin K // j ≠ i} → Fin m → Fin L) : ℝ≥0∞) ≠ 0 := by
    have : Nonempty ({j : Fin K // j ≠ i} → Fin m → Fin L) := ⟨fun _ => hne.some⟩
    exact_mod_cast Fintype.card_ne_zero
  rw [hsum, hcard, Nat.cast_mul, ENNReal.mul_inv (Or.inl hS0) (Or.inl (ENNReal.natCast_ne_top _)),
    mul_assoc, ← mul_assoc _ (Fintype.card ({j : Fin K // j ≠ i} → Fin m → Fin L) : ℝ≥0∞),
    ENNReal.inv_mul_cancel hR0 (ENNReal.natCast_ne_top _), one_mul]

end CurvatureVariance.Paper.Gain.LabelResidual
