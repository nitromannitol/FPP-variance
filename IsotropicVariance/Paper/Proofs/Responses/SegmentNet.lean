/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-!
# Unit nets on segments

The net has at most the segment length plus two points, as used in the Gaussian cell sum of the
proof of Lemma `lem:blocks`.
-/

@[expose] public section

open Set

namespace IsotropicVariance.Paper.Proofs.Responses

/-- A segment admits at most `length + 2` unit-net samples. -/
theorem segment_unit_net {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (p q : V) :
    ∃ N : ℕ, (N + 1 : ℝ) ≤ ‖q - p‖ + 2 ∧
      ∀ z ∈ segment ℝ p q, ∃ n ∈ Finset.range (N + 1),
        dist z (p + ((n : ℝ) / N) • (q - p)) ≤ 1 := by
  let N : ℕ := ⌊‖q - p‖⌋₊ + 1
  have hN : 0 < (N : ℝ) := by dsimp only [N]; positivity
  have hNd : ‖q - p‖ < (N : ℝ) := by simpa only [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ‖q - p‖
  have hNl : (N : ℝ) ≤ ‖q - p‖ + 1 := by
    dsimp only [N]
    push_cast
    linarith only [Nat.floor_le (norm_nonneg (q - p))]
  refine ⟨N, by linarith only [hNl], ?_⟩
  intro z hz
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  let n : ℕ := ⌊b * N⌋₊
  have hbn : 0 ≤ b * (N : ℝ) := mul_nonneg hb hN.le
  have hnlo : (n : ℝ) ≤ b * N := Nat.floor_le hbn
  have hnhi : b * (N : ℝ) < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnN : n ≤ N := by
    apply (Nat.cast_le (α := ℝ)).mp
    have hb1 : b ≤ 1 := by linarith only [ha, hab]
    exact hnlo.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb1 hN.le)
  refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hnN), ?_⟩
  have heq : a • p + b • q - (p + ((n : ℝ) / N) • (q - p)) =
      (b - (n : ℝ) / N) • (q - p) := by
    have haeq : a = 1 - b := by linarith only [hab]
    rw [haeq]
    module
  have hd0 : 0 ≤ b - (n : ℝ) / N := by
    have h := (div_le_iff₀ hN).mpr hnlo
    linarith only [h]
  have hd1 : (b - (n : ℝ) / N) * N ≤ 1 := by
    have hid : (b - (n : ℝ) / N) * N = b * N - n := by field_simp
    rw [hid]
    linarith only [hnhi]
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd0]
  exact (mul_le_mul_of_nonneg_left hNd.le hd0).trans hd1

end IsotropicVariance.Paper.Proofs.Responses
