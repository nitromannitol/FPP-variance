/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Summing positive changes supported on visited neighborhoods

The approximation error appears on every coordinate; its contribution vanishes
when near-optimality errors tend to zero for a fixed finite family.
-/

@[expose] public section
open scoped BigOperators
namespace IsotropicVariance.Paper.Proofs.Classical

/-- Sum positive squared changes bounded by `C` on `V` and by an error everywhere. -/
theorem sum_positive_sq_le_card {ι : Type*} [DecidableEq ι] (J V : Finset ι) (hV : V ⊆ J)
    (d : ι → ℝ) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hd : ∀ i ∈ J, d i ≤ (if i ∈ V then C else 0) + ε) :
    (∑ i ∈ J, max (d i) 0 ^ 2) ≤ 2 * C ^ 2 * V.card + 2 * ε ^ 2 * J.card := by
  have hPoint (i : ι) (hi : i ∈ J) : max (d i) 0 ^ 2 ≤ (if i ∈ V then 2 * C ^ 2 else 0) + 2 * ε ^ 2 := by
    by_cases h : i ∈ V
    · have hm : max (d i) 0 ≤ C + ε := max_le (by simpa only [ite_eq_left h] using hd i hi) (add_nonneg hC hε)
      have hh := pow_le_pow_left₀ (le_max_right (d i) 0) hm 2
      simp only [ite_eq_left h]
      nlinarith only [hh, sq_nonneg (C - ε)]
    · have hm : max (d i) 0 ≤ ε := max_le (by simpa only [ite_eq_right h, zero_add] using hd i hi) hε
      have hh := pow_le_pow_left₀ (le_max_right (d i) 0) hm 2
      simp only [ite_eq_right h, zero_add]
      nlinarith only [hh, sq_nonneg ε]
  have hFilter : J.filter (fun i => i ∈ V) = V := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hV h, h⟩⟩
  have hSum : (∑ i ∈ J, if i ∈ V then 2 * C ^ 2 else 0) = 2 * C ^ 2 * V.card := by
    rw [← Finset.sum_filter, hFilter, Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    _ ≤ ∑ i ∈ J, ((if i ∈ V then 2 * C ^ 2 else 0) + 2 * ε ^ 2) := Finset.sum_le_sum hPoint
    _ = _ := by rw [Finset.sum_add_distrib, hSum, Finset.sum_const, nsmul_eq_mul]; ring

end IsotropicVariance.Paper.Proofs.Classical
