/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! # Physical sizes of targets in the induction domain

The slope `t₀` is fixed data: a target in `𝒟(s)`, the domain centred at `s t₀`, has physical
transverse norm at most `(‖t₀‖ + 1) s` for `s ≥ 1` (the bound `|y|/N ≤ |t₀| + 1` behind the path
of at most `C` edges from `(4s, 4y₀)` to `(N, y)` in the proof of Proposition `prop:induction`).
-/

@[expose] public section
namespace CurvatureVariance.Paper.Mean

/-- A target `y ∈ 𝒟(s)`, `s ≥ 1`, has transverse norm at most `(‖t₀‖ + 1) s`. -/
theorem norm_transverse_le_of_mem {m : ℕ} {M : Model m} (hM : M.Standing)
    {s : ℝ} (hs : 1 ≤ s) {y : Fin m → ℤ} (hy : y ∈ premiseDomain M s) :
    ‖transversePoint y‖ ≤ (‖M.t₀‖ + 1) * s := by
  have hr : s ^ ((3 : ℝ) / 4 + M.δ / 100) ≤ s := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hs
      (show (3 : ℝ) / 4 + M.δ / 100 ≤ 1 by linarith only [hM.delta_le_one])
  have hh := norm_le_norm_sub_add (transversePoint y) (s • M.t₀)
  rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans hs)] at hh
  linarith only [hh, hy.trans hr]

/-- A fitting model has a physical domain bound using only the common slope bound. -/
theorem norm_transverse_le_of_mem_fit {m : ℕ} {bd : Bounds m} {M : Model m}
    (hM : M.Standing) (hfit : M.Fits bd) {s : ℝ} (hs : 1 ≤ s)
    {y : Fin m → ℤ} (hy : y ∈ premiseDomain M s) :
    ‖transversePoint y‖ ≤ (bd.T + 1) * s :=
  (norm_transverse_le_of_mem hM hs hy).trans
    (mul_le_mul_of_nonneg_right (add_le_add hfit.t₀_le le_rfl) (zero_le_one.trans hs))

/-- A transverse norm bound gives a bound for the physical coordinate path length. -/
theorem oneNorm_le_of_transverse_bound {m s : ℕ} {y : Fin m → ℤ} {B : ℝ}
    (hB : 1 ≤ B) (hy : ‖transversePoint y‖ ≤ B * s) :
    oneNorm ((s : ℤ), y) ≤ (m + 1 : ℝ) * B * s := by
  have hcoord (i : Fin m) : ((y i).natAbs : ℝ) ≤ B * s := by
    have hh := PiLp.norm_apply_le (transversePoint y) i
    change ‖(y i : ℝ)‖ ≤ ‖transversePoint y‖ at hh
    simpa only [Real.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs] using hh.trans hy
  have hs : (s : ℝ) ≤ B * s := le_mul_of_one_le_left (Nat.cast_nonneg s) hB
  unfold oneNorm
  push_cast
  simp only [Int.natAbs_natCast]
  calc
    (s : ℝ) + ∑ i : Fin m, ((y i).natAbs : ℝ) ≤ B * s + ∑ _i : Fin m, B * s :=
      add_le_add hs (Finset.sum_le_sum fun i _ => hcoord i)
    _ = (m + 1 : ℝ) * B * s := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end CurvatureVariance.Paper.Mean
