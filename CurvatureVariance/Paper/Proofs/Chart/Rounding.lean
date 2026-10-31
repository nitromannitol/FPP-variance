/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Equation `eq:rounding`: rounding inside a ball

**The rounding fact `eq:rounding`** (Section `sec:prelim`): for `c, x ∈ ℝ^{d-1}` and
`R ≥ 2√(d−1)` with `|x − c| ≤ R`, there is `z ∈ ℤ^{d-1}` with `|z − c| ≤ R` and
`|z − x| ≤ 2√(d−1)`.

The paper takes a nearest lattice point to the point of `[x, c]` at distance
`min(|x − c|, √(d−1))` from `x`. Here `x` is moved radially toward `c` into the ball of radius
`R − √(d−1)`, if needed (`exists_radial`, a move of at most `√(d−1)`), then each coordinate is
rounded to the nearest integer (`norm_transversePoint_round_sub_le_half`, a move of at most
`√(d−1)/2`).
-/

@[expose] public section

namespace CurvatureVariance.Paper.Chart

open CurvatureVariance.Paper

variable {m : ℕ}

/-- Coordinatewise nearest rounding moves a point of `ℝ^m` by at most `√m/2`. -/
theorem norm_transversePoint_round_sub_le_half (y : EuclideanSpace ℝ (Fin m)) :
    ‖transversePoint (fun j => round (y j)) - y‖ ≤ Real.sqrt m / 2 := by
  rw [EuclideanSpace.norm_eq, show Real.sqrt m / 2 = Real.sqrt (m * (1 / 2) ^ 2) by
    rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq (by norm_num)]; ring]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖(transversePoint (fun j => round (y j)) - y) i‖ ^ 2
        ≤ ∑ _i : Fin m, ((1 : ℝ) / 2) ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        have h := abs_sub_round (y i)
        rw [abs_sub_comm] at h
        simpa [transversePoint, Real.norm_eq_abs] using
          pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = m * (1 / 2) ^ 2 := by simp

/-- The radial move: a point `x` with `|x − c| ≤ R` moves toward `c` into the ball of radius
`ρ ≤ R`, by at most `R − ρ`. -/
theorem exists_radial (c x : EuclideanSpace ℝ (Fin m)) {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    (hx : ‖x - c‖ ≤ R) : ∃ y : EuclideanSpace ℝ (Fin m), ‖y - c‖ ≤ ρ ∧ ‖y - x‖ ≤ R - ρ := by
  by_cases h : ‖x - c‖ ≤ ρ
  · exact ⟨x, h, by simp; linarith⟩
  rw [not_le] at h
  have hpos : 0 < ‖x - c‖ := lt_of_le_of_lt hρ h
  refine ⟨c + (ρ / ‖x - c‖) • (x - c), ?_, ?_⟩
  · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ hpos.ne']
  · have hle : ρ / ‖x - c‖ ≤ 1 := (div_le_one hpos).mpr h.le
    have heq : c + (ρ / ‖x - c‖) • (x - c) - x = (ρ / ‖x - c‖ - 1) • (x - c) := by
      rw [sub_smul, one_smul]; abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith), neg_sub, sub_mul,
      one_mul, div_mul_cancel₀ _ hpos.ne']
    linarith

/-- **The rounding fact `eq:rounding`** (rounding inside a ball). -/
theorem roundingStatement_holds : Contracts.RoundingStatement m := by
  intro c x R hR hx
  have hs := Real.sqrt_nonneg (m : ℝ)
  obtain ⟨y, hyc, hyx⟩ := exists_radial c x (ρ := R - Real.sqrt m) (by linarith) (by linarith) hx
  have hz := norm_transversePoint_round_sub_le_half y
  refine ⟨fun j => round (y j), ?_, ?_⟩
  · calc ‖transversePoint (fun j => round (y j)) - c‖
          = ‖(transversePoint (fun j => round (y j)) - y) + (y - c)‖ := by
            rw [sub_add_sub_cancel]
      _ ≤ ‖transversePoint (fun j => round (y j)) - y‖ + ‖y - c‖ := norm_add_le _ _
      _ ≤ R := by linarith
  · calc ‖transversePoint (fun j => round (y j)) - x‖
          = ‖(transversePoint (fun j => round (y j)) - y) + (y - x)‖ := by
            rw [sub_add_sub_cancel]
      _ ≤ ‖transversePoint (fun j => round (y j)) - y‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ 2 * Real.sqrt m := by linarith

end CurvatureVariance.Paper.Chart
