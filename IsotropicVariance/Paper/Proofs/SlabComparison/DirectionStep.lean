/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.Directions
public import IsotropicVariance.Paper.Proofs.SlabComparison.Excess

/-! # One step of the dyadic direction estimate -/

@[expose] public section
namespace IsotropicVariance.Paper.Proofs.SlabComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At radius `r ≥ S²`, one ordered near-geodesic step changes direction by at most a
fourth-power error proportional to `S²/r`. The next radius need only be at most `2r`. -/
theorem direction_step_fourth {T : E → E → ℝ} {A S r : ℝ}
    (hA : 0 ≤ A) (hS : 1 ≤ S) (hr : 0 < r) (hscale : S ^ 2 ≤ r)
    {a u v : E} (hu : dist a u = r) (hv : v ≠ a) (hv2 : dist a v ≤ 2 * r)
    (hau : |T a u - dist a u| ≤ A * (S * Real.sqrt (dist a u) + S ^ 2))
    (huv : |T u v - dist u v| ≤ A * (S * Real.sqrt (dist u v) + S ^ 2))
    (hav : |T a v - dist a v| ≤ A * (S * Real.sqrt (dist a v) + S ^ 2))
    (hdefect : T a u + T u v ≤ T a v + 1) :
    ‖direction (u - a) - direction (v - a)‖ ^ 4 * r ≤ (6 * (3 * A + 1)) ^ 2 * S ^ 2 := by
  have hu0 : u ≠ a := by
    intro h
    rw [h, dist_self] at hu
    linarith
  have hS0 : 0 ≤ S := le_trans zero_le_one hS
  have huv3 : dist u v ≤ 3 * r := by
    have h := dist_triangle u a v
    rw [dist_comm u a, hu] at h
    linarith
  have hex := triangle_excess_le hA hS hau huv hav hdefect
    (show dist a u ≤ 3 * r by rw [hu]; linarith) huv3
    (show dist a v ≤ 3 * r by linarith)
  have hsr : S ≤ Real.sqrt r := by
    nlinarith [Real.sq_sqrt hr.le, Real.sqrt_nonneg r]
  have hroot : Real.sqrt (3 * r) ≤ 2 * Real.sqrt r := by
    nlinarith [Real.sq_sqrt hr.le, Real.sq_sqrt (show 0 ≤ 3 * r by positivity),
      Real.sqrt_nonneg r, Real.sqrt_nonneg (3 * r)]
  have hmul1 := mul_le_mul_of_nonneg_left hroot hS0
  have hmul2 := mul_le_mul_of_nonneg_left hsr hS0
  have hex' : dist a u + dist u v - dist a v ≤ 3 * (3 * A + 1) * S * Real.sqrt r := by
    nlinarith
  have hdir := direction_change_sq_le (sub_ne_zero.mpr hu0) (sub_ne_zero.mpr hv)
  have hnorm : ‖u - a‖ = r := by simpa only [dist_eq_norm'] using hu
  rw [hnorm, sub_sub_sub_cancel_right] at hdir
  have hdir' : ‖direction (u - a) - direction (v - a)‖ ^ 2 * r ≤
      (6 * (3 * A + 1)) * S * Real.sqrt r := by
    simp only [dist_eq_norm'] at hex'
    nlinarith
  have hsq := mul_self_le_mul_self (by positivity :
    0 ≤ ‖direction (u - a) - direction (v - a)‖ ^ 2 * r) hdir'
  apply (mul_le_mul_iff_of_pos_right hr).mp
  calc
    _ = (‖direction (u - a) - direction (v - a)‖ ^ 2 * r) ^ 2 := by ring
    _ ≤ ((6 * (3 * A + 1)) * S * Real.sqrt r) ^ 2 := by simpa only [pow_two] using hsq
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hr.le]

end IsotropicVariance.Paper.Proofs.SlabComparison
