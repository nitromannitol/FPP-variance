/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.Directions
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! # From distances of unit directions to angles

The dyadic estimate in the proof of Lemma `lem:straight` is carried out in Lean on the
distance of the unit directions, `‖u/|u| − v/|v|‖`. The statement of the lemma is about the angle
`∠(u, v)`. For unit vectors the two are related by `‖u/|u| − v/|v|‖² = 2 − 2 cos ∠(u, v)`.
-/

@[expose] public section
open InnerProductGeometry
namespace IsotropicVariance.Paper.Proofs.Straight
open SlabComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `cos(1/10) ≤ 249/250`, by the Taylor bound of the cosine. -/
lemma cos_one_tenth_le : Real.cos (1 / 10) ≤ 249 / 250 := by
  have hx : |(1 / 10 : ℝ)| = 1 / 10 := abs_of_pos (by norm_num)
  have h := (abs_le.mp (Real.cos_bound (x := 1 / 10) (by rw [hx]; norm_num))).2
  rw [hx] at h
  norm_num at h
  linarith only [h]

/-- The chord of two nonzero vectors: `‖u/|u| − v/|v|‖² = 2 − 2 cos ∠(u, v)`. -/
lemma norm_direction_sub_sq {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖direction u - direction v‖ ^ 2 = 2 - 2 * Real.cos (angle u v) := by
  have hu0 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hinner : inner ℝ (direction u) (direction v) = Real.cos (angle u v) := by
    rw [cos_angle]
    simp only [direction, real_inner_smul_left, real_inner_smul_right]
    field_simp
  rw [norm_sub_sq_real, norm_direction hu, norm_direction hv, hinner]
  ring

/-- Directions at distance at most `1/24` make an angle at most `1/10`: the conclusion of
Lemma `lem:straight`. -/
theorem angle_le_of_direction_close {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : ‖direction u - direction v‖ ≤ 1 / 24) : angle u v ≤ 1 / 10 := by
  by_contra hlt
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 1 / 10) (by norm_num) (angle_le_pi u v)
    (not_le.mp hlt)
  have hsq := norm_direction_sub_sq hu hv
  have hδ : ‖direction u - direction v‖ ^ 2 ≤ (1 / 24) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  norm_num at hδ
  linarith only [hcos, hsq, hδ, cos_one_tenth_le]

end IsotropicVariance.Paper.Proofs.Straight
