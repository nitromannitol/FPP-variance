/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Direction changes controlled by Euclidean triangle excess -/

@[expose] public section
open scoped InnerProductSpace
namespace IsotropicVariance.Paper.Proofs.SlabComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unit direction of a nonzero displacement (zero is assigned direction zero). -/
noncomputable def direction (v : E) : E := ‖v‖⁻¹ • v

lemma norm_direction {v : E} (hv : v ≠ 0) : ‖direction v‖ = 1 := by
  simp only [direction, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- The normalized direction change squared is bounded by twice the triangle excess,
relative to the first radius. This avoids introducing angle functions into the dyadic proof. -/
theorem direction_change_sq_le {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖direction u - direction v‖ ^ 2 * ‖u‖ ≤ 2 * (‖u‖ + ‖v - u‖ - ‖v‖) := by
  have hu0 := norm_pos_iff.mpr hu
  have hv0 := norm_pos_iff.mpr hv
  have heq : ⟪direction u, direction v⟫_ℝ * ‖u‖ * ‖v‖ = ⟪u, v⟫_ℝ := by
    simp only [direction, real_inner_smul_left, real_inner_smul_right]
    field_simp [hu0.ne', hv0.ne']
  have hsq : ‖direction u - direction v‖ ^ 2 = 2 - 2 * ⟪direction u, direction v⟫_ℝ := by
    rw [norm_sub_sq_real, norm_direction hu, norm_direction hv]
    ring
  have hsq' := congrArg (fun t : ℝ => t * ‖u‖ * ‖v‖) hsq
  have hc := real_inner_le_norm (v - u) v
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hc
  apply (mul_le_mul_iff_of_pos_right hv0).mp
  nlinarith

end IsotropicVariance.Paper.Proofs.SlabComparison
