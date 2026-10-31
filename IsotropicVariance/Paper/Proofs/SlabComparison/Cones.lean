/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.Directions
public import IsotropicVariance.Infra.Measurability.SlabTime
import Mathlib.Tactic.FieldSimp
import IsotropicVariance.Paper.Proofs.Profiles.TreeGeometry

/-! # Linear coordinates of vectors in a narrow cone

These deterministic estimates turn the unit-direction control of the dyadic argument into
bounds on the coordinate across a slab, and on transverse increments of a slab chain.
-/

@[expose] public section
open scoped InnerProductSpace
open IsotropicVariance.Paper.Proofs.Profiles (abs_lon_le_norm)
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Multiplying the normalized direction by the radius recovers the vector, including zero. -/
lemma norm_smul_direction (v : E) : ‖v‖ • direction v = v := by
  by_cases hv : v = 0
  · simp [hv, direction]
  · simp only [direction, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

/-- A coordinate that is bounded below on a reference direction remains positive in a narrow
cone about that direction. The coordinate need only be nonexpansive. -/
theorem coordinate_lower_of_direction_close (L : E →ₗ[ℝ] ℝ)
    (hL : ∀ v, |L v| ≤ ‖v‖) {v w : E} {c ε : ℝ}
    (hw : c ≤ L w) (hclose : ‖direction v - w‖ ≤ ε) :
    (c - ε) * ‖v‖ ≤ L v := by
  have h := (abs_le.mp ((hL (direction v - w)).trans hclose)).1
  rw [map_sub] at h
  have hdir : c - ε ≤ L (direction v) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hdir (norm_nonneg v)
  have heq := congrArg L (norm_smul_direction v)
  rw [map_smul, smul_eq_mul] at heq
  nlinarith [hmul]

/-- Directional proximity to `e₁` forces a positive longitudinal increment. -/
theorem lon_lower_of_direction_close {m : ℕ} {v : Pt m} {ε : ℝ}
    (hclose : ‖direction v - (e₁ : Pt m)‖ ≤ ε) :
    (1 - ε) * ‖v‖ ≤ Pt.lon v := by
  let L : Pt m →ₗ[ℝ] ℝ :=
    { toFun := Pt.lon
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact coordinate_lower_of_direction_close L abs_lon_le_norm (by change (1 : ℝ) ≤ 1; exact le_rfl) hclose

/-- The transverse part is small when the direction is close to the longitudinal axis. -/
theorem tr_upper_of_direction_close {m : ℕ} {v : Pt m} {ε : ℝ}
    (hclose : ‖direction v - (e₁ : Pt m)‖ ≤ ε) :
    ‖Pt.tr v‖ ≤ ε * ‖v‖ := by
  have ht : ‖Pt.tr (direction v)‖ ≤ ε := by
    have h := (WithLp.norm_snd_le ℝ (direction v - (e₁ : Pt m))).trans hclose
    change ‖Pt.tr (direction v) - 0‖ ≤ ε at h
    simpa only [sub_zero] using h
  have heq := congrArg Pt.tr (norm_smul_direction v)
  change ‖v‖ • Pt.tr (direction v) = Pt.tr v at heq
  rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
  nlinarith [mul_le_mul_of_nonneg_left ht (norm_nonneg v)]

end IsotropicVariance.Paper.Proofs.SlabComparison
