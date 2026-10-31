/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.Cones
public import IsotropicVariance.Paper.Proofs.SlabComparison.SlabBounds

/-! # Slab coordinates and the interior cones of the endpoint surgery -/

@[expose] public section
open Set Metric
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper Infra.Slab
variable {m : ℕ}

/-- The linear coordinate normal to a slab. -/
noncomputable def slabLinear (sl : Slab m) : Pt m →ₗ[ℝ] ℝ := (slabCoordAffine sl).linear

lemma slabLinear_sub (sl : Slab m) (x y : Pt m) :
    slabLinear sl (x - y) = slabCoord sl x - slabCoord sl y :=
  (slabCoordAffine sl).linearMap_vsub x y

lemma abs_slabLinear_le (sl : Slab m) (v : Pt m) : |slabLinear sl v| ≤ ‖v‖ := by
  have hh := (lipschitzWith_slabCoord sl).dist_le_mul v 0
  rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_zero_right] at hh
  simpa only [← slabLinear_sub, sub_zero] using hh

lemma coord_face₀ (sl : Slab m) {x : Pt m} (hx : x ∈ sl.face₀) : slabCoord sl x = 0 := by
  obtain ⟨x, hx, rfl⟩ := hx
  simpa [slabCoord] using hx

lemma coord_face₁ (sl : Slab m) {x : Pt m} (hx : x ∈ sl.face₁) :
    slabCoord sl x = sl.width := by
  obtain ⟨x, hx, rfl⟩ := hx
  simpa [slabCoord] using hx

/-- The chord across two faces of slope at most two has normal unit component at least `1/3`.
The weaker rational bound simplifies the cone estimates. -/
lemma slabLinear_direction_chord (sl : Slab m) (hw : 0 < sl.width) {x y : Pt m}
    (hx : x ∈ sl.face₀) (hy : y ∈ sl.face₁) (hs : sl.slope x y ≤ 2) :
    1 / 3 ≤ slabLinear sl (direction (y - x)) := by
  have hwle : sl.width ≤ dist x y := by
    have h := abs_slabLinear_le sl (y - x)
    rw [slabLinear_sub, coord_face₁ sl hy, coord_face₀ sl hx, sub_zero,
      abs_of_pos hw, ← dist_eq_norm'] at h
    exact h
  have hd : 0 < ‖y - x‖ := by rw [← dist_eq_norm']; exact hw.trans_le hwle
  have hle := dist_le_three_mul_width sl hw hs
  rw [direction, map_smul, smul_eq_mul, slabLinear_sub, coord_face₁ sl hy, coord_face₀ sl hx,
    sub_zero]
  rw [← div_eq_inv_mul, le_div_iff₀ hd]
  rw [← dist_eq_norm']
  linarith

/-- A lower bound on both face coordinates is a lower bound on distance to their union. -/
lemma le_infDist_faces (sl : Slab m) {p : Pt m} {r : ℝ}
    (h0 : r ≤ slabCoord sl p) (h1 : r ≤ sl.width - slabCoord sl p) :
    r ≤ infDist p sl.faces := by
  have hn : sl.faces.Nonempty := ⟨sl.motion 0, 0, by simp [Pt.lon], rfl⟩
  apply (Metric.le_infDist hn).mpr
  intro q hq
  have hLip := (lipschitzWith_slabCoord sl).dist_le_mul p q
  rw [Real.dist_eq, NNReal.coe_one, one_mul] at hLip
  rcases (mem_slab_faces_iff sl).mp hq with hq | hq
  · rw [hq, sub_zero] at hLip
    exact h0.trans ((le_abs_self _).trans hLip)
  · rw [hq] at hLip
    have hh := (neg_le_abs _).trans hLip
    linarith

end IsotropicVariance.Paper.Proofs.SlabComparison
