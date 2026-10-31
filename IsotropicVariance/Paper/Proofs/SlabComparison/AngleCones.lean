/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.ChainDirections
public import IsotropicVariance.Paper.Proofs.SlabComparison.SlabGeometry
public import IsotropicVariance.Paper.Proofs.Straight.Angle

/-! # From the angles of Lemma `lem:straight` to the cones of Lemma `lem:slab`

The two geometric facts of the proof of Lemma `lem:slab`, for the angles of Lemma `lem:straight`.

* `interior_of_endpoint_angles`, in the proof of equation `eq:slab`: a point at angle at most
  `1/10` from the segment `[x, y]` at both ends, far from both, is inside the slab, at distance more
  than one from the faces.
* `tr_le_lon_of_angle_le`, in the proof of equation `eq:columns`: a vector at angle at most `1/5`
  from `e₁` has slope at most `1/4`.

Both are carried out on the distance of the unit directions: `‖u/|u| − v/|v|‖ ≤ ∠(u, v)`.
-/

@[expose] public section
open Set Metric InnerProductGeometry
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper Infra.Slab
open Straight (norm_direction_sub_sq)
variable {m : ℕ}

/-- The chord of two directions is at most their angle. -/
theorem norm_direction_sub_le_of_angle_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) {θ : ℝ} (hθ : 0 ≤ θ)
    (h : angle u v ≤ θ) : ‖direction u - direction v‖ ≤ θ := by
  have hsq := norm_direction_sub_sq hu hv
  have hcos := Real.one_sub_sq_div_two_le_cos (x := angle u v)
  have hangle : angle u v ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (angle_nonneg u v) h 2
  exact (sq_le_sq₀ (norm_nonneg _) hθ).mp (by linarith only [hsq, hcos, hangle])

/-- **The middle of a near-geodesic is inside the slab** (proof of equation `eq:slab`): a point
`p` at distance at least `9` from `x` and `y`, on the two faces at slope at most two, with
`∠(p − x, y − x) ≤ 1/10` and `∠(p − y, x − y) ≤ 1/10`, lies in the slab, at distance more than one
from the faces. -/
theorem interior_of_endpoint_angles (sl : Slab m) (hw : 0 < sl.width) {x y p : Pt m}
    (hx : x ∈ sl.face₀) (hy : y ∈ sl.face₁) (hs : sl.slope x y ≤ 2)
    (hxp : 9 ≤ dist x p) (hyp : 9 ≤ dist y p)
    (hforward : angle (p - x) (y - x) ≤ 1 / 10)
    (hbackward : angle (p - y) (x - y) ≤ 1 / 10) :
    p ∈ sl.set ∧ 1 < infDist p sl.faces := by
  have hdir (a b : Pt m) (hab : 9 ≤ dist a b) : b - a ≠ 0 := by
    intro h
    rw [dist_eq_norm', h, norm_zero] at hab
    norm_num at hab
  have hxy : y - x ≠ 0 := fun h => by
    have hdiff := slabLinear_sub sl y x
    rw [h, map_zero, coord_face₁ sl hy, coord_face₀ sl hx, sub_zero] at hdiff
    linarith only [hdiff, hw]
  have hyx : x - y ≠ 0 := fun h => hxy (by rw [← neg_sub x y, h, neg_zero])
  have hchord := slabLinear_direction_chord sl hw hx hy hs
  have h0 := coordinate_lower_of_direction_close (slabLinear sl) (abs_slabLinear_le sl)
    hchord (norm_direction_sub_le_of_angle_le (hdir x p hxp) hxy (by norm_num) hforward)
  rw [slabLinear_sub, coord_face₀ sl hx, sub_zero, ← dist_eq_norm'] at h0
  have hchord' : 1 / 3 ≤ (-slabLinear sl) (direction (x - y)) := by
    rw [← neg_sub y x, direction_neg, LinearMap.neg_apply, map_neg, neg_neg]
    exact hchord
  have h1 := coordinate_lower_of_direction_close (-slabLinear sl)
    (fun v => by simpa only [LinearMap.neg_apply, abs_neg] using abs_slabLinear_le sl v)
    hchord' (norm_direction_sub_le_of_angle_le (hdir y p hyp) hyx (by norm_num) hbackward)
  rw [LinearMap.neg_apply, slabLinear_sub, coord_face₁ sl hy, ← dist_eq_norm'] at h1
  have hcoord0 : 2 ≤ slabCoord sl p := by linarith only [h0, hxp]
  have hcoord1 : 2 ≤ sl.width - slabCoord sl p := by linarith only [h1, hyp]
  refine ⟨(mem_slab_set_iff sl).mpr ⟨by linarith only [hcoord0], by linarith only [hcoord1]⟩, ?_⟩
  exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_infDist_faces sl hcoord0 hcoord1)

/-- **A vector at angle at most `1/5` from `e₁` has slope at most `1/4`** (proof of
equation `eq:columns`, "since `tan(1/5) < 1/4`"). -/
theorem tr_le_lon_of_angle_le {v : Pt m} (hv : v ≠ 0) (h : angle v (e₁ : Pt m) ≤ 1 / 5) :
    ‖Pt.tr v‖ ≤ Pt.lon v / 4 := by
  have he₁ : (e₁ : Pt m) ≠ 0 := by
    intro h0
    have hnorm := Paper.norm_e₁ (m := m)
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hdire : direction (e₁ : Pt m) = e₁ := by
    simpa only [one_smul] using direction_smul_e₁ (m := m) (ℓ := 1) one_pos
  have hclose := norm_direction_sub_le_of_angle_le hv he₁ (by norm_num) h
  rw [hdire] at hclose
  have hlon := lon_lower_of_direction_close hclose
  have htr := tr_upper_of_direction_close hclose
  linarith only [hlon, htr]

end IsotropicVariance.Paper.Proofs.SlabComparison
