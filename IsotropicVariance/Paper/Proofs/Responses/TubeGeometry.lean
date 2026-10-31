/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.GaussianSegment
public import IsotropicVariance.Paper.Proofs.Responses.Cells
public import IsotropicVariance.Paper.Proofs.Localization.Frame
import IsotropicVariance.Paper.Proofs.Profiles.CubeGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-!
# The transverse cell of a point near an old curve

The tube reduction in the proof of Lemma `lem:blocks`. Projection to transverse
coordinates contracts distances; normalizing by the cell width and rounding costs `√m`,
and replacing the endpoint cubes by their integer indices costs another `√m`.
-/

@[expose] public section

open Set Metric

namespace IsotropicVariance.Paper.Proofs.Responses

variable {m : ℕ}

/-- The transverse coordinates measured in units of the cell width. -/
noncomputable def normalizedTransverse (W : ℝ) (x : Pt m) : EuclideanSpace ℝ (Fin m) :=
  W⁻¹ • Pt.tr x

lemma normalizedTransverse_dist_le {W : ℝ} (hW : 0 < W) (x y : Pt m) :
    dist (normalizedTransverse W x) (normalizedTransverse W y) ≤ W⁻¹ * dist x y := by
  rw [normalizedTransverse, normalizedTransverse, dist_eq_norm, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hW.le)]
  exact mul_le_mul_of_nonneg_left (Localization.Pt.norm_tr_sub_le_dist x y) (inv_nonneg.mpr hW.le)

lemma normalizedTransverse_gridCube_dist_le {W s : ℝ} (hW : 0 < W)
    {i : ℕ} {j : Fin m → ℤ} {u : Pt m} (hu : u ∈ gridCube s W 0 i j) :
    dist (normalizedTransverse W u) (transverseIntegerPoint j) ≤ Real.sqrt m := by
  rw [dist_eq_norm]
  convert Profiles.norm_le_of_abs_le (y := normalizedTransverse W u - transverseIntegerPoint j)
    zero_le_one (fun k => ?_) using 1 <;> try rw [mul_one]
  change |W⁻¹ * Pt.tr u k - (j k : ℝ)| ≤ 1
  have h := hu.2 k
  simp only [sub_zero] at h
  have hlo : (j k : ℝ) ≤ Pt.tr u k / W :=
    (le_div_iff₀ hW).mpr (by simpa only [mul_comm] using h.1)
  have hhi : Pt.tr u k / W ≤ (j k : ℝ) + 1 :=
    (div_le_iff₀ hW).mpr (by simpa only [mul_comm] using h.2)
  rw [div_eq_inv_mul] at hlo hhi
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi]

/-- Normalized transverse points of a chord between the endpoint cubes lie within `√m` of
the chord between the integer indices. -/
lemma normalizedTransverse_segment_close {W s : ℝ} (hW : 0 < W) {i : ℕ}
    {j k : Fin m → ℤ} {u v y : Pt m} (hu : u ∈ gridCube s W 0 i j)
    (hv : v ∈ gridCube s W 0 (i + 1) k) (hy : y ∈ segment ℝ u v) :
    ∃ q ∈ segment ℝ (transverseIntegerPoint j) (transverseIntegerPoint k),
      dist (normalizedTransverse W y) q ≤ Real.sqrt m := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  refine ⟨a • transverseIntegerPoint j + b • transverseIntegerPoint k,
    ⟨a, b, ha, hb, hab, rfl⟩, ?_⟩
  have heq : normalizedTransverse W (a • u + b • v) -
      (a • transverseIntegerPoint j + b • transverseIntegerPoint k) =
      a • (normalizedTransverse W u - transverseIntegerPoint j) +
      b • (normalizedTransverse W v - transverseIntegerPoint k) := by
    ext l
    simp [normalizedTransverse, Pt.tr]
    ring
  rw [dist_eq_norm, heq]
  have hu' := normalizedTransverse_gridCube_dist_le hW hu
  have hv' := normalizedTransverse_gridCube_dist_le hW hv
  rw [dist_eq_norm] at hu' hv'
  calc
    _ ≤ ‖a • (normalizedTransverse W u - transverseIntegerPoint j)‖ +
        ‖b • (normalizedTransverse W v - transverseIntegerPoint k)‖ := norm_add_le _ _
    _ = a * ‖normalizedTransverse W u - transverseIntegerPoint j‖ +
        b * ‖normalizedTransverse W v - transverseIntegerPoint k‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * Real.sqrt m + b * Real.sqrt m :=
      add_le_add (mul_le_mul_of_nonneg_left hu' ha) (mul_le_mul_of_nonneg_left hv' hb)
    _ = _ := by rw [← add_mul, hab, one_mul]

/-- A fine cell within distance two of a curve point belongs to the enlarged transverse tube.
The factor two accommodates nonattainment of distance to a half-open block. -/
theorem infDist_floor_near_segment_le {W s D : ℝ} (hW : 1 ≤ W) {i : ℕ}
    {j k : Fin m → ℤ} {u v x y : Pt m} (hu : u ∈ gridCube s W 0 i j)
    (hv : v ∈ gridCube s W 0 (i + 1) k) (hxy : dist y x ≤ 2)
    (hx : infDist x (segment ℝ u v) ≤ D) :
    infDist (transverseIntegerPoint fun l => ⌊Pt.tr y l / W⌋)
      (segment ℝ (transverseIntegerPoint j) (transverseIntegerPoint k)) ≤
        2 * Real.sqrt m + 2 + W⁻¹ * D := by
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hcompact : IsCompact (segment ℝ u v) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨p, hp, hdist⟩ := hcompact.exists_infDist_eq_dist
    ⟨u, left_mem_segment ℝ u v⟩ x
  obtain ⟨q, hq, hpq⟩ := normalizedTransverse_segment_close hW0 hu hv hp
  have hfloor : dist (transverseIntegerPoint fun l => ⌊Pt.tr y l / W⌋)
      (normalizedTransverse W y) ≤ Real.sqrt m := by
    simpa only [normalizedTransverse, PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul] using
      dist_floor_point_le (normalizedTransverse W y)
  have hyx : dist (normalizedTransverse W y) (normalizedTransverse W x) ≤ 2 := by
    refine (normalizedTransverse_dist_le hW0 y x).trans ?_
    have hWi : W⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW
    exact (mul_le_mul_of_nonneg_left hxy (inv_nonneg.mpr hW0.le)).trans
      (by nlinarith only [hWi])
  have hxp : dist (normalizedTransverse W x) (normalizedTransverse W p) ≤ W⁻¹ * D :=
    (normalizedTransverse_dist_le hW0 x p).trans
      (mul_le_mul_of_nonneg_left (hdist ▸ hx) (inv_nonneg.mpr hW0.le))
  refine (infDist_le_dist_of_mem hq).trans ?_
  calc
    _ ≤ dist (transverseIntegerPoint fun l => ⌊Pt.tr y l / W⌋) (normalizedTransverse W y) +
        dist (normalizedTransverse W y) q := dist_triangle _ _ _
    _ ≤ Real.sqrt m + (dist (normalizedTransverse W y) (normalizedTransverse W x) +
        dist (normalizedTransverse W x) q) := add_le_add hfloor (dist_triangle _ _ _)
    _ ≤ Real.sqrt m + (2 + (dist (normalizedTransverse W x) (normalizedTransverse W p) +
        dist (normalizedTransverse W p) q)) :=
      add_le_add_right (add_le_add hyx (dist_triangle _ _ _)) _
    _ ≤ Real.sqrt m + (2 + (W⁻¹ * D + Real.sqrt m)) := by gcongr
    _ = _ := by ring

end IsotropicVariance.Paper.Proofs.Responses
