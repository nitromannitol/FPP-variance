/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Cubes
import CurvatureVariance.Paper.Proofs.Responses.RowGeometry
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes

/-!
# Geometry of sheared row cubes

The normalized shear sends each row cube within `√m` of its integer index. Its norm is at
most `(1+T)/w` when the slope has norm at most `T`. Together with the fine-index rounding error,
this transfers distance from a physical chord to distance from the corresponding index chord.
-/

@[expose] public section

open Set

namespace CurvatureVariance.Paper.Tubes

variable {m : ℕ}

/-- The transverse shear, normalized by the fine-cube width. -/
noncomputable def indexProjection (w : ℕ) (t : EuclideanSpace ℝ (Fin m)) :
    Pt m →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun x := (w : ℝ)⁻¹ • (x.ofLp.2 - x.ofLp.1 • t)
  map_add' x y := by
    ext q
    change (w : ℝ)⁻¹ * ((x.ofLp.2 q + y.ofLp.2 q) - (x.ofLp.1 + y.ofLp.1) * t q) =
      (w : ℝ)⁻¹ * (x.ofLp.2 q - x.ofLp.1 * t q) +
      (w : ℝ)⁻¹ * (y.ofLp.2 q - y.ofLp.1 * t q)
    ring
  map_smul' a x := by
    ext q
    change (w : ℝ)⁻¹ * (a * x.ofLp.2 q - (a * x.ofLp.1) * t q) =
      a * ((w : ℝ)⁻¹ * (x.ofLp.2 q - x.ofLp.1 * t q))
    ring

/-- The normalized shear has norm at most `(1+T)/w` on slopes of norm at most `T`. -/
theorem norm_indexProjection_le {w : ℕ} (hw : 1 ≤ w)
    {t : EuclideanSpace ℝ (Fin m)} {T : ℝ} (ht : ‖t‖ ≤ T) (x : Pt m) :
    ‖indexProjection w t x‖ ≤ ((1 + T) / (w : ℝ)) * ‖x‖ := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hfst : |x.ofLp.1| ≤ ‖x‖ := by
    simpa only [WithLp.fst, Real.norm_eq_abs] using WithLp.norm_fst_le (p := (2 : ENNReal)) ℝ x
  have hsnd : ‖x.ofLp.2‖ ≤ ‖x‖ := WithLp.norm_snd_le (p := (2 : ENNReal)) ℝ x
  have hshear : ‖x.ofLp.2 - x.ofLp.1 • t‖ ≤ (1 + T) * ‖x‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have hmul := mul_le_mul_of_nonneg_left ht (abs_nonneg x.ofLp.1)
    have hT : 0 ≤ T := (norm_nonneg t).trans ht
    have hf := mul_le_mul_of_nonneg_right hfst hT
    linarith only [hsnd, hmul, hf]
  change ‖(w : ℝ)⁻¹ • (x.ofLp.2 - x.ofLp.1 • t)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hw0)]
  calc
    _ ≤ (w : ℝ)⁻¹ * ((1 + T) * ‖x‖) := mul_le_mul_of_nonneg_left hshear (inv_nonneg.2 hw0.le)
    _ = _ := by ring

/-- Flooring the normalized shear moves a point by at most `√m` in index space. -/
theorem norm_fineIndex_sub_projection_le (w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (x : Pt m) :
    ‖transversePoint (fineIndex w t x) - indexProjection w t x‖ ≤ Real.sqrt m := by
  simpa only [mul_one] using Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le (m := m)
    (r := 1) zero_le_one (fun q => by
      change |(⌊(x.ofLp.2 q - x.ofLp.1 * t q) / w⌋ : ℝ) -
        (w : ℝ)⁻¹ * (x.ofLp.2 q - x.ofLp.1 * t q)| ≤ 1
      rw [inv_mul_eq_div]
      have hl := Int.floor_le ((x.ofLp.2 q - x.ofLp.1 * t q) / w)
      have hu := Int.lt_floor_add_one ((x.ofLp.2 q - x.ofLp.1 * t q) / w)
      exact abs_le.mpr ⟨by linarith only [hu], by linarith only [hl]⟩)

/-- Row rounding and integer row membership cost at most `√m` after normalization. -/
theorem norm_projection_row_sub_index_le (n : ℕ) {w : ℕ} (hw : 1 ≤ w)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (j : Fin m → ℤ)
    {u : Vertex m} (hu : u ∈ rowCube n w t i j) :
    ‖indexProjection w t (point u) - transversePoint j‖ ≤ Real.sqrt m := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have huc := hu
  rw [Responses.rowCube_eq_transverseCube n hw t i j] at huc
  simpa only [mul_one] using Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le (m := m)
    (r := 1) zero_le_one (fun q => by
      have hc0 : |(u.2 q : ℝ) - ((⌊(i : ℝ) * n * t q⌋ : ℝ) +
          (w : ℝ) * j q + ((w : ℝ) - 1) / 2)| ≤ ((w : ℝ) - 1) / 2 := huc.2 q
      have hc := abs_le.mp hc0
      have hf := Int.floor_le ((i : ℝ) * n * t q)
      have hf' := Int.lt_floor_add_one ((i : ℝ) * n * t q)
      have he : |(u.2 q : ℝ) - (i : ℝ) * n * t q - (w : ℝ) * j q| ≤ w := by
        exact abs_le.mpr ⟨by linarith only [hc.1, hf', hw1], by linarith only [hc.2, hf]⟩
      change |(w : ℝ)⁻¹ * ((u.2 q : ℝ) - (u.1 : ℝ) * t q) - (j q : ℝ)| ≤ 1
      rw [hu.1, Int.cast_mul, Int.cast_natCast]
      have hid : (w : ℝ)⁻¹ * ((u.2 q : ℝ) - (i : ℝ) * n * t q) - (j q : ℝ) =
          ((u.2 q : ℝ) - (i : ℝ) * n * t q - (w : ℝ) * j q) / w := by
        field_simp
      rw [hid, abs_div, abs_of_pos hw0]
      exact (div_le_one hw0).2 he)

/-- Distance to the physical endpoint chord controls distance to the integer index chord. -/
theorem infDist_index_le (n : ℕ) {w : ℕ} (hw : 1 ≤ w)
    {t : EuclideanSpace ℝ (Fin m)} {T : ℝ} (ht : ‖t‖ ≤ T) (i i' : ℤ) (j k : Fin m → ℤ)
    {u v : Vertex m} (hu : u ∈ rowCube n w t i j) (hv : v ∈ rowCube n w t i' k)
    (x : Pt m) :
    Metric.infDist (transversePoint (fineIndex w t x))
        (segment ℝ (transversePoint j) (transversePoint k)) ≤
      2 * Real.sqrt m + ((1 + T) / (w : ℝ)) * Metric.infDist x (segment ℝ (point u) (point v)) := by
  have hc : IsCompact (segment ℝ (point u) (point v)) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨q, hq, hdist⟩ := hc.exists_infDist_eq_dist ⟨point u, left_mem_segment ℝ _ _⟩ x
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hq
  let r := a • transversePoint j + b • transversePoint k
  have hr : r ∈ segment ℝ (transversePoint j) (transversePoint k) := ⟨a, b, ha, hb, hab, rfl⟩
  have hqr : ‖indexProjection w t q - r‖ ≤ Real.sqrt m := by
    rw [← heq, map_add, map_smul, map_smul]
    have hid : a • indexProjection w t (point u) + b • indexProjection w t (point v) - r =
        a • (indexProjection w t (point u) - transversePoint j) +
        b • (indexProjection w t (point v) - transversePoint k) := by dsimp only [r]; module
    rw [hid]
    calc
      _ ≤ ‖a • (indexProjection w t (point u) - transversePoint j)‖ +
          ‖b • (indexProjection w t (point v) - transversePoint k)‖ := norm_add_le _ _
      _ = a * ‖indexProjection w t (point u) - transversePoint j‖ +
          b * ‖indexProjection w t (point v) - transversePoint k‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * Real.sqrt m + b * Real.sqrt m := add_le_add
        (mul_le_mul_of_nonneg_left (norm_projection_row_sub_index_le n hw t i j hu) ha)
        (mul_le_mul_of_nonneg_left (norm_projection_row_sub_index_le n hw t i' k hv) hb)
      _ = _ := by rw [← add_mul, hab, one_mul]
  have hdiff : ‖indexProjection w t x - indexProjection w t q‖ ≤
      ((1 + T) / (w : ℝ)) * Metric.infDist x (segment ℝ (point u) (point v)) := by
    rw [← map_sub, hdist, dist_eq_norm]
    exact norm_indexProjection_le hw ht (x - q)
  refine (Metric.infDist_le_dist_of_mem hr).trans ?_
  rw [dist_eq_norm]
  have htri := norm_add_le (transversePoint (fineIndex w t x) - indexProjection w t x)
    (indexProjection w t x - r)
  have htri' := norm_add_le (indexProjection w t x - indexProjection w t q)
    (indexProjection w t q - r)
  rw [sub_add_sub_cancel] at htri htri'
  linarith only [htri, htri', norm_fineIndex_sub_projection_le w t x, hqr, hdiff]

end CurvatureVariance.Paper.Tubes
