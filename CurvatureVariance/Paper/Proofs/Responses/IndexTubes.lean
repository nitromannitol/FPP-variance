/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Space.TransversePoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Group.Int
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Window segments and transverse chord distances

These deterministic estimates use Euclidean product and transverse norms.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Responses.Geometry

/-- Integer cube indices embedded in Euclidean transverse space. -/
def indexPoint {m : ℕ} (j : Fin m → ℤ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => (j i : ℝ))

/-- The closed index tube defined by Euclidean distance from the index segment. -/
def indexTube {m : ℕ} (j k : Fin m → ℤ) (R : ℝ) : Set (Fin m → ℤ) :=
  {l | Metric.infDist (indexPoint l) (segment ℝ (indexPoint j) (indexPoint k)) ≤ R}

/-- Distance to the compact index segment is attained. -/
theorem mem_indexTube_iff {m : ℕ} (j k l : Fin m → ℤ) (R : ℝ) :
    l ∈ indexTube j k R ↔ ∃ p ∈ segment ℝ (indexPoint j) (indexPoint k), dist (indexPoint l) p ≤ R := by
  have hc : IsCompact (segment ℝ (indexPoint j) (indexPoint k)) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨p, hp, hdist⟩ := hc.exists_infDist_eq_dist ⟨indexPoint j, left_mem_segment ℝ _ _⟩ (indexPoint l)
  constructor
  · intro h
    exact ⟨p, hp, hdist ▸ h⟩
  · rintro ⟨q, hq, hd⟩
    exact (Metric.infDist_le_dist_of_mem hq).trans hd

/-- The supremum norm on integer indices is bounded by the Euclidean norm
of their embedding. -/
theorem norm_index_le {m : ℕ} (j : Fin m → ℤ) : ‖j‖ ≤ ‖indexPoint j‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  rw [← Int.norm_cast_real]
  exact PiLp.norm_apply_le (indexPoint j) i

/-- Every finite-radius Euclidean index tube is finite. -/
theorem indexTube_finite {m : ℕ} (j k : Fin m → ℤ) (R : ℝ) : (indexTube j k R).Finite := by
  let B : ℝ := max ‖indexPoint j‖ ‖indexPoint k‖
  apply (isCompact_closedBall (0 : Fin m → ℤ) (R + B)).finite_of_discrete.subset
  intro l hl
  obtain ⟨p, hp, hdist⟩ := (mem_indexTube_iff j k l R).mp hl
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
  have hnorm : ‖a • indexPoint j + b • indexPoint k‖ ≤ B := by
    calc
      _ ≤ ‖a • indexPoint j‖ + ‖b • indexPoint k‖ := norm_add_le _ _
      _ = a * ‖indexPoint j‖ + b * ‖indexPoint k‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * B + b * B := add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
      _ = B := by rw [← add_mul, hab, one_mul]
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_index_le l).trans ((norm_le_norm_sub_add (indexPoint l)
    (a • indexPoint j + b • indexPoint k)).trans (add_le_add hdist hnorm))

end CurvatureVariance.Paper.Responses.Geometry
