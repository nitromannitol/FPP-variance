/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Minimum
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Points near a segment (the proof of Lemma `lem:modulus`)

`exists_ray_near`: a point within `λ` of the segment `[u, v]` is, seen from each endpoint, within
`λ` of a nonnegative multiple of the direction of the segment. With it, `norm_normalize_sub_le` and
`isCompact_segment'`.
-/

@[expose] public section

open Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Modulus

variable {m : ℕ}

/-- The direction of a vector close to a ray: if `|w − μe| ≤ λ` with `‖e‖ = 1`, `μ ≥ 0`, then
`|w/|w| − e| ≤ 2λ/|w|`. -/
lemma norm_normalize_sub_le {w e : Pt m} (hw : w ≠ 0) (he : ‖e‖ = 1) {μ lam : ℝ} (hμ : 0 ≤ μ)
    (h : ‖w - μ • e‖ ≤ lam) : ‖‖w‖⁻¹ • w - e‖ ≤ 2 * lam / ‖w‖ := by
  have hA : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have h1 : ‖‖w‖⁻¹ • w - e‖ ≤ ‖‖w‖⁻¹ • (w - μ • e)‖ + |μ / ‖w‖ - 1| := by
    have : ‖w‖⁻¹ • w - e = ‖w‖⁻¹ • (w - μ • e) + (μ / ‖w‖ - 1) • e := by
      rw [smul_sub, smul_smul, sub_smul, one_smul, div_eq_inv_mul]
      abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul (μ / ‖w‖ - 1), he, mul_one, Real.norm_eq_abs]
  have h2 : ‖‖w‖⁻¹ • (w - μ • e)‖ ≤ lam / ‖w‖ := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right h hA.le
  have h3 : |μ / ‖w‖ - 1| ≤ lam / ‖w‖ := by
    rw [show μ / ‖w‖ - 1 = (μ - ‖w‖) / ‖w‖ by field_simp, abs_div, abs_of_pos hA]
    refine div_le_div_of_nonneg_right ?_ hA.le
    have := abs_norm_sub_norm_le (μ • e) w
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hμ, norm_sub_rev] at this
    linarith
  have h4 : 2 * lam / ‖w‖ = lam / ‖w‖ + lam / ‖w‖ := by ring
  linarith

lemma isCompact_segment' (u v : Pt m) : IsCompact (segment ℝ u v) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

/-- A point within `λ` of the segment `[u, v]`: `x − u` is within `λ` of a nonnegative
multiple of `(v − u)/|v − u|`, and `v − x` too. -/
lemma exists_ray_near {u v x : Pt m} (huv : u ≠ v) {lam : ℝ}
    (hx : infDist x (segment ℝ u v) ≤ lam) :
    ∃ μ μ' : ℝ, 0 ≤ μ ∧ 0 ≤ μ' ∧
      ‖(x - u) - μ • (‖v - u‖⁻¹ • (v - u))‖ ≤ lam ∧
      ‖(v - x) - μ' • (‖v - u‖⁻¹ • (v - u))‖ ≤ lam := by
  obtain ⟨s, hs, hd⟩ := (isCompact_segment' u v).exists_infDist_eq_dist
    ⟨u, left_mem_segment ℝ u v⟩ x
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hs
  have hn : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huv))
  have hsu : a • u + b • v - u = (b * ‖v - u‖) • (‖v - u‖⁻¹ • (v - u)) := by
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hn.ne', mul_one, smul_sub,
      show a = 1 - b by linarith, sub_smul, one_smul]
    abel
  have hvs : v - (a • u + b • v) = (a * ‖v - u‖) • (‖v - u‖⁻¹ • (v - u)) := by
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hn.ne', mul_one, smul_sub,
      show b = 1 - a by linarith, sub_smul, one_smul]
    abel
  have hxs : dist x (a • u + b • v) ≤ lam := hd ▸ hx
  refine ⟨b * ‖v - u‖, a * ‖v - u‖, by positivity, by positivity, ?_, ?_⟩
  · rw [← hsu, show x - u - (a • u + b • v - u) = x - (a • u + b • v) by abel, ← dist_eq_norm]
    exact hxs
  · rw [← hvs, show v - x - (v - (a • u + b • v)) = a • u + b • v - x by abel, ← dist_eq_norm,
      dist_comm]
    exact hxs

end IsotropicVariance.Paper.Proofs.Modulus
