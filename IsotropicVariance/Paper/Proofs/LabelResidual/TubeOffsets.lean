/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.OffsetAverage
public import IsotropicVariance.Paper.Proofs.Responses.TubeGeometry
import IsotropicVariance.Paper.Proofs.Profiles.GridGeometry
import Mathlib.Tactic.Linarith

/-!
# Offset counts for the tube of an index pair

A coordinate-box argument, with integer points and `zNorm`, shows that for the good-tube
comparison the fraction of offsets where the tube is not in one core is at most
`m (|k-j| + 2ρ + 2√L + 2)/L`.
-/

@[expose] public section

open Set Metric
open scoped ENNReal

open IsotropicVariance.Paper.Proofs.Responses (transverseIntegerPoint)
namespace IsotropicVariance.Paper.Proofs.LabelResidual

open Responses

variable {m : ℕ}

/-- The closed `ρ` neighbourhood, in cell units, of the segment between two indices. -/
def indexTube (j k : Fin m → ℤ) (ρ : ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {y | infDist y (segment ℝ (transverseIntegerPoint j) (transverseIntegerPoint k)) ≤ ρ}

/-- A point of the closed tube is within `ρ` of a point of the compact index segment. -/
theorem mem_indexTube_iff (j k : Fin m → ℤ) (ρ : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    y ∈ indexTube j k ρ ↔
      ∃ p ∈ segment ℝ (transverseIntegerPoint j) (transverseIntegerPoint k), dist y p ≤ ρ := by
  have hc : IsCompact (segment ℝ (transverseIntegerPoint j) (transverseIntegerPoint k)) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨p, hp, hdist⟩ := hc.exists_infDist_eq_dist
    ⟨transverseIntegerPoint j, left_mem_segment ℝ _ _⟩ y
  constructor
  · intro h
    exact ⟨p, hp, hdist ▸ h⟩
  · rintro ⟨q, hq, hd⟩
    exact (infDist_le_dist_of_mem hq).trans hd

/-- The index tube lies in a box of common side length `|k-j| + 2ρ`. -/
theorem indexTube_subset_box (j k : Fin m → ℤ) (ρ : ℝ) :
    ∀ y ∈ indexTube j k ρ, ∀ c, ((min (j c) (k c) : ℤ) : ℝ) - ρ ≤ y c ∧
      y c ≤ (((min (j c) (k c) : ℤ) : ℝ) - ρ) + (zNorm (k-j) + 2 * ρ) := by
  intro y hy c
  obtain ⟨p, ⟨a, b, ha, hb, hab, rfl⟩, hd⟩ := (mem_indexTube_iff j k ρ y).1 hy
  have hyc : |y c - (a • transverseIntegerPoint j + b • transverseIntegerPoint k) c| ≤ ρ := by
    have := PiLp.norm_apply_le (y - (a • transverseIntegerPoint j + b • transverseIntegerPoint k)) c
    rw [← dist_eq_norm] at this
    simpa [Real.norm_eq_abs] using this.trans hd
  rw [abs_le] at hyc
  have hpc : (a • transverseIntegerPoint j + b • transverseIntegerPoint k) c =
      a * (j c : ℝ) + b * (k c : ℝ) := by simp [transverseIntegerPoint]
  rw [hpc] at hyc
  have hkj : |((k c : ℝ) - (j c : ℝ))| ≤ zNorm (k-j) := by
    have := PiLp.norm_apply_le (transverseIntegerPoint (k-j)) c
    rw [norm_transverseIntegerPoint] at this
    simpa [transverseIntegerPoint, Real.norm_eq_abs] using this
  rw [abs_le] at hkj
  have hmin : ((min (j c) (k c) : ℤ) : ℝ) ≤ j c ∧ ((min (j c) (k c) : ℤ) : ℝ) ≤ k c := by
    constructor <;> exact_mod_cast min_le_iff.2 (by simp)
  have hmin' : ((min (j c) (k c) : ℤ) : ℝ) = j c ∨
      ((min (j c) (k c) : ℤ) : ℝ) = k c := by
    rcases min_choice (j c) (k c) with h | h <;> rw [h] <;> simp
  obtain rfl : b = 1-a := by linarith
  have hb' : 0 ≤ 1-a := hb
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hmin.1 ha, mul_le_mul_of_nonneg_left hmin.2 hb', hyc.1]
  · rcases hmin' with h | h
    · rw [h]; rw [h] at hmin
      nlinarith [mul_nonneg ha (sub_nonneg.2 hmin.2), hyc.2, hkj.2]
    · rw [h]; rw [h] at hmin
      nlinarith [mul_nonneg hb' (sub_nonneg.2 hmin.1), hyc.2, hkj.1]

/-- Explicit bad-offset bound for a tube around a pair of indices. -/
theorem average_bad_indexTube_le (L : ℕ+) (j k : Fin m → ℤ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((OffsetGeometry.badOffsets L (Real.sqrt (L : ℕ)) (indexTube j k ρ)).card : ℝ≥0∞) /
      (Fintype.card (Fin m → Fin (L : ℕ)) : ℝ≥0∞) ≤
      ENNReal.ofReal ((m : ℝ) *
        (zNorm (k-j) + 2*ρ + 2*Real.sqrt (L : ℕ) + 2) / (L : ℝ)) := by
  exact average_badOffsets_le L (Real.sqrt_nonneg _)
    (add_nonneg (Profiles.zNorm_nonneg _) (mul_nonneg (by norm_num) hρ))
    (fun c => ((min (j c) (k c) : ℤ) : ℝ)-ρ) (indexTube j k ρ)
    (indexTube_subset_box j k ρ)

end IsotropicVariance.Paper.Proofs.LabelResidual
