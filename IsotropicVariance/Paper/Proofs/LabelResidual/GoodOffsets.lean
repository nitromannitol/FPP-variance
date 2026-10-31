/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.CoreGeometry
public import IsotropicVariance.Paper.Proofs.Responses.TubeGeometry
public import IsotropicVariance.Paper.Proofs.Responses.Cells

/-!
# Good offsets contain endpoint cubes and contributing cells in one core

A tube in dimensionless transverse coordinates contained in a counted offset core contains
the two actual endpoint cubes in the corresponding `coreFace`s. Every contributing integer
cell in that tube belongs to the same block. These are the deterministic geometric uses of
the offset count in the proof of Lemma `lem:residual`.
-/

@[expose] public section

open Set Metric

namespace IsotropicVariance.Paper.Proofs.LabelResidual

variable {m : ℕ}

/-- An integer cell in the counted core belongs to that core's block. -/
theorem cellBlockIndex_eq_of_mem_groupCore (L : ℕ+) (o : Fin m → Fin (L : ℕ))
    (g z : Fin m → ℤ)
    (h : Responses.transverseIntegerPoint z ∈ OffsetGeometry.groupCore L (Real.sqrt (L : ℕ)) o g) :
    Responses.cellBlockIndex L o z = blockLowerIndex L o g := by
  apply Responses.cellBlockIndex_eq L.pos o (isBlockIndex_blockLowerIndex L o g)
  intro k
  have hk := h k
  change (o k : ℝ) + (L : ℝ) * (g k : ℝ) + Real.sqrt (L : ℕ) ≤ (z k : ℝ) ∧
    (z k : ℝ) < (o k : ℝ) + (L : ℝ) * (g k : ℝ) + (L : ℝ) - Real.sqrt (L : ℕ) at hk
  have hz : (blockLowerIndex L o g k : ℝ) = (o k : ℝ) + (L : ℝ) * (g k : ℝ) := by
    simp only [blockLowerIndex, Int.cast_add, Int.cast_natCast, Int.cast_mul]
  constructor
  · exact_mod_cast (show (blockLowerIndex L o g k : ℝ) ≤ (z k : ℝ) by
      rw [hz]; linarith only [hk.1, Real.sqrt_nonneg (L : ℕ)])
  · exact_mod_cast (show (z k : ℝ) < (blockLowerIndex L o g k + L : ℤ) by
      push_cast; rw [hz]; linarith only [hk.2, Real.sqrt_nonneg (L : ℕ)])

/-- A normalized grid cube is in the same core as a tube of radius at least `√m` about
any segment containing its integer corner. -/
theorem gridCube_subset_coreFace_of_tube_subset (L : ℕ+) (o : Fin m → Fin (L : ℕ))
    (g j : Fin m → ℤ) {n W ρ : ℝ} (hW : 0 < W) (i : ℕ)
    (S : Set (EuclideanSpace ℝ (Fin m))) (hj : Responses.transverseIntegerPoint j ∈ S)
    (hρ : Real.sqrt m ≤ ρ)
    (hcore : {y : EuclideanSpace ℝ (Fin m) | infDist y S ≤ ρ} ⊆
      OffsetGeometry.groupCore L (Real.sqrt (L : ℕ)) o g) :
    gridCube n W 0 i j ⊆ coreFace n W L i (blockLowerIndex L o g) := by
  intro x hx
  apply mem_coreFace_of_mem_groupCore L o g hW i
  · simpa only [Pt.lon_zero, zero_add, sub_zero] using hx.1
  · have hdist := Responses.normalizedTransverse_gridCube_dist_le hW hx
    have hinf : infDist (Responses.normalizedTransverse W x) S ≤ ρ :=
      ((infDist_le_dist_of_mem hj).trans hdist).trans hρ
    convert hcore hinf using 1
    ext k
    simp only [Responses.normalizedTransverse, PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]

end IsotropicVariance.Paper.Proofs.LabelResidual
