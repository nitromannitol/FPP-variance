/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.Offsets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Offset cores in the coordinates of continuum blocks

The counting estimate of `Offsets` is stated in dimensionless transverse coordinates.
This module identifies its core with the actual two faces in equation `eq:labelprofile`,
`coreFace`.
-/

@[expose] public section

namespace IsotropicVariance.Paper.Proofs.LabelResidual

open Set

/-- The lower index of the block with offset `o` and integer quotient `g`. -/
def blockLowerIndex {m : ℕ} (L : ℕ+) (o : Fin m → Fin (L : ℕ))
    (g : Fin m → ℤ) : Fin m → ℤ :=
  fun k => (o k : ℕ) + (L : ℤ) * g k

/-- The block lower index belongs to the offset partition. -/
theorem isBlockIndex_blockLowerIndex {m : ℕ} (L : ℕ+) (o : Fin m → Fin (L : ℕ))
    (g : Fin m → ℤ) : IsBlockIndex L o (blockLowerIndex L o g) := by
  intro k
  change (L : ℤ) ∣ ((o k : ℕ) + (L : ℤ) * g k) - (o k : ℕ)
  rw [add_sub_cancel_left]
  exact dvd_mul_right _ _

/-- A transverse point of the counted core gives a point of the actual core face. -/
theorem mem_coreFace_of_mem_groupCore {m : ℕ} (L : ℕ+)
    (o : Fin m → Fin (L : ℕ)) (g : Fin m → ℤ) {W n : ℝ} (hW : 0 < W)
    (i : ℕ) {x : Pt m} (hx : Pt.lon x = (i : ℝ) * n)
    (hcore : WithLp.toLp 2 (fun k => Pt.tr x k / W) ∈
      OffsetGeometry.groupCore L (Real.sqrt (L : ℕ)) o g) :
    x ∈ coreFace n W L i (blockLowerIndex L o g) := by
  refine ⟨hx, fun k => ?_⟩
  have h := hcore k
  change (o k : ℝ) + (L : ℝ) * (g k : ℝ) + Real.sqrt (L : ℕ) ≤ Pt.tr x k / W ∧
    Pt.tr x k / W < (o k : ℝ) + (L : ℝ) * (g k : ℝ) + (L : ℝ) -
      Real.sqrt (L : ℕ) at h
  have hz : (blockLowerIndex L o g k : ℝ) = (o k : ℝ) + (L : ℝ) * (g k : ℝ) := by
    simp only [blockLowerIndex, Int.cast_add, Int.cast_natCast, Int.cast_mul]
  rw [hz]
  constructor
  · have hh := (le_div_iff₀ hW).mp h.1
    nlinarith only [hh]
  · have hh := (div_lt_iff₀ hW).mp h.2
    nlinarith only [hh]

end IsotropicVariance.Paper.Proofs.LabelResidual
