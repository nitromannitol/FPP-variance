/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.UnitGrid
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Int.Interval

/-! # Only finitely many enlarged grid cells meet a bounded set

The coordinate-box argument follows the finite-support estimate in
`IsotropicVariance.Infra.WhiteNoise.Partition`, applied here to enlarged regional cells.
-/

@[expose] public section
open Set Metric
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.WhiteNoise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Enlarged grid neighborhoods meeting a bounded set form a finite family. -/
theorem finite_gridNeighborhood_meets {K : Set E} (hK : Bornology.IsBounded K) :
    {z : Coord E → ℤ | ∃ x ∈ K, x ∈ gridNeighborhood z}.Finite := by
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hK
  refine (Set.Finite.pi (t := fun _ : Coord E => Set.Icc (-⌈R + 4⌉) ⌈R + 4⌉)
    fun _ => Set.finite_Icc _ _).subset ?_
  rintro z ⟨x, hxK, hx⟩ i -
  obtain ⟨h1, h2⟩ := hx i
  have hc := abs_le.mp ((abs_coord_le x i).trans (hR x hxK))
  have hceil := Int.le_ceil (R + 4)
  constructor
  · have hh : (-(⌈R + 4⌉ : ℤ) : ℝ) ≤ z i := by
      linarith only [hceil, hc.1, h2]
    exact_mod_cast hh
  · have hh : (z i : ℝ) ≤ (⌈R + 4⌉ : ℤ) := by
      linarith only [hceil, hc.2, h1]
    exact_mod_cast hh

end IsotropicVariance.Paper.Proofs.Classical
