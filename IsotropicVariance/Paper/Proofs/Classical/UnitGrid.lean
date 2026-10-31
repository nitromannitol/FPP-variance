/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoise.Coordinates
import Mathlib.MeasureTheory.Function.Floor

/-! # Unit grid for the classical replacement argument

The orthonormal coordinates are the volume-preserving coordinates
`Infra.WhiteNoise.coordEquiv`. The half-open cells partition the space;
closed enlarged cells will carry the changes caused by regional refreshes.
-/

@[expose] public section
open MeasureTheory Set Metric
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.WhiteNoise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The integer cell containing a point, in orthonormal coordinates. -/
noncomputable def gridIndex (x : E) : Coord E → ℤ := fun i => ⌊coord x i⌋

/-- Half-open unit cells, including their lower faces. -/
def gridCell (z : Coord E → ℤ) : Set E := {x | gridIndex x = z}

/-- Closed cells enlarged by two coordinate units in either direction. -/
def gridNeighborhood (z : Coord E → ℤ) : Set E :=
  {x | ∀ i, (z i : ℝ) - 2 ≤ coord x i ∧ coord x i ≤ (z i : ℝ) + 3}

variable [MeasurableSpace E] [BorelSpace E]

/-- The grid coordinates form a measurable random variable. -/
theorem measurable_gridIndex : Measurable (gridIndex : E → Coord E → ℤ) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply i).comp measurable_coord).floor

/-- Each regional cell is Borel. -/
theorem measurableSet_gridCell (z : Coord E → ℤ) : MeasurableSet (gridCell z) :=
  measurable_gridIndex (measurableSet_singleton z)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Every point belongs to its unique grid cell. -/
theorem mem_gridCell (x : E) : x ∈ gridCell (gridIndex x) := rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- Distinct grid cells are disjoint, including on their boundaries. -/
theorem pairwiseDisjoint_gridCell : Pairwise (fun z w : Coord E → ℤ => Disjoint (gridCell z) (gridCell w)) := by
  intro z w hzw
  apply disjoint_left.mpr
  intro x hx hw
  exact hzw (hx.symm.trans hw)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Coordinate inequalities for a point in a grid cell. -/
theorem coord_bounds_of_mem_gridCell {z : Coord E → ℤ} {x : E}
    (hx : x ∈ gridCell z) (i : Coord E) :
    (z i : ℝ) ≤ coord x i ∧ coord x i < (z i : ℝ) + 1 := by
  have hi : ⌊coord x i⌋ = z i := congrFun hx i
  constructor
  · rw [← hi]; exact Int.floor_le _
  · rw [← hi]; exact Int.lt_floor_add_one _

omit [MeasurableSpace E] [BorelSpace E] in
/-- The enlarged neighborhood is closed. -/
theorem isClosed_gridNeighborhood (z : Coord E → ℤ) : IsClosed (gridNeighborhood z) := by
  have hEq : gridNeighborhood z = ⋂ i, {x : E | (z i : ℝ) - 2 ≤ coord x i ∧ coord x i ≤ (z i : ℝ) + 3} := by
    ext x
    simp only [gridNeighborhood, mem_ofPred_eq, mem_iInter]
  rw [hEq]
  apply isClosed_iInter
  intro i
  exact (isClosed_le continuous_const (contDiff_coord (n := 0) i).continuous).inter
    (isClosed_le (contDiff_coord (n := 0) i).continuous continuous_const)

end IsotropicVariance.Paper.Proofs.Classical
