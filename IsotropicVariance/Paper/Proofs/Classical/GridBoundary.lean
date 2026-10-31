/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.UnitGrid

/-! # Null boundaries for the half-open regional grid -/

@[expose] public section
open MeasureTheory Set Metric
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.WhiteNoise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every orthonormal coordinate hyperplane has zero volume. -/
theorem volume_gridCoord_eq (i : Coord E) (r : ℝ) :
    volume {x : E | coord x i = r} = 0 := by
  have h := (measurePreserving_coordEquiv (E := E)).quasiMeasurePreserving.preimage_null
    (Measure.pi_hyperplane (fun _ : Coord E => (volume : Measure ℝ)) i r)
  have hs : (coordEquiv E) ⁻¹' {f : Coord E → ℝ | f i = r} =
      {x : E | coord x i = r} := by
    ext x
    rfl
  rw [hs] at h
  exact h

/-- The half-open grid cells have null boundaries, as required for regional
independence in the noise model. -/
theorem volume_frontier_gridCell (z : Coord E → ℤ) :
    volume (frontier (gridCell z)) = 0 := by
  let K : Set E := {x | ∀ i, (z i : ℝ) ≤ coord x i ∧ coord x i ≤ (z i : ℝ) + 1}
  let V : Set E := {x | ∀ i, (z i : ℝ) < coord x i ∧ coord x i < (z i : ℝ) + 1}
  have hK : IsClosed K := by
    have heq : K = ⋂ i, {x : E | (z i : ℝ) ≤ coord x i ∧ coord x i ≤ (z i : ℝ) + 1} := by
      ext x; simp only [K, mem_ofPred_eq, mem_iInter]
    rw [heq]
    exact isClosed_iInter fun i =>
      (isClosed_le continuous_const (contDiff_coord (n := 0) i).continuous).inter
        (isClosed_le (contDiff_coord (n := 0) i).continuous continuous_const)
  have hV : IsOpen V := by
    have heq : V = ⋂ i, {x : E | (z i : ℝ) < coord x i ∧ coord x i < (z i : ℝ) + 1} := by
      ext x; simp only [V, mem_ofPred_eq, mem_iInter]
    rw [heq]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (contDiff_coord (n := 0) i).continuous).inter
        (isOpen_lt (contDiff_coord (n := 0) i).continuous continuous_const)
  have hCK : gridCell z ⊆ K := fun x hx i =>
    ⟨(coord_bounds_of_mem_gridCell hx i).1, (coord_bounds_of_mem_gridCell hx i).2.le⟩
  have hVC : V ⊆ gridCell z := by
    intro x hx
    apply funext
    intro i
    exact Int.floor_eq_iff.mpr ⟨(hx i).1.le, (hx i).2⟩
  have hSub : frontier (gridCell z) ⊆
      ⋃ i : Coord E, ({x : E | coord x i = (z i : ℝ)} ∪
        {x : E | coord x i = (z i : ℝ) + 1}) := by
    intro x hx
    have hxK : x ∈ K := (closure_minimal hCK hK) hx.1
    by_contra h
    have hn : ∀ i, coord x i ≠ (z i : ℝ) ∧ coord x i ≠ (z i : ℝ) + 1 := by
      intro i
      constructor
      · intro hi; exact h (mem_iUnion.mpr ⟨i, Or.inl hi⟩)
      · intro hi; exact h (mem_iUnion.mpr ⟨i, Or.inr hi⟩)
    have hxV : x ∈ V := fun i =>
      ⟨lt_of_le_of_ne (hxK i).1 (hn i).1.symm, lt_of_le_of_ne (hxK i).2 (hn i).2⟩
    exact hx.2 ((interior_maximal hVC hV) hxV)
  apply measure_mono_null hSub
  apply measure_iUnion_null
  intro i
  exact measure_union_null (volume_gridCoord_eq i _) (volume_gridCoord_eq i _)

end IsotropicVariance.Paper.Proofs.Classical
