/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Poisson.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# The unit-cube partition of Euclidean space

Half-open cubes indexed by integer vectors, with their uniform probability measures.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace IsotropicVariance.Infra.Poisson

/-- The integer index of the half-open cube containing a point. -/
noncomputable def cubeIndex {d : ℕ} (x : E d) : Fin d → ℤ := fun i => ⌊x i⌋

/-- Unit cube with lower corner `z`. -/
def cube {d : ℕ} (z : Fin d → ℤ) : Set (E d) := {x | cubeIndex x = z}

/-- Cube indices are measurable. -/
theorem measurable_cubeIndex {d : ℕ} : Measurable (cubeIndex : E d → Fin d → ℤ) :=
  Measurable.of_eval fun i => Int.measurable_floor.comp (by fun_prop)

/-- Half-open cubes are Borel. -/
theorem measurableSet_cube {d : ℕ} (z : Fin d → ℤ) : MeasurableSet (cube z) :=
  measurable_cubeIndex (measurableSet_singleton z)

/-- A coordinate description convenient for product Lebesgue measure. -/
theorem cube_eq_preimage_pi {d : ℕ} (z : Fin d → ℤ) :
    cube z = WithLp.ofLp ⁻¹' Set.pi Set.univ
      (fun i => Set.Ico (z i : ℝ) ((z i : ℝ) + 1)) := by
  ext x
  simp only [cube, Set.mem_ofPred_eq, funext_iff, cubeIndex, Int.floor_eq_iff,
    Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico]

/-- Every half-open unit cube has volume one, including in dimension zero. -/
theorem volume_cube {d : ℕ} (z : Fin d → ℤ) : volume (cube z) = 1 := by
  rw [cube_eq_preimage_pi,
    (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
      ((measurableSet_pi Set.countable_univ).mpr (Or.inl (fun _ _ => measurableSet_Ico))).nullMeasurableSet,
    volume_pi_pi]
  simp [Real.volume_Ico]

/-- Distinct cubes are disjoint. -/
theorem pairwiseDisjoint_cube {d : ℕ} :
    Pairwise (fun z w : Fin d → ℤ => Disjoint (cube z) (cube w)) := by
  intro z w hzw
  exact Set.disjoint_left.mpr fun x hx hy => hzw (hx.symm.trans hy)

/-- A bounded set meets only finitely many cubes. -/
theorem finite_cubeIndex_image {d : ℕ} {B : Set (E d)} (hB : Bornology.IsBounded B) :
    (cubeIndex '' B).Finite := by
  obtain ⟨R, hR⟩ := hB.exists_norm_le
  apply (Set.Finite.pi (fun _ : Fin d => Set.finite_Icc ⌊-R⌋ ⌊R⌋)).subset
  rintro z ⟨x, hx, rfl⟩
  intro i _
  have hc : |x i| ≤ R := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans (hR x hx)
  exact ⟨Int.floor_mono (abs_le.mp hc).1, Int.floor_mono (abs_le.mp hc).2⟩

/-- The uniform probability measure on a cube, carried by the cube subtype. -/
noncomputable def cubeUniform {d : ℕ} (z : Fin d → ℤ) : Measure (cube z) :=
  volume.comap Subtype.val

instance cubeUniform.isProbabilityMeasure {d : ℕ} (z : Fin d → ℤ) :
    IsProbabilityMeasure (cubeUniform z) := by
  constructor
  rw [cubeUniform, comap_subtype_coe_apply (measurableSet_cube z),
    Set.image_univ, Subtype.range_coe, volume_cube]

/-- Mapping the cube's uniform measure into space gives restricted Lebesgue measure. -/
theorem map_cubeUniform {d : ℕ} (z : Fin d → ℤ) :
    (cubeUniform z).map Subtype.val = volume.restrict (cube z) :=
  map_comap_subtype_coe (measurableSet_cube z) volume

end IsotropicVariance.Infra.Poisson
