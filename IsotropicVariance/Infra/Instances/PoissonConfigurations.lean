/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonFiniteCloudSort
public import IsotropicVariance.Infra.Instances.PoissonCoding
public import IsotropicVariance.Infra.Poisson.Construction

/-! # Canonical locally finite counting configurations

A configuration has one canonically ordered finite cloud in each half-open integer cube.
There are countably many cubes, so this carrier is standard Borel. Its measure decoder is
injective and measurable; the carrier contains no unused infinite mark tails.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace IsotropicVariance.Infra.Instances

/-- Canonical configurations in Euclidean coordinates. -/
abbrev PoissonConfiguration (d : ℕ) := ∀ z : Fin d → ℤ, PoissonFiniteCloud (Poisson.cube z)

instance (d : ℕ) : StandardBorelSpace (PoissonConfiguration d) := inferInstance

/-- A local canonical cloud placed in physical space. -/
noncomputable def poissonCubeCloud {d : ℕ} (z : Fin d → ℤ)
    (c : PoissonFiniteCloud (Poisson.cube z)) : Measure (Poisson.E d) :=
  (poissonFiniteCloudMeasure _ c).map Subtype.val

/-- The natural count of points of a local cloud in a physical region. -/
noncomputable def poissonCubeCount {d : ℕ} (z : Fin d → ℤ)
    (c : PoissonFiniteCloud (Poisson.cube z)) (B : Set (Poisson.E d)) : ℕ := by
  classical
  exact ∑ i : Fin c.1, if (c.2.val i).val ∈ B then 1 else 0

lemma poissonCubeCloud_apply {d : ℕ} (z : Fin d → ℤ)
    (c : PoissonFiniteCloud (Poisson.cube z)) {B : Set (Poisson.E d)} (hB : MeasurableSet B) :
    poissonCubeCloud z c B = (poissonCubeCount z c B : ℝ≥0∞) := by
  classical
  rw [poissonCubeCloud, Measure.map_apply measurable_subtype_coe hB]
  simp only [poissonFiniteCloudMeasure, Measure.finsetSum_apply, poissonCubeCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (c.2.val i).val ∈ B <;>
    simp [Measure.dirac_apply' _ (hB.preimage measurable_subtype_coe), h]

lemma measurable_poissonCubeCloud {d : ℕ} (z : Fin d → ℤ) : Measurable (poissonCubeCloud z) :=
  (Measure.measurable_map _ measurable_subtype_coe).comp (measurable_poissonFiniteCloudMeasure _)

/-- Decode all local clouds into their locally finite counting measure. -/
noncomputable def poissonConfigurationMeasure {d : ℕ} (c : PoissonConfiguration d) :
    Measure (Poisson.E d) := Measure.sum (fun z => poissonCubeCloud z (c z))

lemma measurable_poissonConfigurationMeasure {d : ℕ} :
    Measurable (poissonConfigurationMeasure : PoissonConfiguration d → Measure (Poisson.E d)) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  simp only [poissonConfigurationMeasure, Measure.sum_apply _ hB]
  exact Measurable.tsum fun z => (Measure.measurable_coe hB).comp
    ((measurable_poissonCubeCloud z).comp (measurable_pi_apply z))

lemma poissonCubeCloud_apply_eq_zero {d : ℕ} (z : Fin d → ℤ)
    (c : PoissonFiniteCloud (Poisson.cube z)) {B : Set (Poisson.E d)}
    (hB : MeasurableSet B) (hz : z ∉ Poisson.cubeIndex '' B) : poissonCubeCloud z c B = 0 := by
  classical
  have hn (i : Fin c.1) : (c.2.val i).val ∉ B := fun hi =>
    hz ⟨(c.2.val i).val, hi, (c.2.val i).property⟩
  rw [poissonCubeCloud_apply z c hB]
  simp [poissonCubeCount, hn]

/-- Every decoded outcome is a locally finite counting measure, not merely almost every one. -/
theorem poissonConfigurationMeasure_counting {d : ℕ} (c : PoissonConfiguration d) :
    Poisson.IsLocallyFiniteCountingMeasure (poissonConfigurationMeasure c) := by
  classical
  apply Poisson.isLocallyFiniteCountingMeasure_of_counts
  intro B hB hb
  let F := (Poisson.finite_cubeIndex_image hb).toFinset
  have hzero (z : Fin d → ℤ) (hz : z ∉ F) : poissonCubeCloud z (c z) B = 0 := by
    apply poissonCubeCloud_apply_eq_zero z (c z) hB
    simpa only [F, Set.Finite.mem_toFinset] using hz
  rw [poissonConfigurationMeasure, Measure.sum_apply _ hB, tsum_eq_sum hzero]
  refine ⟨∑ z ∈ F, poissonCubeCount z (c z) B, ?_⟩
  simp only [Nat.cast_sum, poissonCubeCloud_apply _ _ hB]

/-- Restriction to one cube recovers precisely that cube's finite cloud. -/
lemma poissonConfigurationMeasure_restrict_cube {d : ℕ} (c : PoissonConfiguration d)
    (z : Fin d → ℤ) :
    (poissonConfigurationMeasure c).restrict (Poisson.cube z) = poissonCubeCloud z (c z) := by
  classical
  ext B hB
  have hzero (w : Fin d → ℤ) (hw : w ≠ z) :
      poissonCubeCloud w (c w) (B ∩ Poisson.cube z) = 0 := by
    apply poissonCubeCloud_apply_eq_zero w (c w) (hB.inter (Poisson.measurableSet_cube z))
    rintro ⟨p, hp, hpw⟩
    exact hw (hpw.symm.trans hp.2)
  rw [Measure.restrict_apply hB, poissonConfigurationMeasure,
    Measure.sum_apply _ (hB.inter (Poisson.measurableSet_cube z)), tsum_eq_single z hzero]
  rw [poissonCubeCloud_apply _ _ (hB.inter (Poisson.measurableSet_cube z)),
    poissonCubeCloud_apply _ _ hB]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [mem_inter_iff, (c z).2.val i |>.property, and_true]

/-- Canonical ordering removes all ambiguity in the measure representation. -/
theorem poissonConfigurationMeasure_injective {d : ℕ} :
    Function.Injective (poissonConfigurationMeasure : PoissonConfiguration d → Measure (Poisson.E d)) := by
  intro c c' h
  funext z
  apply poissonFiniteCloudMeasure_injective
  apply (MeasurableEmbedding.subtype_coe (Poisson.measurableSet_cube z)).map_injective
  have hh := congrArg (fun μ : Measure (Poisson.E d) => μ.restrict (Poisson.cube z)) h
  simpa only [poissonConfigurationMeasure_restrict_cube, poissonCubeCloud] using hh

end IsotropicVariance.Infra.Instances
