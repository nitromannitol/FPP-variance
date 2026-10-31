/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Poisson.Cubes
public import IsotropicVariance.Infra.Poisson.Counts
public import IsotropicVariance.Infra.Poisson.Splitting

/-!
# Independent unit-cube clouds

The explicit standard Borel sample space and random counting measure for the homogeneous
Poisson construction. All samples are locally finite because bounded regions meet finitely
many cubes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace IsotropicVariance.Infra.Poisson

instance cube.standardBorelSpace {d : ℕ} (z : Fin d → ℤ) : StandardBorelSpace (cube z) :=
  (measurableSet_cube z).standardBorel

/-- One count and one infinite sequence of cube-valued marks at each integer cube. -/
abbrev ProcessSample (d : ℕ) := ∀ z : Fin d → ℤ, CloudSample (cube z)

/-- The product law of independent uniform Poisson clouds. -/
noncomputable def processLaw (d : ℕ) (lam : ℝ≥0) : Measure (ProcessSample d) :=
  Measure.infinitePi (fun z => cloudLaw lam (cubeUniform z))

instance processLaw.isProbabilityMeasure (d : ℕ) (lam : ℝ≥0) :
    IsProbabilityMeasure (processLaw d lam) := by
  unfold processLaw
  infer_instance

/-- Put a cube's finite cloud in physical space. -/
noncomputable def cubeCloud {d : ℕ} (z : Fin d → ℤ) (w : CloudSample (cube z)) :
    Measure (E d) := (cloud w).map Subtype.val

/-- Sum the independent finite clouds over all integer cubes. -/
noncomputable def process {d : ℕ} (w : ProcessSample d) : Measure (E d) :=
  Measure.sum (fun z => cubeCloud z (w z))

/-- The cube cloud is measurable for the Giry sigma-algebra. -/
theorem measurable_cubeCloud {d : ℕ} (z : Fin d → ℤ) : Measurable (cubeCloud z) :=
  (Measure.measurable_map _ measurable_subtype_coe).comp measurable_cloud

/-- The constructed random measure is Giry-measurable. -/
theorem measurable_process {d : ℕ} : Measurable (process : ProcessSample d → Measure (E d)) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  simp only [process, Measure.sum_apply _ hB]
  apply Measurable.tsum
  intro z
  exact (Measure.measurable_coe hB).comp ((measurable_cubeCloud z).comp (measurable_pi_apply z))

/-- Evaluation of a cube cloud is its natural-valued mark count. -/
theorem cubeCloud_apply {d : ℕ} (z : Fin d → ℤ) (w : CloudSample (cube z))
    {B : Set (E d)} (hB : MeasurableSet B) :
    cubeCloud z w B = (cloudCount (Subtype.val ⁻¹' B) w : ℝ≥0∞) := by
  rw [cubeCloud, Measure.map_apply measurable_subtype_coe hB,
    cloud_apply (hB.preimage measurable_subtype_coe)]

/-- Cubes outside the index image of a region contribute exactly zero mass. -/
theorem cubeCloud_apply_eq_zero {d : ℕ} (z : Fin d → ℤ) (w : CloudSample (cube z))
    {B : Set (E d)} (hB : MeasurableSet B) (hz : z ∉ cubeIndex '' B) :
    cubeCloud z w B = 0 := by
  have hempty : (Subtype.val ⁻¹' B : Set (cube z)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hz ⟨x.val, hx, x.property⟩
  rw [cubeCloud, Measure.map_apply measurable_subtype_coe hB, hempty, measure_empty]

/-- Every constructed outcome is a locally finite counting measure. -/
theorem process_counting {d : ℕ} (w : ProcessSample d) :
    IsLocallyFiniteCountingMeasure (process w) := by
  classical
  apply isLocallyFiniteCountingMeasure_of_counts
  intro B hB hb
  let F := (finite_cubeIndex_image hb).toFinset
  have hzero (z : Fin d → ℤ) (hz : z ∉ F) : cubeCloud z (w z) B = 0 := by
    apply cubeCloud_apply_eq_zero z (w z) hB
    simpa only [F, Set.Finite.mem_toFinset] using hz
  rw [process, Measure.sum_apply _ hB, tsum_eq_sum hzero]
  refine ⟨∑ z ∈ F, cloudCount (Subtype.val ⁻¹' B) (w z), ?_⟩
  simp only [Nat.cast_sum, cubeCloud_apply _ _ hB]

/-- Cube probabilities of physical Borel regions equal their Lebesgue masses in the cube. -/
theorem cubeUniform_preimage {d : ℕ} (z : Fin d → ℤ) {B : Set (E d)}
    (hB : MeasurableSet B) :
    cubeUniform z (Subtype.val ⁻¹' B) = volume (B ∩ cube z) := by
  rw [← Measure.map_apply measurable_subtype_coe hB, map_cubeUniform,
    Measure.restrict_apply hB]

/-- The natural count contributed by a finite family of cubes. -/
noncomputable def finiteCubeCount {d : ℕ} (F : Finset (Fin d → ℤ)) (B : Set (E d))
    (w : ProcessSample d) : ℕ :=
  ∑ z ∈ F, cloudCount (Subtype.val ⁻¹' B) (w z)

/-- Finite cube counts are measurable. -/
theorem measurable_finiteCubeCount {d : ℕ} (F : Finset (Fin d → ℤ))
    {B : Set (E d)} (hB : MeasurableSet B) : Measurable (finiteCubeCount F B) := by
  unfold finiteCubeCount
  exact Finset.measurable_sum F (fun z _ =>
    (measurable_cloudCount (hB.preimage measurable_subtype_coe)).comp (measurable_pi_apply z))

/-- An exact finite-sum representation of a bounded-region count, for any covering cube family. -/
theorem process_apply_eq_finiteCubeCount {d : ℕ} (F : Finset (Fin d → ℤ))
    {B : Set (E d)} (hB : MeasurableSet B) (hF : cubeIndex '' B ⊆ (F : Set (Fin d → ℤ)))
    (w : ProcessSample d) : process w B = (finiteCubeCount F B w : ℝ≥0∞) := by
  rw [process, Measure.sum_apply _ hB, tsum_eq_sum (s := F)]
  · simp only [finiteCubeCount, Nat.cast_sum, cubeCloud_apply _ _ hB]
  · intro z hz
    exact cubeCloud_apply_eq_zero z (w z) hB (fun hh => hz (hF hh))

/-- The contribution from a single cube has its prescribed Poisson law under the product law. -/
theorem hasLaw_cubeCount {d : ℕ} (lam : ℝ≥0) (z : Fin d → ℤ)
    {B : Set (E d)} (hB : MeasurableSet B) :
    HasLaw (fun w : ProcessSample d => cloudCount (Subtype.val ⁻¹' B) (w z))
      (poissonMeasure (lam * (volume (B ∩ cube z)).toNNReal)) (processLaw d lam) := by
  have hlaw := (hasLaw_cloudCount (cubeUniform z) lam
    (hB.preimage measurable_subtype_coe)).comp
    (measurePreserving_eval_infinitePi (fun z => cloudLaw lam (cubeUniform z)) z).hasLaw
  simpa only [cubeUniform_preimage z hB, processLaw, Function.comp_def, Function.eval] using hlaw

/-- Contributions from different cubes are independent. -/
theorem iIndepFun_cubeCounts {d : ℕ} (lam : ℝ≥0) {B : Set (E d)} (hB : MeasurableSet B) :
    iIndepFun (fun z (w : ProcessSample d) => cloudCount (Subtype.val ⁻¹' B) (w z))
      (processLaw d lam) :=
  iIndepFun_infinitePi (fun _z => measurable_cloudCount (hB.preimage measurable_subtype_coe))

/-- A finite sum of independent natural Poisson variables has the summed rate. -/
theorem hasLaw_finset_sum_poisson {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → ℕ} {r : ι → ℝ≥0}
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X P)
    (hl : ∀ i, HasLaw (X i) (poissonMeasure (r i)) P) (F : Finset ι) :
    HasLaw (∑ i ∈ F, X i) (poissonMeasure (∑ i ∈ F, r i)) P := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, poissonMeasure_zero]
    exact hasLaw_dirac_of_ae_eq (Filter.Eventually.of_forall fun _ => rfl)
  | @insert i F hiF ih =>
    rw [Finset.sum_insert hiF, Finset.sum_insert hiF]
    exact (hi.indepFun_finsetSum_of_notMem hm hiF).symm.hasLaw_add_poissonMeasure (hl i) ih

/-- The count on a finite family of cubes is Poisson with the sum of the cube rates. -/
theorem hasLaw_finiteCubeCount {d : ℕ} (lam : ℝ≥0) (F : Finset (Fin d → ℤ))
    {B : Set (E d)} (hB : MeasurableSet B) :
    HasLaw (finiteCubeCount F B)
      (poissonMeasure (∑ z ∈ F, lam * (volume (B ∩ cube z)).toNNReal)) (processLaw d lam) := by
  have hh := hasLaw_finset_sum_poisson
    (fun z => (measurable_cloudCount (hB.preimage measurable_subtype_coe)).comp (measurable_pi_apply z))
    (iIndepFun_cubeCounts lam hB) (fun z => hasLaw_cubeCount lam z hB) F
  have heq : (∑ z ∈ F, (fun w : ProcessSample d => cloudCount (Subtype.val ⁻¹' B) (w z))) =
      finiteCubeCount F B := by
    funext w
    simp only [finiteCubeCount, Finset.sum_apply]
  simpa only [Function.comp_def, heq] using hh

/-- Lebesgue masses in a covering finite cube family sum to the region's mass. -/
theorem sum_volume_inter_cube {d : ℕ} (F : Finset (Fin d → ℤ))
    {B : Set (E d)} (hB : MeasurableSet B) (hF : cubeIndex '' B ⊆ (F : Set (Fin d → ℤ))) :
    (∑ z ∈ F, volume (B ∩ cube z)) = volume B := by
  have hu : (⋃ z ∈ F, B ∩ cube z) = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, _, hz⟩ := Set.mem_iUnion₂.mp hx
      exact hz.1
    · intro hx
      exact Set.mem_iUnion₂.mpr ⟨cubeIndex x, hF ⟨x, hx, rfl⟩, hx, rfl⟩
  calc
    (∑ z ∈ F, volume (B ∩ cube z)) = volume (⋃ z ∈ F, B ∩ cube z) := by
      symm
      apply measure_biUnion_finset
      · intro z _ w _ hzw
        exact (pairwiseDisjoint_cube hzw).mono inter_subset_right inter_subset_right
      · intro z _
        exact hB.inter (measurableSet_cube z)
    _ = volume B := congrArg volume hu

/-- Bounded-region counts of the constructed random measure have the required Poisson law. -/
theorem hasLaw_process_count {d : ℕ} (lam : ℝ≥0) {B : Set (E d)}
    (hB : MeasurableSet B) (hb : Bornology.IsBounded B) :
    HasLaw (fun w : ProcessSample d => process w B)
      (poissonCountLaw (lam * (volume B).toNNReal)) (processLaw d lam) := by
  classical
  let F := (finite_cubeIndex_image hb).toFinset
  have hF : cubeIndex '' B ⊆ (F : Set (Fin d → ℤ)) := by
    intro z hz
    change z ∈ (finite_cubeIndex_image hb).toFinset
    simpa only [Set.Finite.mem_toFinset] using hz
  have hsum : (∑ z ∈ F, lam * (volume (B ∩ cube z)).toNNReal) =
      lam * (volume B).toNNReal := by
    rw [← Finset.mul_sum, ← ENNReal.toNNReal_sum]
    · rw [sum_volume_inter_cube F hB hF]
    · intro z _
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_left) hb.measure_lt_top)
  have hlaw := (hasLaw_map (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ≥0∞)).aemeasurable).comp
    (hasLaw_finiteCubeCount lam F hB)
  rw [hsum] at hlaw
  have heq : (Nat.cast : ℕ → ℝ≥0∞) ∘ finiteCubeCount F B =
      (fun w : ProcessSample d => process w B) := by
    funext w
    exact (process_apply_eq_finiteCubeCount F hB hF w).symm
  rw [heq] at hlaw
  exact hlaw

end IsotropicVariance.Infra.Poisson
