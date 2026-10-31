/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonTransfer
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-! # Countable coding of locally finite Poisson configurations

Bounded evaluations on a countable generating pi-system separate locally finite measures.
This does not assert standard Borel structure for the whole Giry space.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace IsotropicVariance.Infra.Instances

/-- Finite intersections of a countable generating sequence, including the empty intersection. -/
noncomputable def poissonCodeTest (m : ℕ) (F : Finset ℕ) : Set (Pt m) :=
  ⋂ i ∈ F, MeasurableSpace.natGeneratingSequence (Pt m) i

lemma measurableSet_poissonCodeTest (m : ℕ) (F : Finset ℕ) :
    MeasurableSet (poissonCodeTest m F) :=
  MeasurableSet.biInter (Finset.countable_toSet F) fun i _ =>
    MeasurableSpace.measurableSet_natGeneratingSequence i

lemma isPiSystem_poissonCodeTest (m : ℕ) : IsPiSystem (range (poissonCodeTest m)) := by
  classical
  rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩ _
  refine ⟨F ∪ G, ?_⟩
  ext x
  simp only [poissonCodeTest, mem_iInter, Finset.mem_union, mem_inter_iff]
  aesop

lemma generateFrom_poissonCodeTest (m : ℕ) :
    MeasurableSpace.generateFrom (range (poissonCodeTest m)) =
      (inferInstance : MeasurableSpace (Pt m)) := by
  classical
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨F, rfl⟩
    exact measurableSet_poissonCodeTest m F
  · rw [← MeasurableSpace.generateFrom_natGeneratingSequence (Pt m)]
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨n, rfl⟩
    exact ⟨{n}, by simp [poissonCodeTest]⟩

/-- Countably many bounded Borel evaluations of a measure configuration. -/
noncomputable def poissonCountCode {m : ℕ} (μ : Measure (Pt m)) : ℕ × Finset ℕ → ℝ≥0∞ :=
  fun p => μ (poissonCodeTest m p.2 ∩ Metric.closedBall 0 p.1)

lemma measurable_poissonCountCode {m : ℕ} :
    Measurable (poissonCountCode : Measure (Pt m) → ℕ × Finset ℕ → ℝ≥0∞) := by
  apply Measurable.of_eval
  intro p
  exact Measure.measurable_coe
    ((measurableSet_poissonCodeTest m p.2).inter Metric.isClosed_closedBall.measurableSet)

/-- The code is injective among locally finite measures. Finiteness is needed only on one side;
no standard Borel or finiteness assertion about arbitrary Giry configurations is used. -/
theorem poissonCountCode_ext {m : ℕ} {μ ν : Measure (Pt m)}
    (hμ : ∀ n : ℕ, μ (Metric.closedBall 0 n) < ⊤)
    (hcode : poissonCountCode μ = poissonCountCode ν) : μ = ν := by
  have hrestr (n : ℕ) : μ.restrict (Metric.closedBall 0 n) = ν.restrict (Metric.closedBall 0 n) := by
    have : IsFiniteMeasure (μ.restrict (Metric.closedBall 0 n)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hμ n⟩
    apply ext_of_generate_finite (range (poissonCodeTest m))
      (generateFrom_poissonCodeTest m).symm (isPiSystem_poissonCodeTest m)
    · rintro _ ⟨F, rfl⟩
      simpa only [poissonCountCode, Measure.restrict_apply (measurableSet_poissonCodeTest m F)] using congrFun hcode (n, F)
    · simpa only [Measure.restrict_apply_univ, poissonCountCode, poissonCodeTest,
        Finset.notMem_empty, iInter_of_empty, iInter_const, univ_inter] using congrFun hcode (n, ∅)
  ext B hB
  have hm : Monotone (fun n : ℕ => B ∩ Metric.closedBall (0 : Pt m) n) := by
    intro n k hnk
    exact inter_subset_inter_right B (Metric.closedBall_subset_closedBall (by exact_mod_cast hnk))
  rw [← Metric.iUnion_inter_closedBall_nat B (0 : Pt m), hm.directed_le.measure_iUnion,
    hm.directed_le.measure_iUnion]
  congr 1
  funext n
  simpa only [Measure.restrict_apply hB] using congrArg (fun ξ : Measure (Pt m) => ξ B) (hrestr n)

end IsotropicVariance.Infra.Instances
