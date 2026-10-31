/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Poisson.FiniteCounts
public import IsotropicVariance.Infra.Poisson.Operations
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Uniqueness and rigid-motion invariance of homogeneous Poisson laws

Bounded Borel evaluations already generate the Giry sigma-algebra, by exhaustion with closed balls.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace IsotropicVariance.Infra.Poisson

/-- Bounded Borel regions, used as an index type for joint evaluations. -/
abbrev BoundedBorelSets (d : ℕ) :=
  {B : Set (E d) // MeasurableSet B ∧ Bornology.IsBounded B}

/-- Bounded Borel evaluations of a measure. -/
def boundedEvaluations {d : ℕ} (ν : Measure (E d)) : BoundedBorelSets d → ℝ≥0∞ :=
  fun B => ν B.1

/-- A measure on any Borel set is the supremum of its bounded closed-ball truncations. -/
theorem measure_eq_iSup_inter_closedBall {d : ℕ} (ν : Measure (E d)) (B : Set (E d)) :
    ν B = ⨆ n : ℕ, ν (B ∩ Metric.closedBall 0 n) := by
  have hm : Monotone (fun n : ℕ => B ∩ Metric.closedBall (0 : E d) n) := by
    intro m n hmn
    exact inter_subset_inter_right B (Metric.closedBall_subset_closedBall (by exact_mod_cast hmn))
  rw [← hm.directed_le.measure_iUnion, Metric.iUnion_inter_closedBall_nat]

/-- Bounded Borel evaluations generate the full Giry sigma-algebra. -/
theorem giry_eq_comap_boundedEvaluations {d : ℕ} :
    (inferInstance : MeasurableSpace (Measure (E d))) =
      MeasurableSpace.comap boundedEvaluations inferInstance := by
  have hcan : Measurable (boundedEvaluations : Measure (E d) → BoundedBorelSets d → ℝ≥0∞) :=
    Measurable.of_eval fun B => Measure.measurable_coe B.2.1
  let m : MeasurableSpace (Measure (E d)) :=
    MeasurableSpace.comap boundedEvaluations inferInstance
  have hbound (B : Set (E d)) (hB : MeasurableSet B) (hb : Bornology.IsBounded B) :
      @Measurable (Measure (E d)) ℝ≥0∞ m inferInstance (fun ν => ν B) := by
    have he : Measurable (fun v : BoundedBorelSets d → ℝ≥0∞ => v ⟨B, hB, hb⟩) :=
      measurable_pi_apply _
    have hm : @Measurable (Measure (E d)) (BoundedBorelSets d → ℝ≥0∞) m
        inferInstance boundedEvaluations := Measurable.of_comap_le le_rfl
    exact he.comp hm
  have hfull : @Measurable (Measure (E d)) (Measure (E d)) m Measure.instMeasurableSpace id := by
    apply Measure.measurable_of_measurable_coe (mβ := m)
    intro B hB
    have heq : (fun ν : Measure (E d) => id ν B) =
        (fun ν => ⨆ n : ℕ, ν (B ∩ Metric.closedBall 0 n)) := by
      funext ν
      exact measure_eq_iSup_inter_closedBall ν B
    rw [heq]
    apply Measurable.iSup
    intro n
    exact hbound _ (hB.inter Metric.isClosed_closedBall.measurableSet)
      (Metric.isBounded_closedBall.subset inter_subset_right)
  apply le_antisymm
  · simpa only [MeasurableSpace.comap_id] using hfull.comap_le
  · exact hcan.comap_le

/-- Bounded joint evaluations determine a random measure's law. -/
theorem map_eq_of_joint_bounded_counts {d : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {η : Ω → Measure (E d)} {ξ : Ω' → Measure (E d)} (hη : Measurable η) (hξ : Measurable ξ)
    (h : ∀ I : Finset (BoundedBorelSets d),
      P.map (fun ω => I.restrict (boundedEvaluations (η ω))) =
        Q.map (fun ω => I.restrict (boundedEvaluations (ξ ω)))) :
    P.map η = Q.map ξ := by
  have heval : Measurable (boundedEvaluations : Measure (E d) → BoundedBorelSets d → ℝ≥0∞) :=
    Measurable.of_eval fun B => Measure.measurable_coe B.2.1
  have hηeval : Measurable (fun ω => boundedEvaluations (η ω)) := heval.comp hη
  have hξeval : Measurable (fun ω => boundedEvaluations (ξ ω)) := heval.comp hξ
  have heq : P.map (fun ω => boundedEvaluations (η ω)) = Q.map (fun ω => boundedEvaluations (ξ ω)) := by
    have hp := isProjectiveLimit_map (hηeval.aemeasurable (μ := P))
    simp_rw [h] at hp
    exact hp.unique (isProjectiveLimit_map (hξeval.aemeasurable (μ := Q)))
  ext S hS
  have hS' : MeasurableSet[MeasurableSpace.comap boundedEvaluations inferInstance] S := by
    rw [← giry_eq_comap_boundedEvaluations]
    exact hS
  obtain ⟨T, hT, rfl⟩ := hS'
  rw [Measure.map_apply hη (heval hT), Measure.map_apply hξ (heval hT)]
  have hh := congrArg (fun μ : Measure (BoundedBorelSets d → ℝ≥0∞) => μ T) heq
  rw [Measure.map_apply hηeval hT, Measure.map_apply hξeval hT] at hh
  convert hh using 1 <;> congr 1

/-- A homogeneous Poisson process has a unique law at its prescribed intensity. -/
theorem IsPoissonProcess.law_eq {d : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {lam : ℝ≥0}
    {η : Ω → Measure (E d)} {ξ : Ω' → Measure (E d)} {P : Measure Ω} {Q : Measure Ω'}
    (hη : IsPoissonProcess lam η P) (hξ : IsPoissonProcess lam ξ Q) :
    P.map η = Q.map ξ := by
  have := hη.isProbabilityMeasure
  have := hξ.isProbabilityMeasure
  apply map_eq_of_joint_bounded_counts hη.measurable hξ.measurable
  intro I
  simpa only [Finset.restrict_def, boundedEvaluations] using
    hη.map_bounded_counts_eq hξ (fun B : I => B.val.val)
      (fun B => B.val.property.1) (fun B => B.val.property.2)

end IsotropicVariance.Infra.Poisson
