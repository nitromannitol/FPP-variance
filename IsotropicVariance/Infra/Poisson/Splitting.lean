/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Poisson.Thinning
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Joint generating functions for disjoint cloud counts

Multinomial splitting of the iid marks followed by Poissonization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Complex
open scoped NNReal ENNReal BigOperators

namespace IsotropicVariance.Infra.Poisson

/-- Disjoint regions allow at most one nontrivial factor in a mark weight. -/
theorem disjoint_markWeight {X ι : Type*} [Fintype ι] (B : ι → Set X)
    [∀ i, DecidablePred (· ∈ B i)] (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (z : ι → ℂ) (x : X) :
    (∏ i, if x ∈ B i then z i else 1) =
      1 + ∑ i, (B i).indicator (fun _ => z i - 1) x := by
  classical
  by_cases hx : ∃ i, x ∈ B i
  · obtain ⟨j, hj⟩ := hx
    have hother (i : ι) (hij : i ≠ j) : x ∉ B i := by
      intro hi
      exact Set.disjoint_left.mp (hd hij) hi hj
    rw [Finset.prod_eq_single j, Finset.sum_eq_single j]
    · simp [hj]
    · intro i _ hij
      simp [hother i hij]
    · simp
    · intro i _ hij
      simp [hother i hij]
    · simp
  · have hn (i : ι) : x ∉ B i := fun hi => hx ⟨i, hi⟩
    simp [hn]

/-- The joint cloud generating monomial is a product over the retained marks. -/
theorem cloudCount_prod_pow {X ι : Type*} [Fintype ι] (B : ι → Set X)
    [∀ i, DecidablePred (· ∈ B i)] (w : CloudSample X) (z : ι → ℂ) :
    (∏ i, z i ^ cloudCount (B i) w) =
      ∏ j : Fin w.1, ∏ i, if w.2 j ∈ B i then z i else 1 := by
  classical
  simp_rw [cloudCount_pow]
  exact Finset.prod_comm

/-- The integral of the one-mark weight for disjoint regions. -/
theorem integral_disjoint_markWeight {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) [IsProbabilityMeasure ν] (B : ι → Set X)
    [∀ i, DecidablePred (· ∈ B i)] (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (z : ι → ℂ) :
    (∫ x, ∏ i, if x ∈ B i then z i else 1 ∂ν) =
      1 + ∑ i, (ν.real (B i) : ℂ) * (z i - 1) := by
  classical
  simp_rw [disjoint_markWeight B hd z]
  rw [integral_add (integrable_const _)
    (integrable_finsetSum _ (fun i _ => (integrable_const _).indicator (hB i))),
    integral_finsetSum _ (fun i _ => (integrable_const _).indicator (hB i))]
  simp [integral_indicator_const, hB, Complex.real_smul]

/-- Disjoint cloud counts have the product of Poisson generating functions. -/
theorem integral_prod_pow_cloudCount {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (∫ w, ∏ i, z i ^ cloudCount (B i) w ∂cloudLaw r ν) =
      ∏ i, Complex.exp ((r : ℂ) * ν.real (B i) * (z i - 1)) := by
  classical
  simp_rw [cloudCount_prod_pow]
  rw [integral_cloud_prod ν r (h := fun x => ∏ i, if x ∈ B i then z i else 1)
    (Finset.measurable_prod _ (fun i _ => Measurable.ite (hB i) measurable_const measurable_const))
    (by intro x; rw [norm_prod]; apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _); intro i _; split_ifs; exact hz i; simp),
    integral_disjoint_markWeight ν B hB hd]
  rw [← Complex.exp_sum]
  congr 1
  simp only [add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end IsotropicVariance.Infra.Poisson
