/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.Basic
import IsotropicVariance.Statements.Cited.IsOsIntegralOfOneLe
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The sum rule for finite sums

The sum rule of the paper, equation `eq:sum`, is the case `s ≥ 1` of [AKM, Lemma A.4]: for finitely
many `0 ≤ X_i ≤ O_s(θ_i)`, `∑ X_i ≤ O_s(∑ θ_i)`, with no independence. `isOs_sum_of_one_le` reads it
off the stated form of that lemma for integrals, `Cited.isOs_integral_of_one_le`, over the counting
measure of the index set.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace IsotropicVariance.Infra.Os

open Cited

/-- **The sum rule, equation `eq:sum`**: for `s ≥ 1` and finitely many `0 ≤ X_i ≤ O_s(θ_i)`,
`∑ X_i ≤ O_s(∑ θ_i)`, with no independence. -/
theorem isOs_sum_of_one_le {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s : ℝ} (hs : 1 ≤ s) (T : Finset ι) (θ : ι → ℝ)
    (hθ : ∀ i ∈ T, 0 < θ i) (X : ι → Ω → ℝ) (hX : ∀ i ∈ T, IsOs P s (θ i) (X i))
    (hX0 : ∀ i ∈ T, 0 ≤ᵐ[P] X i) :
    IsOs P s (∑ i ∈ T, θ i) (fun ω => ∑ i ∈ T, X i ω) := by
  let : MeasurableSpace T := ⊤
  have : MeasurableSingletonClass T := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  -- measurable versions, nonnegative at every point
  let Y : T → Ω → ℝ := fun i ω => max ((hX i i.2).1.mk (X i) ω) 0
  have hYm : ∀ i, Measurable (Y i) := fun i => (hX i i.2).1.measurable_mk.max measurable_const
  have hXY : ∀ i : T, X i =ᵐ[P] Y i := fun i => by
    filter_upwards [(hX i i.2).1.ae_eq_mk, hX0 i i.2] with ω h1 h2
    change X i ω = max ((hX i i.2).1.mk (X i) ω) 0
    rw [← h1]
    exact (max_eq_left h2).symm
  have hsum := (isOs_integral_of_one_le P Measure.count hs (fun i : T => θ i) (fun i => hθ i i.2)
    .of_discrete Integrable.of_finite Y (measurable_from_prod_countable_right hYm)
    (fun _ _ => le_max_right _ _) fun i => (hX i i.2).congr (hXY i)).2
  simp only [integral_count] at hsum
  rw [Finset.sum_coe_sort T θ] at hsum
  refine hsum.congr ?_
  filter_upwards [ae_all_iff.2 hXY] with ω hω
  rw [← Finset.sum_coe_sort T fun i => X i ω]
  exact Finset.sum_congr rfl fun i _ => (hω i).symm

end IsotropicVariance.Infra.Os
