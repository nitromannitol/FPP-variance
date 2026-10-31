/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.ArcMeasure
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Push-forward under continuous monotone changes of parameter

A continuous nondecreasing map from the unit interval onto a closed interval pushes a finite measure
forward to another measure if their cumulative masses match under the map. Flat intervals
are allowed; no inverse or strict monotonicity is assumed.
-/

@[expose] public section
open Set MeasureTheory Filter
open scoped Topology

namespace IsotropicVariance.Infra.Curves

lemma mapsTo_Icc_of_monotoneOn_endpoints {φ : ℝ → ℝ}
    (hm : MonotoneOn φ (Icc 0 1)) (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    MapsTo φ (Icc 0 1) (Icc 0 1) := by
  intro t ht
  constructor
  · simpa [h0] using hm (by simp) ht ht.1
  · simpa [h1] using hm ht (by simp) ht.2

/-- A distribution-function criterion allowing flat intervals in the parameter map. -/
theorem map_eq_of_cumulative_Icc (μ ν : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) 1) (hν : ∀ᵐ t ∂ν, t ∈ Icc a b)
    {φ : ℝ → ℝ} (hc : Continuous φ) (hm : MonotoneOn φ (Icc 0 1))
    (h0 : φ 0 = a) (h1 : φ 1 = b)
    (hmass : μ univ = ν univ)
    (hCDF : ∀ t ∈ Icc (0 : ℝ) 1, μ (Iic t) = ν (Iic (φ t))) : μ.map φ = ν := by
  have hmap : MapsTo φ (Icc (0 : ℝ) 1) (Icc a b) := by
    intro t ht
    constructor
    · simpa [h0] using hm (by simp) ht ht.1
    · simpa [h1] using hm ht (by simp) ht.2
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hc.measurable measurableSet_Iic]
  by_cases hx0 : x < a
  · have hleft : μ (φ ⁻¹' Iic x) = 0 := by
      apply measure_mono_null (show φ ⁻¹' Iic x ⊆ (Icc (0 : ℝ) 1)ᶜ by
        intro t ht hti; exact (not_le_of_gt (hx0.trans_le (hmap hti).1)) ht)
      exact ae_iff.mp hμ
    have hright : ν (Iic x) = 0 := by
      apply measure_mono_null (show Iic x ⊆ (Icc a b)ᶜ by
        intro t ht hti; exact (not_le_of_gt (hx0.trans_le hti.1)) ht)
      exact ae_iff.mp hν
    rw [hleft, hright]
  by_cases hx1 : b ≤ x
  · have hleft : μ (φ ⁻¹' Iic x) = μ univ := by
      apply measure_congr
      filter_upwards [hμ] with t ht
      exact propext ⟨fun _ => mem_univ _, fun _ => (hmap ht).2.trans hx1⟩
    have hright : ν (Iic x) = ν univ := by
      apply measure_congr
      filter_upwards [hν] with t ht
      exact propext ⟨fun _ => mem_univ _, fun _ => ht.2.trans hx1⟩
    rw [hleft, hright, hmass]
  have hx : x ∈ Icc a b := ⟨le_of_not_gt hx0, (lt_of_not_ge hx1).le⟩
  have himage : φ '' Icc (0 : ℝ) 1 = Icc a b := by
    simpa [h0, h1] using hc.continuousOn.image_Icc_of_monotoneOn zero_le_one hm
  obtain ⟨w, hw, hwx⟩ := (show x ∈ φ '' Icc (0 : ℝ) 1 by rwa [himage])
  have hcompact : IsCompact (Icc (0 : ℝ) 1 ∩ φ ⁻¹' Iic x) :=
    isCompact_Icc.inter_right (isClosed_Iic.preimage hc)
  obtain ⟨t, ht⟩ := hcompact.exists_isGreatest ⟨w, hw, hwx.le⟩
  have hφt : φ t = x := le_antisymm ht.1.2 (by
    rw [← hwx]; exact hm hw ht.1.1 (ht.2 ⟨hw, hwx.le⟩))
  have heq : μ (φ ⁻¹' Iic x) = μ (Iic t) := by
    apply measure_congr
    filter_upwards [hμ] with z hz
    exact propext ⟨fun h => ht.2 ⟨hz, h⟩, fun h => (hm hz ht.1.1 h).trans hφt.le⟩
  rw [heq, hCDF t ht.1.1, hφt]

end IsotropicVariance.Infra.Curves
