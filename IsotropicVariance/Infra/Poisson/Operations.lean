/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Poisson.Basic

/-!
# Exact restrictions and splices of locally finite counting measures

The operations act on every outcome, and measurability uses the Giry sigma-algebra.
These are deterministic identities; no unproved probabilistic splice law is assumed.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace IsotropicVariance.Infra.Poisson

variable {d : ℕ}

/-- Finite natural counts on bounded Borel sets imply the usual local-finiteness class. -/
theorem isLocallyFiniteCountingMeasure_of_counts {ν : Measure (E d)}
    (h : ∀ B : Set (E d), MeasurableSet B → Bornology.IsBounded B → ∃ n : ℕ, ν B = n) :
    IsLocallyFiniteCountingMeasure ν := by
  refine ⟨⟨fun x => ?_⟩, h⟩
  obtain ⟨n, hn⟩ := h (Metric.ball x 1) measurableSet_ball Metric.isBounded_ball
  exact ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, by rw [hn]; exact ENNReal.natCast_lt_top n⟩

/-- Restriction is Giry-measurable. -/
theorem measurable_restrict {S : Set (E d)} (hS : MeasurableSet S) :
    Measurable (fun ν : Measure (E d) => ν.restrict S) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  simp only [Measure.restrict_apply hB]
  exact Measure.measurable_coe (hB.inter hS)

end IsotropicVariance.Infra.Poisson
