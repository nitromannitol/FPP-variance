/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Poisson.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Degenerate intensity, probability normalization, and null-set counts

The zero-intensity process is constructed on a standard Borel probability space. Count laws
force the ambient measure to be a probability measure. Bounded Borel volume-null sets have no
points almost surely. These facts use the genuine process predicate, not additional hypotheses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace IsotropicVariance.Infra.Poisson

instance poissonCountLaw.isProbabilityMeasure (r : ℝ≥0) : IsProbabilityMeasure (poissonCountLaw r) := by
  unfold poissonCountLaw
  infer_instance

/-- The finite Poisson distribution at rate zero is the point mass at zero. -/
theorem poissonMeasure_zero : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro n
  by_cases hn : n = 0
  · subst n
    simp [poissonMeasure_singleton]
  · simp [poissonMeasure_singleton, hn, zero_pow hn]

/-- The ENNReal count law at rate zero is the point mass at zero. -/
theorem poissonCountLaw_zero : poissonCountLaw 0 = Measure.dirac (0 : ℝ≥0∞) := by
  rw [poissonCountLaw, poissonMeasure_zero, Measure.map_dirac' (show Measurable (Nat.cast : ℕ → ℝ≥0∞) from Measurable.of_discrete)]
  simp

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {lam : ℝ≥0}
  {η : Ω → Measure (E d)} {P : Measure Ω}

/-- The finite-count laws force probability normalization of the sample law. -/
theorem IsPoissonProcess.isProbabilityMeasure (h : IsPoissonProcess lam η P) :
    IsProbabilityMeasure P :=
  (h.count_law ∅ MeasurableSet.empty Bornology.isBounded_empty).isProbabilityMeasure

end IsotropicVariance.Infra.Poisson
