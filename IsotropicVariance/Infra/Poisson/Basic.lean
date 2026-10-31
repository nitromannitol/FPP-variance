/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# A measurable homogeneous Poisson point-process interface

For the Poisson alternative for the noise in Assumption `ass:local`. Counts are
ENNReal-valued evaluations of a random measure; their laws are the pushforwards of the natural
Poisson laws under the injective natural-number cast. Every outcome is locally finite and
integer-valued on bounded Borel sets. The predicate asserts joint independence for finite
disjoint bounded Borel families, never an unproved invariance or resampling conclusion.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace IsotropicVariance.Infra.Poisson

/-- The physical Euclidean space, with its Borel structure and Lebesgue volume. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A locally finite counting measure: its mass on every bounded Borel set is a natural number.
The local-finiteness class is recorded explicitly for Mathlib's measure APIs. -/
def IsLocallyFiniteCountingMeasure {d : ℕ} (ν : Measure (E d)) : Prop :=
  IsLocallyFiniteMeasure ν ∧
    ∀ B : Set (E d), MeasurableSet B → Bornology.IsBounded B → ∃ n : ℕ, ν B = n

/-- The natural Poisson distribution viewed as a law of ENNReal-valued counts. -/
noncomputable def poissonCountLaw (r : ℝ≥0) : Measure ℝ≥0∞ :=
  (poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞)

/-- The homogeneous Poisson process of intensity `lam` on Euclidean space.
`η` is measurable for the Giry sigma-algebra, each outcome is a locally finite counting measure,
and finite disjoint bounded Borel sets have independent counts with the prescribed Poisson laws.
No construction, uniqueness or rigid-motion property is assumed as a field. -/
structure IsPoissonProcess {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (lam : ℝ≥0) (η : Ω → Measure (E d)) (P : Measure Ω) : Prop where
  measurable : Measurable η
  counting : ∀ ω, IsLocallyFiniteCountingMeasure (η ω)
  count_law : ∀ B : Set (E d), MeasurableSet B → Bornology.IsBounded B →
    HasLaw (fun ω => η ω B) (poissonCountLaw (lam * (volume B).toNNReal)) P
  independent : ∀ (k : ℕ) (B : Fin k → Set (E d)), (∀ i, MeasurableSet (B i)) →
    (∀ i, Bornology.IsBounded (B i)) → Pairwise (fun i j => Disjoint (B i) (B j)) →
      iIndepFun (fun i ω => η ω (B i)) P

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {lam : ℝ≥0}
  {η : Ω → Measure (E d)} {P : Measure Ω}

/-- Every Borel count is measurable, including counts on unbounded sets. -/
theorem IsPoissonProcess.measurable_count (h : IsPoissonProcess lam η P)
    {B : Set (E d)} (hB : MeasurableSet B) : Measurable (fun ω => η ω B) :=
  (Measure.measurable_coe hB).comp h.measurable

end IsotropicVariance.Infra.Poisson
