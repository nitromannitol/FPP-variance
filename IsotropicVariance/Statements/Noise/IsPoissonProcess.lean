/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `IsotropicVariance.IsPoissonProcess`

One declaration of the statements of this formalization (`IsotropicVariance.Statements`): the
definitions, the results cited from the literature and the main theorems, one per file.

This file holds a definition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance

/-- `η` is a homogeneous Poisson process on `E` with intensity `lam` under `P`
(Assumption `ass:local`): a measurable random measure (Giry σ-algebra), every value
of which is a locally finite counting measure (integer-valued on bounded Borel sets), whose
counts of pairwise disjoint bounded Borel sets are independent, with Poisson laws of means
`lam · volume`. The counts are taken in `[0, ∞]`. -/
def IsPoissonProcess {E : Type*} [PseudoMetricSpace E] [MeasureSpace E] (lam : ℝ≥0)
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → Measure E) (P : Measure Ω) : Prop :=
  Measurable η ∧
    (∀ ω (B : Set E), MeasurableSet B → Bornology.IsBounded B → ∃ k : ℕ, η ω B = k) ∧
    ∀ (k : ℕ) (B : Fin k → Set E), (∀ i, MeasurableSet (B i)) →
      (∀ i, Bornology.IsBounded (B i)) → Pairwise (Function.onFun Disjoint B) →
        iIndepFun (fun i ω => η ω (B i)) P ∧
          ∀ i, HasLaw (fun ω => η ω (B i))
            ((poissonMeasure (lam * (volume (B i)).toNNReal)).map (fun n : ℕ => (n : ℝ≥0∞))) P

end IsotropicVariance
