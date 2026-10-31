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
public import IsotropicVariance.Statements.Curves.RectifiableCurve
public import IsotropicVariance.Statements.Curves.RectifiableCurveCumulativeLength

/-!
# `IsotropicVariance.RectifiableCurve.continuous_cumulativeLength`

One declaration of the statements of this formalization (`IsotropicVariance.Statements`): the
definitions, the results cited from the literature and the main theorems, one per file.

This file holds a definition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance
namespace RectifiableCurve

variable {E : Type*} [PseudoMetricSpace E]

/-- The cumulative length of a rectifiable curve is continuous. -/
lemma continuous_cumulativeLength (γ : RectifiableCurve E) : Continuous γ.cumulativeLength := by
  have h : ContinuousOn (variationOnFromTo γ.toFun (Icc 0 1) 0) (Icc 0 1) := by
    intro t ht
    exact (γ.boundedVariationOn.continuousWithinAt_variationOnFromTo_iff
      (by simp) ht).mpr (γ.continuousOn t ht)
  exact h.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun t => (projIcc 0 1 zero_le_one t).property)

end RectifiableCurve
end IsotropicVariance
