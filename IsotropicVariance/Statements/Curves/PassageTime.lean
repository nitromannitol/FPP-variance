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
public import IsotropicVariance.Statements.Curves.RectifiableCurveCost
public import IsotropicVariance.Statements.Space.Pt

/-!
# `IsotropicVariance.passageTime`

One declaration of the statements of this formalization (`IsotropicVariance.Statements`): the
definitions, the results cited from the literature and the main theorems, one per file.

This file holds a definition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance

/-- The passage time `T(u,v) = inf_{π : u → v} ∫_π ρ(x) |dx|` over rectifiable curves from `u`
to `v` (the introduction), for a real density `σ` (negative values count as zero; the densities
of the theorems are positive). The infimum is finite, since a segment is a rectifiable curve and
the densities of the theorems are bounded, so the real value is taken. -/
noncomputable def passageTime {m : ℕ} (σ : Pt m → ℝ) (u v : Pt m) : ℝ :=
  (⨅ (γ : RectifiableCurve (Pt m)) (_ : γ.toFun 0 = u) (_ : γ.toFun 1 = v),
    γ.cost (fun x => ENNReal.ofReal (σ x))).toReal

end IsotropicVariance
