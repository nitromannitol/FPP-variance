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
public import IsotropicVariance.Statements.Space.Pt

/-!
# `IsotropicVariance.TestFunction.reflectTranslate`

One declaration of the statements of this formalization (`IsotropicVariance.Statements`): the
definitions, the results cited from the literature and the main theorems, one per file.

This file holds a definition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance

/-- The test function `y ↦ χ(x − y)`, so that `(χ∗ω)(x) = ω(χ(x − ·))`. -/
noncomputable def TestFunction.reflectTranslate {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (x : Pt m) : 𝓓((⊤ : Opens (Pt m)), ℝ) where
  toFun y := χ (x - y)
  contDiff' := (TestFunctionClass.map_contDiff χ).comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' :=
    (TestFunctionClass.map_hasCompactSupport χ).comp_homeomorph (Homeomorph.subLeft x)
  tsupport_subset' := by simp

end IsotropicVariance
