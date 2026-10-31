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
public import IsotropicVariance.Statements.Space.IsProperRigidMotion
public import IsotropicVariance.Statements.Space.Pt

/-!
# `IsotropicVariance.IsLocalDensity`

One declaration of the statements of this formalization (`IsotropicVariance.Statements`): the
definitions, the results cited from the literature and the main theorems, one per file.

This file holds a definition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance

/-- **Assumption `ass:local`** for a density `ρ(ω, x)` of the noise
configuration `ω` and the point `x`, given the restrictions `agree` and the motions `moved` of
the configurations of the noise (white noise: `WhiteNoiseConfig.AgreeOn`,
`WhiteNoiseConfig.IsMovedBy`; Poisson: `PoissonConfig.AgreeOn`, `PoissonConfig.IsMovedBy`). -/
structure IsLocalDensity {m : ℕ} {N : Type*} [MeasurableSpace N]
    (agree : Set (Pt m) → N → N → Prop) (moved : (Pt m ≃ᵃⁱ[ℝ] Pt m) → N → N → Prop)
    (ρ : N → Pt m → ℝ) : Prop where
  /-- The density is jointly Borel measurable. -/
  measurable : Measurable (Function.uncurry ρ)
  /-- (1) The value `ρ(ω, x)` is determined by the restriction of `ω` to the closed unit ball
  centered at `x`. -/
  determined : ∀ (x : Pt m) (ν ν' : N), agree (Metric.closedBall x 1) ν ν' → ρ ν x = ρ ν' x
  /-- (2) The density takes values between two fixed positive constants. -/
  bounds : ∃ a b : ℝ, 0 < a ∧ ∀ ν x, a ≤ ρ ν x ∧ ρ ν x ≤ b
  /-- (3) Moving the noise by a (proper) rigid motion moves the density by the same motion. -/
  covariant : ∀ g : Pt m ≃ᵃⁱ[ℝ] Pt m, IsProperRigidMotion g →
    ∀ ν ν' : N, moved g ν ν' → ∀ x, ρ ν' (g x) = ρ ν x

end IsotropicVariance
