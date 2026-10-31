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
public import IsotropicVariance.Statements.Assumption.IsLocalDensity
public import IsotropicVariance.Statements.Configurations.PoissonConfigAgreeOn
public import IsotropicVariance.Statements.Configurations.PoissonConfigIsMovedBy
public import IsotropicVariance.Statements.Curves.PassageTime
public import IsotropicVariance.Statements.Noise.IsPoissonProcess
public import IsotropicVariance.Statements.Space.Pt
import IsotropicVariance.Paper.Closing.Main

/-!
# Proof of `IsotropicVariance.variance_passageTime_le_norm_of_isPoissonProcess`

Proves `IsotropicVariance.Providers.variance_passageTime_le_norm_of_isPoissonProcess`, with exactly
the type of the theorem `IsotropicVariance.variance_passageTime_le_norm_of_isPoissonProcess` stated
in `IsotropicVariance.Statements.Main.VariancePassageTimeLeNormOfIsPoissonProcess`, by
`IsotropicVariance.Paper.Closing.variance_passageTime_le_norm_of_isPoissonProcess`. The statement
module proves its theorem from this one and is not imported here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance.Providers

/-- **Local densities** (Theorem `thm:general`), for a homogeneous Poisson process, at every
point. Let `d = m + 1 ≥ 2`, let `η` be a Poisson process of intensity `lam > 0` on a standard Borel
probability space, and let the density `ρ` satisfy Assumption `ass:local`. Then there is `ε > 0`
such that, for every point `x` with `|x|` sufficiently large, the passage time `T(0, x)` is a
random variable with `Var T(0, x) ≤ |x|^{1-ε}`. -/
theorem variance_passageTime_le_norm_of_isPoissonProcess {m : ℕ} (hm : 1 ≤ m) {lam : ℝ≥0}
    (hlam : 0 < lam) {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {η : Ω → Measure (Pt m)} (hη : IsPoissonProcess lam η P)
    {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r₀ : ℝ, ∀ x : Pt m, r₀ ≤ ‖x‖ →
      AEMeasurable (fun ω => passageTime (ρ (η ω)) 0 x) P ∧
        evariance (fun ω => passageTime (ρ (η ω)) 0 x) P ≤ ENNReal.ofReal (‖x‖ ^ (1 - ε)) :=
  IsotropicVariance.Paper.Closing.variance_passageTime_le_norm_of_isPoissonProcess hm hlam hη hρ

end IsotropicVariance.Providers
