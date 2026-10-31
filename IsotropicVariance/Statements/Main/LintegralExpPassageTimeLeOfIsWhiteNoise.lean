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
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfig
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfigAgreeOn
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfigInstMeasurableSpace
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfigIsMovedBy
public import IsotropicVariance.Statements.Curves.PassageTime
public import IsotropicVariance.Statements.Noise.IsWhiteNoise
public import IsotropicVariance.Statements.Space.EOne
public import IsotropicVariance.Statements.Space.Pt
import IsotropicVariance.Providers.LintegralExpPassageTimeLeOfIsWhiteNoise

/-!
# `IsotropicVariance.lintegral_exp_passageTime_le_of_isWhiteNoise`

One declaration of the statements of this formalization (`IsotropicVariance.Statements`): the
definitions, the results cited from the literature and the main theorems, one per file.

This file states a main theorem; its proof is
`IsotropicVariance.Providers.lintegral_exp_passageTime_le_of_isWhiteNoise`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance

/-- **Local densities** (Theorem `thm:general`), for Gaussian white noise. Let `d = m + 1 ≥ 2`,
let `W` be white noise on a standard Borel probability space, and let the density `ρ` satisfy
Assumption `ass:local`. Then the time constant `μ = lim_{t→∞} t⁻¹ E[T(0, t e₁)]` exists, and
there are `ε > 0` and `C < ∞` such that, for every point `x` with `|x| ≥ 1`, the passage time
`T(0, x)` is a random variable with `E[exp(|T(0, x) − μ|x|| / (C |x|^{(1−ε)/2}))] ≤ 2`. -/
theorem lintegral_exp_passageTime_le_of_isWhiteNoise {m : ℕ} (hm : 1 ≤ m) {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P)
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ => t⁻¹ * ∫ ω, passageTime (ρ (W ω)) 0 (t • e₁) ∂P) atTop
        (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : Pt m, 1 ≤ ‖x‖ →
        AEMeasurable (fun ω => passageTime (ρ (W ω)) 0 x) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (ρ (W ω)) 0 x - μ * ‖x‖| / (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 :=
  by exact IsotropicVariance.Providers.lintegral_exp_passageTime_le_of_isWhiteNoise hm hW hρ

end IsotropicVariance
