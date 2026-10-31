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
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfig
public import IsotropicVariance.Statements.Curves.PassageTime
public import IsotropicVariance.Statements.Density.ConvolutionDensity
public import IsotropicVariance.Statements.Noise.IsWhiteNoise
public import IsotropicVariance.Statements.Space.EOne
public import IsotropicVariance.Statements.Space.Pt
import IsotropicVariance.Paper.Closing.Main

/-!
# Proof of `IsotropicVariance.variance_passageTime_le`

Proves `IsotropicVariance.Providers.variance_passageTime_le`, with exactly the type of the theorem
`IsotropicVariance.variance_passageTime_le` stated in
`IsotropicVariance.Statements.Main.VariancePassageTimeLe`, by
`IsotropicVariance.Paper.Closing.variance_passageTime_le`. The statement module proves its theorem
from this one and is not imported here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance.Providers

/-- **Variance power saving** (Theorem `thm:main`). Let `d = m + 1 ≥ 2`, let `W` be Gaussian white
noise on a standard Borel probability space, let `χ` be a smooth radial function supported in the
closed unit ball, and let `ψ` be a continuous function with values between two positive constants.
For the density `ρ = ψ(χ∗W)` there is `ε > 0` such that, for every sufficiently large `t`, the
passage time `T(0, t e₁)` is a random variable with `Var T(0, t e₁) ≤ t^{1-ε}`. -/
theorem variance_passageTime_le {m : ℕ} (hm : 1 ≤ m) {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P) (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      AEMeasurable (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 (t • e₁)) P ∧
        evariance (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 (t • e₁)) P ≤
          ENNReal.ofReal (t ^ (1 - ε)) :=
  IsotropicVariance.Paper.Closing.variance_passageTime_le hm hW χ hχ_radial hχ_support ψ hψ a b ha
    hψ_bounds

end IsotropicVariance.Providers
