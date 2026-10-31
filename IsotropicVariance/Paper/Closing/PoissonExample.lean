/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Statements.Main.LintegralExpPassageTimeLeOfIsPoissonProcess
public import IsotropicVariance.Infra.Example.PoissonDensity

/-!
# The Poisson convolution example

The sentence after Theorem `thm:general`: `ψ(χ∗ω)` satisfies Assumption `ass:local` also when `ω`
is a Poisson process, so Theorem `thm:general` applies to it. This file is not on the path of the
main theorems.
-/

public section

open MeasureTheory Filter TopologicalSpace
open scoped NNReal Topology Distributions

namespace IsotropicVariance.Paper.Closing

open Infra.Example in
/-- **Theorem `thm:general` for the density `ψ(χ∗η)` of a homogeneous Poisson process**, with the
hypotheses on `χ` and `ψ` of the main theorem `IsotropicVariance.lintegral_exp_passageTime_le`:
the density satisfies Assumption `ass:local` (`Infra.Example`), so
`IsotropicVariance.lintegral_exp_passageTime_le_of_isPoissonProcess` applies. -/
theorem lintegral_exp_passageTime_le_of_isPoissonProcess_convolution {m : ℕ} (hm : 1 ≤ m)
    {lam : ℝ≥0} (hlam : 0 < lam) {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {η : Ω → Measure (Pt m)}
    (hη : IsPoissonProcess lam η P) (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ =>
        t⁻¹ * ∫ ω, passageTime (poissonConvolutionDensity χ ψ (η ω)) 0 (t • e₁) ∂P) atTop (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : Pt m, 1 ≤ ‖x‖ →
        AEMeasurable (fun ω => passageTime (poissonConvolutionDensity χ ψ (η ω)) 0 x) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (poissonConvolutionDensity χ ψ (η ω)) 0 x - μ * ‖x‖| /
                (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 :=
  IsotropicVariance.lintegral_exp_passageTime_le_of_isPoissonProcess hm hlam hη
    (isLocalDensity_poissonConvolutionDensity χ hχ_radial hχ_support ψ hψ a b ha hψ_bounds)

end IsotropicVariance.Paper.Closing
