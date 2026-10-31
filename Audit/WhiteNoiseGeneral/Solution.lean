/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Audit.WhiteNoiseGeneral.SolutionDefs
public import IsotropicVariance.Statements.Companions.ExistsIsWhiteNoise
public import IsotropicVariance.Statements.Main.LintegralExpPassageTimeLeOfIsWhiteNoise
public import IsotropicVariance.Statements.Main.VariancePassageTimeLeOfIsWhiteNoise
public import IsotropicVariance.Statements.Main.VariancePassageTimeLeNormOfIsWhiteNoise
import IsotropicVariance.Infra.Example.LocalDensity

/-!
# General densities, for white noise: the solution

This module proves the five theorems of `Audit.WhiteNoiseGeneral.Challenge` from the library's
`IsotropicVariance.lintegral_exp_passageTime_le_of_isWhiteNoise`,
`IsotropicVariance.variance_passageTime_le_of_isWhiteNoise`,
`IsotropicVariance.variance_passageTime_le_norm_of_isWhiteNoise` (at every point),
`IsotropicVariance.exists_isWhiteNoise` and
`IsotropicVariance.Infra.Example.isLocalDensity_convolutionDensity`. The challenge's definitions
come from `Audit.WhiteNoiseGeneral.SolutionDefs`.

Every definition of the challenge is the library's, in another namespace, so it agrees with the
library's by unfolding, with two exceptions, the new structures:
* `RectifiableCurve`: the bridge is the equivalence `RectifiableCurve.equivLib` with the library's
  curves, which keeps the parametrization and hence the cost (`RectifiableCurve.cost_toLib`). So
  the passage times agree (`passageTime_eq_lib`).
* `IsLocalDensity`: its four fields are the library's, so it converts both ways
  (`IsLocalDensity.toLib`, `IsLocalDensity.ofLib`).

The library's σ-algebra on white-noise configurations is removed from the instances here, so that
the statements elaborate with the challenge's, which is the same σ-algebra.
-/

attribute [-instance] IsotropicVariance.WhiteNoiseConfig.instMeasurableSpace

public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped NNReal ENNReal Distributions

namespace WhiteNoiseGeneral

namespace RectifiableCurve

variable {E : Type*} [PseudoMetricSpace E]

/-- The library's curve with the same parametrization. -/
def toLib (γ : RectifiableCurve E) : IsotropicVariance.RectifiableCurve E :=
  ⟨γ.toFun, γ.continuousOn, γ.boundedVariationOn⟩

/-- The rectifiable curves are the library's. -/
def equivLib : RectifiableCurve E ≃ IsotropicVariance.RectifiableCurve E where
  toFun := toLib
  invFun γ := ⟨γ.toFun, γ.continuousOn, γ.boundedVariationOn⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A curve costs what the library's curve with the same parametrization costs. -/
theorem cost_toLib (ρ : E → ℝ≥0∞) (γ : RectifiableCurve E) : γ.toLib.cost ρ = γ.cost ρ := by
  unfold cost IsotropicVariance.RectifiableCurve.cost arcLengthMeasure
    IsotropicVariance.RectifiableCurve.arcLengthMeasure
  rfl

end RectifiableCurve

/-- The passage time is the library's. -/
theorem passageTime_eq_lib {m : ℕ} (σ : Pt m → ℝ) (u v : Pt m) :
    passageTime σ u v = IsotropicVariance.passageTime σ u v :=
  congrArg ENNReal.toReal (RectifiableCurve.equivLib.iInf_congr fun γ => by
    rw [← RectifiableCurve.cost_toLib]; rfl)

namespace IsLocalDensity

variable {m : ℕ} {N : Type*} [MeasurableSpace N] {agree : Set (Pt m) → N → N → Prop}
  {moved : (Pt m ≃ᵃⁱ[ℝ] Pt m) → N → N → Prop} {ρ : N → Pt m → ℝ}

/-- Assumption `ass:local` is the library's. -/
theorem toLib (h : IsLocalDensity agree moved ρ) : IsotropicVariance.IsLocalDensity agree moved ρ :=
  ⟨h.measurable, h.determined, h.bounds, h.covariant⟩

/-- Assumption `ass:local` is the library's. -/
theorem ofLib (h : IsotropicVariance.IsLocalDensity agree moved ρ) : IsLocalDensity agree moved ρ :=
  ⟨h.measurable, h.determined, h.bounds, h.covariant⟩

end IsLocalDensity

open Filter Topology

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
              (|passageTime (ρ (W ω)) 0 x - μ * ‖x‖| / (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 := by
  simp only [passageTime_eq_lib]
  exact IsotropicVariance.lintegral_exp_passageTime_le_of_isWhiteNoise hm hW hρ.toLib

theorem variance_passageTime_le_of_isWhiteNoise {m : ℕ} (hm : 1 ≤ m) {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P)
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      AEMeasurable (fun ω => passageTime (ρ (W ω)) 0 (t • e₁)) P ∧
        evariance (fun ω => passageTime (ρ (W ω)) 0 (t • e₁)) P ≤
          ENNReal.ofReal (t ^ (1 - ε)) := by
  simp only [passageTime_eq_lib]
  exact IsotropicVariance.variance_passageTime_le_of_isWhiteNoise hm hW hρ.toLib

theorem variance_passageTime_le_norm_of_isWhiteNoise {m : ℕ} (hm : 1 ≤ m) {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P)
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r₀ : ℝ, ∀ x : Pt m, r₀ ≤ ‖x‖ →
      AEMeasurable (fun ω => passageTime (ρ (W ω)) 0 x) P ∧
        evariance (fun ω => passageTime (ρ (W ω)) 0 x) P ≤ ENNReal.ofReal (‖x‖ ^ (1 - ε)) := by
  simp only [passageTime_eq_lib]
  exact IsotropicVariance.variance_passageTime_le_norm_of_isWhiteNoise hm hW hρ.toLib

theorem exists_isWhiteNoise (m : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
      (W : Ω → WhiteNoiseConfig (Pt m)), IsProbabilityMeasure P ∧ IsWhiteNoise W P :=
  IsotropicVariance.exists_isWhiteNoise m

theorem isLocalDensity_convolutionDensity {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy
      (convolutionDensity χ ψ) :=
  IsLocalDensity.ofLib
    (IsotropicVariance.Infra.Example.isLocalDensity_convolutionDensity χ hχ_radial hχ_support ψ hψ
      a b ha hψ_bounds)

end WhiteNoiseGeneral
