/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Classical

/-!
# The bridge from the main theorems' data to the noise interface, noise by noise

The statement `Contracts.SettingOfRealizationStatement` asks, for every realization of the main
theorems' data, for a `Setting` whose passage times `T(u, v)` have the same laws.
It splits by noise into two internal statements:
- `WhiteBridgeStatement`: from a white noise `W` and a density `ρ` satisfying `IsLocalDensity`;
- `PoissonBridgeStatement`: the same from a Poisson process `η` of intensity `lam > 0`.

`settingOfRealizationStatement_of` assembles the contract from them.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

universe u

namespace IsotropicVariance.Paper.Proofs.Bridge

/-- **The bridge for white noise**: a `Setting` whose passage times have the laws of
`T(u, v) = passageTime (ρ (W ·)) u v`. -/
def WhiteBridgeStatement : Prop :=
  ∀ (m : ℕ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : Ω → WhiteNoiseConfig (Pt m)), IsWhiteNoise W P →
    ∀ ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ,
      IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ →
      ∃ S : Setting.{0} m, ∀ u v : Pt m,
        AEMeasurable (fun ω => passageTime (ρ (W ω)) u v) P ∧
          AEMeasurable (fun ω => S.passTime ω u v) S.P ∧
            P.map (fun ω => passageTime (ρ (W ω)) u v) = S.P.map (fun ω => S.passTime ω u v)

/-- **The bridge for a Poisson process** of positive intensity. -/
def PoissonBridgeStatement : Prop :=
  ∀ (m : ℕ) (lam : ℝ≥0), 0 < lam → ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (η : Ω → Measure (Pt m)),
    IsPoissonProcess lam η P →
    ∀ ρ : Measure (Pt m) → Pt m → ℝ,
      IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ →
      ∃ S : Setting.{0} m, ∀ u v : Pt m,
        AEMeasurable (fun ω => passageTime (ρ (η ω)) u v) P ∧
          AEMeasurable (fun ω => S.passTime ω u v) S.P ∧
            P.map (fun ω => passageTime (ρ (η ω)) u v) = S.P.map (fun ω => S.passTime ω u v)

/-- **The bridge** from the two noises. -/
theorem settingOfRealizationStatement_of (hW : WhiteBridgeStatement.{u})
    (hP : PoissonBridgeStatement.{u}) : Contracts.SettingOfRealizationStatement.{u} := by
  intro m X
  rcases X with ⟨noise, Ω, P, config, isLaw, ρ, hρ⟩
  cases noise with
  | white => exact hW m P config isLaw ρ hρ
  | poisson lam => exact hP m lam isLaw.1 P config isLaw.2 ρ hρ

end IsotropicVariance.Paper.Proofs.Bridge
