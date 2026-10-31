/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Closing.Theorems
public import IsotropicVariance.Paper.Proofs.Induction.Main
public import IsotropicVariance.Paper.Proofs.Induction.Step
public import IsotropicVariance.Paper.Proofs.SmallMean.Direct
public import IsotropicVariance.Paper.Contracts.Blocks
public import IsotropicVariance.Paper.Contracts.Gain
public import IsotropicVariance.Paper.Contracts.Induction
public import IsotropicVariance.Paper.Contracts.Localization
public import IsotropicVariance.Paper.Contracts.Profiles
public import IsotropicVariance.Paper.Contracts.Slab
import IsotropicVariance.Paper.Proofs.Blocks.BlockReplacement
import IsotropicVariance.Paper.Proofs.Blocks.BlockSum
import IsotropicVariance.Paper.Proofs.Blocks.RadiusEnergy
import IsotropicVariance.Paper.Proofs.Blocks.RewardMoment
import IsotropicVariance.Paper.Proofs.Bridge.Main
import IsotropicVariance.Paper.Proofs.Classical.Final
import IsotropicVariance.Paper.Proofs.Gain.FewTranslatesBound
import IsotropicVariance.Paper.Proofs.Gain.Main
import IsotropicVariance.Paper.Proofs.Labels.Main
import IsotropicVariance.Paper.Proofs.Localization.Main
import IsotropicVariance.Paper.Proofs.Modified
import IsotropicVariance.Paper.Proofs.Modulus.ModulusFinal
import IsotropicVariance.Paper.Proofs.Profiles.ChainSum
import IsotropicVariance.Paper.Proofs.Profiles.Parent
import IsotropicVariance.Paper.Proofs.Profiles.ProfilesFull
import IsotropicVariance.Paper.Proofs.Profiles.ProfilesShort
import IsotropicVariance.Paper.Proofs.Profiles.RowEnergyMoves
import IsotropicVariance.Paper.Proofs.Profiles.TreeBound
import IsotropicVariance.Paper.Proofs.Residual.Main
import IsotropicVariance.Paper.Proofs.SlabComparison.Slab
import IsotropicVariance.Paper.Proofs.Straight.Statement

/-!
# The main theorems

Every intermediate statement of the paper is proved, so the implications of
`Paper.Closing.Theorems` hold outright. The statements are composed here in the order of the paper:

* Section `sec:prelim`: `Proofs.Classical.classicalBoundsStatement_holds` (`lem:classical`),
  `straightStatement_holds` (`lem:straight`), `slabStatement_holds` (`lem:slab`), and the penalized
  arrays `Contracts.penalizedArraysStatement_holds` (`lem:polynomialarray`).
* Section `sec:exponential`: `Proofs.Profiles.treeStatement_holds` (`lem:tree`), then
  `profilesShortStatement_holds` (`prop:profiles` for `s ≤ N/4`), `rowEnergyStatement_holds`
  (`lem:rowenergy`), `chainSumStatement_holds` (`eq:chainsum`), `parentStatement_holds`
  (`lem:parent`) and `profilesStatement_holds` (`prop:profiles`), in the order that breaks the cycle
  between them.
* Section `sec:localization`: `localizationStatement_holds` (`lem:localization`) and
  `modulusStatement_holds` (`lem:modulus`).
* Section `sec:gain`: `Proofs.Blocks.blockSumStatement_holds` (`eq:blocksum`),
  `radiusEnergyStatement_holds`, `rewardMomentStatement_holds` and
  `blockReplacementStatement_holds` (`lem:blocks`), `fewTranslatesStatement_holds`
  (`lem:fewtranslates`), `labelsStatement_holds` (`lem:labels`), `residualStatement_holds`
  (`lem:residual`), and from them, with `Proofs.Modified.modifiedPoincareStatement_holds`
  (`prop:BR`), `gainStatement_holds` (`prop:gain`).
* Section `sec:completion`: `smallMeanStatement_holds` (`lem:smallmean`).
* `mainSettingExpStatement_holds` and `mainSettingStatement_holds`: the exponential moments and
  the variance bound for every setting, from the classical bounds, the parent lemma, the
  logarithmic gain and the small mean, by the improvement and the induction
  (`Proofs.Induction.mainSettingStatement_of_contracts`,
  `Proofs.Induction.mainSettingExpStatement_of_contracts`).
* `lintegral_exp_passageTime_le_of_isWhiteNoise`,
  `lintegral_exp_passageTime_le_of_isPoissonProcess` and `lintegral_exp_passageTime_le`: the
  theorem on local densities (`thm:general`) for Gaussian white noise and for a homogeneous
  Poisson process, and the main theorem (`thm:main`).
* `variance_passageTime_le_of_isWhiteNoise`, `variance_passageTime_le_of_isPoissonProcess` and
  `variance_passageTime_le`: the variance bound that the paper derives after Theorem `thm:main`,
  at the points `t e₁` with `t` sufficiently large.
* `variance_passageTime_le_norm_of_isWhiteNoise`, `variance_passageTime_le_norm_of_isPoissonProcess`
  and `variance_passageTime_le_norm`: the same variance bound at every point `x` with `|x|`
  sufficiently large, by isotropy.

The last nine have exactly the binders and conclusions of the theorems stated in
`IsotropicVariance.Statements.Main`, which `IsotropicVariance.Providers` proves from them.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

universe u

namespace IsotropicVariance.Paper.Closing

/-- The near-geodesics are straight (`lem:straight`), from the classical bounds
(`lem:classical`). -/
theorem straightStatement_holds : Contracts.StraightStatement.{u} :=
  Proofs.Straight.straightStatement_of Proofs.Classical.classicalBoundsStatement_holds

/-- The slab comparison (`lem:slab`). -/
theorem slabStatement_holds : Contracts.SlabStatement.{u} :=
  Proofs.SlabComparison.slabStatement_of straightStatement_holds

/-- Proposition `prop:profiles` for `s ≤ N/4`. -/
theorem profilesShortStatement_holds : Contracts.ProfilesShortStatement.{u} :=
  Proofs.Profiles.profilesShortStatement_of Proofs.Profiles.treeStatement_holds slabStatement_holds

/-- The energy of the rows (`lem:rowenergy`). -/
theorem rowEnergyStatement_holds : Contracts.RowEnergyStatement.{u} :=
  Proofs.Profiles.rowEnergyStatement_of profilesShortStatement_holds

/-- The sum of independent arrays along the chain (equation `eq:chainsum`). -/
theorem chainSumStatement_holds : Contracts.ChainSumStatement.{u} :=
  Proofs.Profiles.chainSumStatement_of rowEnergyStatement_holds
    Contracts.penalizedArraysStatement_holds

/-- The parent lemma (`lem:parent`). -/
theorem parentStatement_holds : Contracts.ParentStatement.{u} :=
  Proofs.Profiles.parentStatement_of rowEnergyStatement_holds slabStatement_holds

/-- The passage times between transverse cubes (`prop:profiles`). -/
theorem profilesStatement_holds : Contracts.ProfilesStatement.{u} :=
  Proofs.Profiles.profilesStatement_of Proofs.Profiles.treeStatement_holds slabStatement_holds
    profilesShortStatement_holds parentStatement_holds

/-- The localization of nearly minimizing curves (`lem:localization`). -/
theorem localizationStatement_holds : Contracts.LocalizationStatement.{u} :=
  Proofs.Localization.localizationStatement_of Proofs.Profiles.treeStatement_holds
    profilesStatement_holds parentStatement_holds

/-- The modulus of continuity (`lem:modulus`). -/
theorem modulusStatement_holds : Contracts.ModulusStatement.{u} :=
  Proofs.Modulus.modulusStatement_of profilesStatement_holds localizationStatement_holds

/-- The energy of the radii (`lem:blocks`, equation `eq:radiusenergy`). -/
theorem radiusEnergyStatement_holds : Contracts.RadiusEnergyStatement.{u} :=
  Proofs.Blocks.radiusEnergyStatement_of localizationStatement_holds chainSumStatement_holds

/-- The moments of the rewards (`lem:blocks`, first bound of equation `eq:rewardmoment`). -/
theorem rewardMomentStatement_holds : Contracts.RewardMomentStatement.{u} :=
  Proofs.Blocks.rewardMomentStatement_of profilesStatement_holds localizationStatement_holds

/-- The replacement of a block (`lem:blocks`, second bound of equation `eq:rewardmoment`). -/
theorem blockReplacementStatement_holds : Contracts.BlockReplacementStatement.{u} :=
  Proofs.Blocks.blockReplacementStatement_of Proofs.Blocks.blockSumStatement_holds
    rewardMomentStatement_holds chainSumStatement_holds

/-- The few translates (`lem:fewtranslates`). -/
theorem fewTranslatesStatement_holds : Contracts.FewTranslatesStatement.{u} :=
  Proofs.Gain.fewTranslatesStatement_of rowEnergyStatement_holds radiusEnergyStatement_holds
    blockReplacementStatement_holds

/-- The small mean (`lem:smallmean`). -/
theorem smallMeanStatement_holds : Contracts.SmallMeanStatement.{u} :=
  Proofs.SmallMean.smallMeanStatement_of_contracts Proofs.Classical.classicalBoundsStatement_holds
    slabStatement_holds profilesStatement_holds chainSumStatement_holds modulusStatement_holds

/-- The labels of the blocks (`lem:labels`). -/
theorem labelsStatement_holds : Contracts.LabelsStatement.{u} :=
  Proofs.Labels.labelsStatement_of localizationStatement_holds modulusStatement_holds
    profilesStatement_holds

/-- The residual (`lem:residual`). -/
theorem residualStatement_holds : Contracts.ResidualStatement.{u} :=
  Proofs.Residual.residualStatement_of rewardMomentStatement_holds
    Proofs.Blocks.blockSumStatement_holds chainSumStatement_holds localizationStatement_holds

/-- The logarithmic gain (`prop:gain`). -/
theorem gainStatement_holds : Contracts.GainStatement.{u} :=
  Proofs.Gain.gainStatement_of_contracts labelsStatement_holds residualStatement_holds
    fewTranslatesStatement_holds Proofs.Modified.modifiedPoincareStatement_holds.{0, 0}
    modulusStatement_holds slabStatement_holds

/-- The variance bound for every setting. -/
theorem mainSettingStatement_holds : Contracts.MainSettingStatement.{u} :=
  Proofs.Induction.mainSettingStatement_of_contracts Proofs.Classical.classicalBoundsStatement_holds
    parentStatement_holds gainStatement_holds smallMeanStatement_holds

/-- The exponential moments for every setting: Theorem `thm:general` over the noise interface,
with its conclusion. -/
theorem mainSettingExpStatement_holds : Contracts.MainSettingExpStatement.{u} :=
  Proofs.Induction.mainSettingExpStatement_of_contracts
    Proofs.Classical.classicalBoundsStatement_holds parentStatement_holds gainStatement_holds
    smallMeanStatement_holds

/-- The theorem on local densities (`thm:general`) for Gaussian white noise. -/
theorem variance_passageTime_le_of_isWhiteNoise {m : ℕ} (hm : 1 ≤ m) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P)
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      AEMeasurable (fun ω => passageTime (ρ (W ω)) 0 (t • e₁)) P ∧
        evariance (fun ω => passageTime (ρ (W ω)) 0 (t • e₁)) P ≤
          ENNReal.ofReal (t ^ (1 - ε)) :=
  variance_passageTime_le_of_isWhiteNoise_of Proofs.Bridge.settingOfRealizationStatement_holds
    mainSettingStatement_holds.{0} hm hW hρ

/-- The theorem on local densities (`thm:general`) for a homogeneous Poisson process. -/
theorem variance_passageTime_le_of_isPoissonProcess {m : ℕ} (hm : 1 ≤ m) {lam : ℝ≥0}
    (hlam : 0 < lam) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {η : Ω → Measure (Pt m)} (hη : IsPoissonProcess lam η P)
    {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      AEMeasurable (fun ω => passageTime (ρ (η ω)) 0 (t • e₁)) P ∧
        evariance (fun ω => passageTime (ρ (η ω)) 0 (t • e₁)) P ≤
          ENNReal.ofReal (t ^ (1 - ε)) := by
  obtain ⟨S, hRS⟩ := Infra.Instances.settingOfRealizationStatement_poisson
    (poissonRealization hlam hη hρ) rfl
  obtain ⟨ε, hε, t₀, hb⟩ := mainSettingStatement_holds.{0} m hm S
  refine ⟨ε, hε, t₀, fun t ht => ⟨(hRS 0 (t • e₁)).1, ?_⟩⟩
  exact (Proofs.Induction.evariance_eq_of_map_eq (hRS 0 (t • e₁)).1 (hRS 0 (t • e₁)).2.1
    (hRS 0 (t • e₁)).2.2).le.trans (hb t ht).2

/-- The main theorem (`thm:main`): the variance power saving for the density `ψ(χ ∗ W)`. -/
theorem variance_passageTime_le {m : ℕ} (hm : 1 ≤ m) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P) (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      AEMeasurable (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 (t • e₁)) P ∧
        evariance (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 (t • e₁)) P ≤
          ENNReal.ofReal (t ^ (1 - ε)) :=
  variance_passageTime_le_of Proofs.Bridge.settingOfRealizationStatement_holds
    mainSettingStatement_holds.{0} hm hW χ hχ_radial hχ_support ψ hψ a b ha hψ_bounds

/-- The theorem on local densities (`thm:general`) for Gaussian white noise, at every point. -/
theorem variance_passageTime_le_norm_of_isWhiteNoise {m : ℕ} (hm : 1 ≤ m) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P)
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r₀ : ℝ, ∀ x : Pt m, r₀ ≤ ‖x‖ →
      AEMeasurable (fun ω => passageTime (ρ (W ω)) 0 x) P ∧
        evariance (fun ω => passageTime (ρ (W ω)) 0 x) P ≤ ENNReal.ofReal (‖x‖ ^ (1 - ε)) :=
  variance_passageTime_le_norm_of_isWhiteNoise_of
    Proofs.Bridge.settingOfRealizationStatement_holds mainSettingStatement_holds.{0} hm hW hρ

/-- The theorem on local densities (`thm:general`) for a homogeneous Poisson process, at every
point. -/
theorem variance_passageTime_le_norm_of_isPoissonProcess {m : ℕ} (hm : 1 ≤ m) {lam : ℝ≥0}
    (hlam : 0 < lam) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {η : Ω → Measure (Pt m)} (hη : IsPoissonProcess lam η P)
    {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r₀ : ℝ, ∀ x : Pt m, r₀ ≤ ‖x‖ →
      AEMeasurable (fun ω => passageTime (ρ (η ω)) 0 x) P ∧
        evariance (fun ω => passageTime (ρ (η ω)) 0 x) P ≤ ENNReal.ofReal (‖x‖ ^ (1 - ε)) :=
  realization_variance_le_norm Proofs.Bridge.settingOfRealizationStatement_holds
    mainSettingStatement_holds.{0} hm (poissonRealization hlam hη hρ)

/-- The main theorem (`thm:main`) at every point: the variance power saving for the density
`ψ(χ ∗ W)`. -/
theorem variance_passageTime_le_norm {m : ℕ} (hm : 1 ≤ m) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P) (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r₀ : ℝ, ∀ x : Pt m, r₀ ≤ ‖x‖ →
      AEMeasurable (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 x) P ∧
        evariance (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 x) P ≤
          ENNReal.ofReal (‖x‖ ^ (1 - ε)) :=
  variance_passageTime_le_norm_of Proofs.Bridge.settingOfRealizationStatement_holds
    mainSettingStatement_holds.{0} hm hW χ hχ_radial hχ_support ψ hψ a b ha hψ_bounds

/-- The theorem on local densities (`thm:general`) for Gaussian white noise: the exponential
moments of `|T(0, x) − μ|x||`. -/
theorem lintegral_exp_passageTime_le_of_isWhiteNoise {m : ℕ} (hm : 1 ≤ m) {Ω : Type u}
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
  lintegral_exp_passageTime_le_of_isWhiteNoise_of
    Proofs.Bridge.settingOfRealizationStatement_holds mainSettingExpStatement_holds.{0} hm hW hρ

/-- The theorem on local densities (`thm:general`) for a homogeneous Poisson process: the
exponential moments of `|T(0, x) − μ|x||`. -/
theorem lintegral_exp_passageTime_le_of_isPoissonProcess {m : ℕ} (hm : 1 ≤ m) {lam : ℝ≥0}
    (hlam : 0 < lam) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {η : Ω → Measure (Pt m)} (hη : IsPoissonProcess lam η P)
    {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ => t⁻¹ * ∫ ω, passageTime (ρ (η ω)) 0 (t • e₁) ∂P) atTop
        (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : Pt m, 1 ≤ ‖x‖ →
        AEMeasurable (fun ω => passageTime (ρ (η ω)) 0 x) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (ρ (η ω)) 0 x - μ * ‖x‖| / (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 :=
  realization_lintegral_exp_le Proofs.Bridge.settingOfRealizationStatement_holds
    mainSettingExpStatement_holds.{0} hm (poissonRealization hlam hη hρ)

/-- The main theorem (`thm:main`): the exponential moments of `|T(0, x) − μ|x||` for the density
`ψ(χ ∗ W)`. -/
theorem lintegral_exp_passageTime_le {m : ℕ} (hm : 1 ≤ m) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P) (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ =>
        t⁻¹ * ∫ ω, passageTime (convolutionDensity χ ψ (W ω)) 0 (t • e₁) ∂P) atTop (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : Pt m, 1 ≤ ‖x‖ →
        AEMeasurable (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 x) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (convolutionDensity χ ψ (W ω)) 0 x - μ * ‖x‖| /
                (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 :=
  lintegral_exp_passageTime_le_of Proofs.Bridge.settingOfRealizationStatement_holds
    mainSettingExpStatement_holds.{0} hm hW χ hχ_radial hχ_support ψ hψ a b ha hψ_bounds

end IsotropicVariance.Paper.Closing
