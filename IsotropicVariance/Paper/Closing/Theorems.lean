/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Induction
public import IsotropicVariance.Paper.Contracts.Classical
public import IsotropicVariance.Infra.Example.LocalDensity
public import IsotropicVariance.Paper.Proofs.Induction.Tools
import IsotropicVariance.Paper.Proofs.Profiles.Basic

/-!
# Theorems `thm:general` and `thm:main` from the statements over the noise interface

**Theorem `thm:general`.**
- Every choice of the data of the main theorems (a noise on a standard Borel space and a density
  satisfying `IsLocalDensity`) is a `Realization` (`whiteNoiseRealization`,
  `poissonRealization`).
- The bridge `SettingOfRealizationStatement` gives a `Setting` whose passage times `T(u, v)` have
  the same laws.
- `MainSettingStatement` bounds their variances, and the variance of a random variable depends only
  on its law (`Proofs.Induction.evariance_eq_of_map_eq`).
- This gives `realization_variance_le`, and for Gaussian white noise
  `variance_passageTime_le_of_isWhiteNoise_of`, with exactly the binders and conclusion of the
  main theorem `IsotropicVariance.variance_passageTime_le_of_isWhiteNoise`.

**Theorem `thm:main`.** By the example (`Infra.Example.isLocalDensity_convolutionDensity`),
`ψ(χ∗W)` satisfies Assumption `ass:local`, so the white-noise case applies
(`variance_passageTime_le_of`).

**Every point.** By isotropy (`Proofs.Profiles.map_passTime_eq_map_TRV`), `T(0, x)` has the law
of `T_{|x|}` in the setting, so the same `ε` bounds `Var T(0, x)` by `|x|^{1-ε}` for `|x|`
sufficiently large (`realization_variance_le_norm`,
`variance_passageTime_le_norm_of_isWhiteNoise_of`, `variance_passageTime_le_norm_of`).

**The exponential moments.** The conclusion of Theorems `thm:main` and `thm:general` themselves
transfers in the same way from `MainSettingExpStatement`. The mean of `T(0, t e₁)` depends only on
its law (`Proofs.Induction.integral_eq_of_map_eq`), so the realization has the time constant `μ`
of the setting. The exponential moment of `|T(0, x) − μ|x||` depends only on the law of
`T(0, x)` (`Proofs.Induction.lintegral_comp_eq_of_map_eq`), which by isotropy is that of
`T_{|x|}` (`realization_lintegral_exp_le`, `lintegral_exp_passageTime_le_of_isWhiteNoise_of`,
`lintegral_exp_passageTime_le_of`).

`IsotropicVariance.Paper.Closing.Main` applies these theorems to the bridge
(`Proofs.Bridge.settingOfRealizationStatement_holds`) and to `MainSettingStatement` and
`MainSettingExpStatement`, and proves the Poisson case in the same way.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

universe u

namespace IsotropicVariance.Paper.Closing

/-- The data of the main theorems for Gaussian white noise, as a realization. -/
noncomputable def whiteNoiseRealization {m : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P)
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    Realization.{u} m where
  noise := .white
  Ω := Ω
  P := P
  config := W
  isLaw := hW
  ρ := ρ
  isLocalDensity := hρ

/-- The data of the main theorems for a homogeneous Poisson process, as a realization. -/
noncomputable def poissonRealization {m : ℕ} {lam : ℝ≥0} (hlam : 0 < lam) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {η : Ω → Measure (Pt m)} (hη : IsPoissonProcess lam η P) {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) :
    Realization.{u} m where
  noise := .poisson lam
  Ω := Ω
  P := P
  config := η
  isLaw := ⟨hlam, hη⟩
  ρ := ρ
  isLocalDensity := hρ

/-- **The variance bound transfers from the setting to the realization.** -/
theorem realization_variance_le (hS : Contracts.SettingOfRealizationStatement.{u})
    (hM : Contracts.MainSettingStatement.{0}) {m : ℕ} (hm : 1 ≤ m) (R : Realization.{u} m) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      AEMeasurable (R.TRV t) R.P ∧ evariance (R.TRV t) R.P ≤ ENNReal.ofReal (t ^ (1 - ε)) := by
  obtain ⟨S, hRS⟩ := hS m R
  obtain ⟨ε, hε, t₀, hb⟩ := hM m hm S
  refine ⟨ε, hε, t₀, fun t ht => ⟨(hRS 0 (t • e₁)).1, ?_⟩⟩
  exact (Proofs.Induction.evariance_eq_of_map_eq (hRS 0 (t • e₁)).1 (hRS 0 (t • e₁)).2.1
    (hRS 0 (t • e₁)).2.2).le.trans (hb t ht).2

/-- **The variance bound at every point**: by stationarity and isotropy (part (3) of Assumption
`ass:local`), `T(0, x)` has the law of `T_{|x|}`, so the exponent `ε` of the setting bounds
`Var T(0, x)` by `|x|^{1-ε}` for `|x|` sufficiently large. -/
theorem realization_variance_le_norm (hS : Contracts.SettingOfRealizationStatement.{u})
    (hM : Contracts.MainSettingStatement.{0}) {m : ℕ} (hm : 1 ≤ m) (R : Realization.{u} m) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r₀ : ℝ, ∀ x : Pt m, r₀ ≤ ‖x‖ →
      AEMeasurable (fun ω => passageTime (R.ρ (R.config ω)) 0 x) R.P ∧
        evariance (fun ω => passageTime (R.ρ (R.config ω)) 0 x) R.P ≤
          ENNReal.ofReal (‖x‖ ^ (1 - ε)) := by
  obtain ⟨S, hRS⟩ := hS m R
  obtain ⟨ε, hε, t₀, hb⟩ := hM m hm S
  refine ⟨ε, hε, t₀, fun x hx => ⟨(hRS 0 x).1, ?_⟩⟩
  have hlaw := Proofs.Profiles.map_passTime_eq_map_TRV (X := S) hm 0 x
  rw [dist_zero_left] at hlaw
  calc evariance (fun ω => passageTime (R.ρ (R.config ω)) 0 x) R.P
      = evariance (fun ω => S.passTime ω 0 x) S.P :=
        Proofs.Induction.evariance_eq_of_map_eq (hRS 0 x).1 (hRS 0 x).2.1 (hRS 0 x).2.2
    _ = evariance (S.TRV ‖x‖) S.P :=
        Proofs.Induction.evariance_eq_of_map_eq (hRS 0 x).2.1 (hb ‖x‖ hx).1 hlaw
    _ ≤ ENNReal.ofReal (‖x‖ ^ (1 - ε)) := (hb ‖x‖ hx).2

/-- **Theorem `thm:general` for Gaussian white noise**, with the binders and conclusion of the
theorem `IsotropicVariance.variance_passageTime_le_of_isWhiteNoise`, from the bridge and
Theorem `thm:general` over the noise interface. -/
theorem variance_passageTime_le_of_isWhiteNoise_of
    (hS : Contracts.SettingOfRealizationStatement.{u}) (hM : Contracts.MainSettingStatement.{0})
    {m : ℕ} (hm : 1 ≤ m) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : Ω → WhiteNoiseConfig (Pt m)}
    (hW : IsWhiteNoise W P) {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      AEMeasurable (fun ω => passageTime (ρ (W ω)) 0 (t • e₁)) P ∧
        evariance (fun ω => passageTime (ρ (W ω)) 0 (t • e₁)) P ≤
          ENNReal.ofReal (t ^ (1 - ε)) :=
  realization_variance_le hS hM hm (whiteNoiseRealization hW hρ)

/-- **Theorem `thm:main`**, with the binders and conclusion of the main theorem
`IsotropicVariance.variance_passageTime_le`: the convolution density `ψ(χ∗W)` satisfies
Assumption `ass:local` (`Infra.Example`), so the white-noise case of Theorem `thm:general`
applies. -/
theorem variance_passageTime_le_of
    (hS : Contracts.SettingOfRealizationStatement.{u}) (hM : Contracts.MainSettingStatement.{0})
    {m : ℕ} (hm : 1 ≤ m) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P) (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      AEMeasurable (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 (t • e₁)) P ∧
        evariance (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 (t • e₁)) P ≤
          ENNReal.ofReal (t ^ (1 - ε)) :=
  variance_passageTime_le_of_isWhiteNoise_of hS hM hm hW
    (Infra.Example.isLocalDensity_convolutionDensity χ hχ_radial hχ_support ψ hψ a b ha hψ_bounds)

/-- **Theorem `thm:general` for Gaussian white noise, at every point**, with the binders and
conclusion of the main theorem `IsotropicVariance.variance_passageTime_le_norm_of_isWhiteNoise`. -/
theorem variance_passageTime_le_norm_of_isWhiteNoise_of
    (hS : Contracts.SettingOfRealizationStatement.{u}) (hM : Contracts.MainSettingStatement.{0})
    {m : ℕ} (hm : 1 ≤ m) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : Ω → WhiteNoiseConfig (Pt m)}
    (hW : IsWhiteNoise W P) {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r₀ : ℝ, ∀ x : Pt m, r₀ ≤ ‖x‖ →
      AEMeasurable (fun ω => passageTime (ρ (W ω)) 0 x) P ∧
        evariance (fun ω => passageTime (ρ (W ω)) 0 x) P ≤ ENNReal.ofReal (‖x‖ ^ (1 - ε)) :=
  realization_variance_le_norm hS hM hm (whiteNoiseRealization hW hρ)

/-- **Theorem `thm:main` at every point**, with the binders and conclusion of the main theorem
`IsotropicVariance.variance_passageTime_le_norm`. -/
theorem variance_passageTime_le_norm_of
    (hS : Contracts.SettingOfRealizationStatement.{u}) (hM : Contracts.MainSettingStatement.{0})
    {m : ℕ} (hm : 1 ≤ m) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P) (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r₀ : ℝ, ∀ x : Pt m, r₀ ≤ ‖x‖ →
      AEMeasurable (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 x) P ∧
        evariance (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 x) P ≤
          ENNReal.ofReal (‖x‖ ^ (1 - ε)) :=
  variance_passageTime_le_norm_of_isWhiteNoise_of hS hM hm hW
    (Infra.Example.isLocalDensity_convolutionDensity χ hχ_radial hχ_support ψ hψ a b ha hψ_bounds)

/-- **The exponential moment transfers from the setting to the realization, at every point.**
The realization has the time constant `μ` of the setting, and by isotropy (part (3) of Assumption
`ass:local`) `T(0, x)` has the law of `T_{|x|}`, so the constants `ε` and `C` of the setting bound
`E[exp(|T(0, x) − μ|x|| / (C |x|^{(1−ε)/2}))]` by `2` for every `|x| ≥ 1`. -/
theorem realization_lintegral_exp_le (hS : Contracts.SettingOfRealizationStatement.{u})
    (hM : Contracts.MainSettingExpStatement.{0}) {m : ℕ} (hm : 1 ≤ m) (R : Realization.{u} m) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ => t⁻¹ * ∫ ω, R.TRV t ω ∂R.P) atTop (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : Pt m, 1 ≤ ‖x‖ →
        AEMeasurable (fun ω => passageTime (R.ρ (R.config ω)) 0 x) R.P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (R.ρ (R.config ω)) 0 x - μ * ‖x‖| / (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂R.P ≤
            2 := by
  obtain ⟨S, hRS⟩ := hS m R
  obtain ⟨μ, hμ, ε, hε, C, hC, hb⟩ := hM m hm S
  refine ⟨μ, hμ.congr fun t => ?_, ε, hε, C, hC, fun x hx => ⟨(hRS 0 x).1, ?_⟩⟩
  · rw [div_eq_inv_mul]
    exact congrArg (t⁻¹ * ·) (Proofs.Induction.integral_eq_of_map_eq (hRS 0 (t • e₁)).2.1
      (hRS 0 (t • e₁)).1 (hRS 0 (t • e₁)).2.2.symm)
  · set θ := C * ‖x‖ ^ ((1 - ε) / 2)
    have hF : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (|y - μ * ‖x‖| / θ)) := by
      fun_prop
    have hlaw := Proofs.Profiles.map_passTime_eq_map_TRV (X := S) hm 0 x
    rw [dist_zero_left] at hlaw
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (|passageTime (R.ρ (R.config ω)) 0 x - μ * ‖x‖| / θ)) ∂R.P
        = ∫⁻ ω, ENNReal.ofReal (Real.exp (|S.passTime ω 0 x - μ * ‖x‖| / θ)) ∂S.P :=
          Proofs.Induction.lintegral_comp_eq_of_map_eq (hRS 0 x).1 (hRS 0 x).2.1 (hRS 0 x).2.2 hF
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (|S.TRV ‖x‖ ω - μ * ‖x‖| / θ)) ∂S.P :=
          Proofs.Induction.lintegral_comp_eq_of_map_eq (hRS 0 x).2.1
            (Infra.TimeConstant.integrable_TRV S ‖x‖).aemeasurable hlaw hF
      _ ≤ 2 := by
          refine le_of_eq_of_le (lintegral_congr fun ω => ?_) (hb ‖x‖ hx).2
          rw [max_eq_left (abs_nonneg _), Real.rpow_one]

/-- **Theorem `thm:general` for Gaussian white noise**, with the binders and conclusion of the
theorem `IsotropicVariance.lintegral_exp_passageTime_le_of_isWhiteNoise`, from the bridge and
Theorem `thm:general` over the noise interface. -/
theorem lintegral_exp_passageTime_le_of_isWhiteNoise_of
    (hS : Contracts.SettingOfRealizationStatement.{u})
    (hM : Contracts.MainSettingExpStatement.{0}) {m : ℕ} (hm : 1 ≤ m) {Ω : Type u}
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
  realization_lintegral_exp_le hS hM hm (whiteNoiseRealization hW hρ)

/-- **Theorem `thm:main`**, with the binders and conclusion of the main theorem
`IsotropicVariance.lintegral_exp_passageTime_le`: the convolution density `ψ(χ∗W)` satisfies
Assumption `ass:local` (`Infra.Example`), so the white-noise case of Theorem `thm:general`
applies. -/
theorem lintegral_exp_passageTime_le_of
    (hS : Contracts.SettingOfRealizationStatement.{u})
    (hM : Contracts.MainSettingExpStatement.{0}) {m : ℕ} (hm : 1 ≤ m) {Ω : Type u}
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
  lintegral_exp_passageTime_le_of_isWhiteNoise_of hS hM hm hW
    (Infra.Example.isLocalDensity_convolutionDensity χ hχ_radial hχ_support ψ hψ a b ha hψ_bounds)

end IsotropicVariance.Paper.Closing
