/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Bridge.White
public import IsotropicVariance.Infra.Instances.DistributionCoding
public import IsotropicVariance.Infra.Instances.PoissonRealization

/-!
# The bridge from the main theorems' data to the noise interface

`SettingOfRealizationStatement` holds (`settingOfRealizationStatement_holds`), from:
- white noise: the setting on the canonical carrier (`whiteSetting`), with the standard Borel
  structure of the configurations `Infra.Instances.standardBorel_whiteNoiseConfig`;
- Poisson: `Infra.Instances.exists_poissonSetting_of_realization`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe u

namespace IsotropicVariance.Paper.Proofs.Bridge

/-- **The bridge for white noise.** -/
theorem whiteBridgeStatement_holds : WhiteBridgeStatement.{u} :=
  whiteBridgeStatement_of_standardBorel fun _ => Infra.Instances.standardBorel_whiteNoiseConfig

/-- **The bridge for a Poisson process.** -/
theorem poissonBridgeStatement_holds : PoissonBridgeStatement.{u} := by
  intro m lam _ Ω _ _ P _ η hη ρ hρ
  exact Infra.Instances.exists_poissonSetting_of_realization hη hρ

/-- **The bridge** `SettingOfRealizationStatement`: every realization of the main theorems' data
has a setting of the noise interface whose passage times `T(u, v)` have the same laws. -/
theorem settingOfRealizationStatement_holds : Contracts.SettingOfRealizationStatement.{u} :=
  settingOfRealizationStatement_of whiteBridgeStatement_holds poissonBridgeStatement_holds

end IsotropicVariance.Paper.Proofs.Bridge
