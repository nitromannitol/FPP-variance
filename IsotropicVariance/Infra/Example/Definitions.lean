/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Statements.Space.EOne
public import IsotropicVariance.Statements.Space.IsProperRigidMotion
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfigInstMeasurableSpace
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfigAgreeOn
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfigIsMovedBy
public import IsotropicVariance.Statements.Assumption.IsLocalDensity
public import IsotropicVariance.Statements.Density.ConvolutionDensity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Definitions for the convolution-density example

The example uses the declarations `Pt`, `e₁`, `IsProperRigidMotion`,
`WhiteNoiseConfig` with its cylinder σ-algebra `WhiteNoiseConfig.instMeasurableSpace`,
`WhiteNoiseConfig.AgreeOn`, `WhiteNoiseConfig.IsMovedBy`, `IsLocalDensity`,
`TestFunction.reflectTranslate` and `convolutionDensity` of the model
(`IsotropicVariance.Statements`). This file only imports their modules.
-/
