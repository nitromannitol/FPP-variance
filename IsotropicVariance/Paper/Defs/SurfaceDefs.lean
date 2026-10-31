/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Statements.Space.Pt
public import IsotropicVariance.Statements.Space.EOne
public import IsotropicVariance.Statements.Space.IsProperRigidMotion
public import IsotropicVariance.Statements.Curves.RectifiableCurve
public import IsotropicVariance.Statements.Curves.RectifiableCurveLength
public import IsotropicVariance.Statements.Curves.RectifiableCurveCumulativeLength
public import IsotropicVariance.Statements.Curves.RectifiableCurveContinuousCumulativeLength
public import IsotropicVariance.Statements.Curves.RectifiableCurveMonotoneCumulativeLength
public import IsotropicVariance.Statements.Curves.RectifiableCurveLengthFunction
public import IsotropicVariance.Statements.Curves.RectifiableCurveArcLengthMeasure
public import IsotropicVariance.Statements.Curves.RectifiableCurveCost
public import IsotropicVariance.Statements.Curves.PassageTime
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfig
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfigInstMeasurableSpace
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfigAgreeOn
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfigIsMovedBy
public import IsotropicVariance.Statements.Configurations.PoissonConfigAgreeOn
public import IsotropicVariance.Statements.Configurations.PoissonConfigIsMovedBy
public import IsotropicVariance.Statements.Noise.IsWhiteNoise
public import IsotropicVariance.Statements.Noise.IsPoissonProcess
public import IsotropicVariance.Statements.Assumption.IsLocalDensity
public import IsotropicVariance.Statements.Density.TestFunctionReflectTranslate
public import IsotropicVariance.Statements.Density.ConvolutionDensity
public import IsotropicVariance.Statements.Cited.IsOs
public import IsotropicVariance.Statements.Cited.VPlus
public import IsotropicVariance.Statements.Cited.VMinus
public import IsotropicVariance.Statements.Cited.Entropy
public import IsotropicVariance.Statements.Cited.CoordDiff

/-!
# The definitions of the statements

Re-exports the definitions of `IsotropicVariance.Statements` that the main theorems and the cited
results are stated with: points, `e₁` and proper rigid motions; rectifiable curves, their length,
cumulative length, length function, arc-length measure and cost, and the passage time; the
configurations of white noise and of Poisson processes, with their restrictions and motions;
white noise and Poisson processes; local densities; the reflected translates of a test function
and the convolution density; and the notions of the cited results (`Cited.IsOs`, `Cited.vPlus`,
`Cited.vMinus`, `Cited.entropy`, `Cited.coordDiff`). With them come the instance
`WhiteNoiseConfig.instMeasurableSpace` and the two lemmas on cumulative length (continuity and
monotonicity). This module declares nothing, and imports none of the stated theorems.
-/
