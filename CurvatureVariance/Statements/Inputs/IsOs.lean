/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.SetBernoulli
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# `CurvatureVariance.IsOs`

One of the definitions in which the statements of this library are written: the main theorem
`CurvatureVariance.lintegral_exp_passageTime_le` (Theorem `thm:main`), its corollary
`CurvatureVariance.evariance_passageTime_floorVertex_le_uniform`, the theorem at one direction
`CurvatureVariance.evariance_passageTime_floorVertex_le`, the results the paper cites and their
companions. Each statement and each definition is in a file of its own, and depends only on Mathlib
and on these definitions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- [AKM, (0.41)–(0.42), p. xxxvii]: `X ≤ O_s(θ)` means `E[exp((θ⁻¹ X₊)^s)] ≤ 2`, for a random
variable `X` (here: `X` is a.e.-measurable). Its body is that of `Infra.Os.IsOs`. It represents
AKM's notation only for `0 < s` and `0 < θ`, the range where AKM define it; outside that range it
has no meaning (for example `IsOs P s 0 X` holds trivially, since division by zero is `0`), and
every statement using it assumes `0 < s` and `0 < θ`. -/
def IsOs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s θ : ℝ) (X : Ω → ℝ) : Prop :=
  AEMeasurable X P ∧ ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s)) ∂P ≤ 2

end CurvatureVariance
