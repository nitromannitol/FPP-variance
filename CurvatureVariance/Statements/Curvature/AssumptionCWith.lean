/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Probability.Moments.Variance
public import CurvatureVariance.Statements.Space.Pt
public import CurvatureVariance.Statements.Space.PtNorm

/-!
# `CurvatureVariance.AssumptionCWith`

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

/-- **Assumption (Curv)** of the introduction, at the unit direction `ξ` with the constants
`δ, r, M, c` (the paper writes `Λ` for `M` and `λ` for `c`): there are a linear functional `ℓ` and a
quadratic form `q` on the hyperplane `ξ^⊥` with `q h ≥ c |h|²` such that
`|μ(ξ + h) − μ(ξ) − ℓ(h) − q(h)| ≤ M |h|^{2+δ}` for every `h ∈ ξ^⊥` with `|h| ≤ r`. -/
def AssumptionCWith {m : ℕ} (μ : PtNorm m) (ξ : Pt m) (δ r M c : ℝ) : Prop :=
  ∃ ℓ : Module.Dual ℝ (Submodule.span ℝ {ξ})ᗮ, ∃ q : QuadraticForm ℝ (Submodule.span ℝ {ξ})ᗮ,
    (∀ h, c * ‖h‖ ^ 2 ≤ q h) ∧
      ∀ h : (Submodule.span ℝ {ξ})ᗮ, ‖h‖ ≤ r →
        |μ.1 (ξ + h) - μ.1 ξ - ℓ h - q h| ≤ M * ‖h‖ ^ (2 + δ)

end CurvatureVariance
