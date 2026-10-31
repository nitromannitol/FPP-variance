/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Probability.Moments.Variance
public import CurvatureVariance.Statements.Space.Pt
public import CurvatureVariance.Statements.Space.PtNorm

/-!
# `CurvatureVariance.AssumptionCAt`

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

/-- **The expansion of `μ` at the direction `ξ` along the linear hyperplane `H`**, the hypothesis of
the theorem at one direction: there exist `δ ∈ (0, 1]`, `r > 0`, `M ∈ [0, ∞)`, a linear functional
`ℓ_H : H → ℝ` and a positive definite quadratic form `q_H` on `H` such that, for every `h ∈ H` with
`|h| ≤ r`, `|μ(ξ + h) − μ(ξ) − ℓ_H(h) − q_H(h)| ≤ M |h|^{2+δ}`. Here `|h|` is the Euclidean norm of
`ℝ^d`. The constants are not fixed in advance, and `H` need not be orthogonal to `ξ`; that `H` is
transverse to `ξ` is a separate hypothesis of the theorem at one direction. Assumption (Curv) of the
introduction, at a unit `ξ` with constants, is `AssumptionCWith`. -/
def AssumptionCAt {m : ℕ} (μ : PtNorm m) (ξ : Pt m) (H : Submodule ℝ (Pt m)) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 ≤ M ∧
    ∃ ℓ : Module.Dual ℝ H, ∃ q : QuadraticForm ℝ H, q.PosDef ∧
      ∀ h : H, ‖h‖ ≤ r → |μ.1 (ξ + h) - μ.1 ξ - ℓ h - q h| ≤ M * ‖h‖ ^ (2 + δ)

end CurvatureVariance
