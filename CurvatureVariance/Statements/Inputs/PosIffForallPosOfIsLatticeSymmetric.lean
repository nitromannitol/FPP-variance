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
public import CurvatureVariance.Statements.Inputs.IsLatticeSymmetric
public import CurvatureVariance.Statements.Space.EOne
public import CurvatureVariance.Statements.Space.Pt
import CurvatureVariance.Providers.PosIffForallPosOfIsLatticeSymmetric

/-!
# `CurvatureVariance.pos_iff_forall_pos_of_isLatticeSymmetric`

A result the paper cites, stated with Mathlib and the definitions of this directory only, and proved
in this library: its proof is `CurvatureVariance.Providers.pos_iff_forall_pos_of_isLatticeSymmetric`
applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance

/-- **[ADH, Theorem 2.6]**, from the properties listed before it (p. 11): for a continuous function
`µ` on `ℝ^d` that is subadditive, satisfies `µ(cx) = |c| µ(x)`, and is invariant under the
symmetries of `ℤ^d` that fix the origin, `µ(e₁) > 0` if and only if `µ(x) > 0` for all `x ≠ 0`. -/
theorem pos_iff_forall_pos_of_isLatticeSymmetric {m : ℕ} (μ : Pt m → ℝ)
    (hsub : ∀ x y, μ (x + y) ≤ μ x + μ y) (hhom : ∀ (c : ℝ) x, μ (c • x) = |c| * μ x)
    (hsym : IsLatticeSymmetric μ) (hcont : Continuous μ) :
    0 < μ e₁ ↔ ∀ x, x ≠ 0 → 0 < μ x :=
  by exact
    CurvatureVariance.Providers.pos_iff_forall_pos_of_isLatticeSymmetric μ hsub hhom hsym hcont

end CurvatureVariance
