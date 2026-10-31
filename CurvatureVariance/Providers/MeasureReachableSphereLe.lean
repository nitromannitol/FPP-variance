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
public import CurvatureVariance.Statements.Inputs.SupNorm
public import CurvatureVariance.Statements.Lattice.Edge
public import CurvatureVariance.Statements.Lattice.Vertex
public import CurvatureVariance.Statements.Percolation.BondCriticalProb
public import CurvatureVariance.Statements.Percolation.OpenGraph
import CurvatureVariance.Infra.Percolation.LatticeSharpness

/-!
# Provider of `CurvatureVariance.measure_reachable_sphere_le`

Proves `CurvatureVariance.Providers.measure_reachable_sphere_le` with exactly the type of the
statement `CurvatureVariance.Statements.Inputs.MeasureReachableSphereLe`, from
`Infra.Percolation.measure_reachable_sphere_le` (stated with `latticeSupNorm`, whose body is that of
the definition `supNorm`: the two agree definitionally). The statement is proved by `by exact` of
this theorem applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- **[Duminil-Copin and Tassion, Theorem 1.1(1)]** (the decay below `p_c` behind Kesten's estimate
under `F(0) < p_c`): for bond percolation on `ℤ^d`, `d ≥ 2`, and
`p < p_c`, there is `c = c(p) > 0` such that `P_p[0 ↔ ∂Λ_n] ≤ e^{−cn}` for every `n ≥ 1`. -/
theorem measure_reachable_sphere_le {m : ℕ} (hm : 1 ≤ m) (p : unitInterval)
    (hp : (p : ℝ) < bondCriticalProb m) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      setBernoulli (Set.univ : Set (Edge m)) p
          {S | ∃ x : Vertex m, supNorm x = n ∧ (openGraph m S).Reachable 0 x} ≤
        ENNReal.ofReal (Real.exp (-(c * n))) :=
  Infra.Percolation.measure_reachable_sphere_le hm p hp

end CurvatureVariance.Providers
