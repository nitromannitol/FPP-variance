/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance
public import CurvatureVariance.Statements.Curvature.AssumptionCWith
public import CurvatureVariance.Statements.Lattice.Config
public import CurvatureVariance.Statements.Lattice.Edge
public import CurvatureVariance.Statements.Lattice.PassageTime
public import CurvatureVariance.Statements.Lattice.Vertex
public import CurvatureVariance.Statements.Space.Point
public import CurvatureVariance.Statements.Space.Pt
public import CurvatureVariance.Statements.Space.PtNorm
public import CurvatureVariance.Statements.TimeConstant.IsTimeConstant
public import CurvatureVariance.Statements.Weights.AssumptionW
public import CurvatureVariance.Statements.Weights.IsIIDWeights
import CurvatureVariance.Paper.Closing.Main

/-!
# Provider of `CurvatureVariance.lintegral_exp_passageTime_le`

The provider of the main theorem `CurvatureVariance.lintegral_exp_passageTime_le` (Theorem
`thm:main`): `CurvatureVariance.Providers.lintegral_exp_passageTime_le` has exactly its type, and
its proof is `CurvatureVariance.Paper.Closing.lintegral_exp_passageTime_le` applied to the binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- **Theorem `thm:main`.** Let the weights of first-passage percolation on `ℤ^d`, `d = m + 1 ≥ 2`,
be independent with common law `F` satisfying (W), and let `μ` be the time constant. For all
constants `δ ∈ (0, 1]`, `r > 0`, `M ≥ 0` and `c > 0` there are `ε > 0` and `C < ∞` such that, for
every unit vector `ξ` satisfying (Curv) with these constants and every `x ∈ ℤ^d ∖ {0}` within
distance `|x|^{3/4}` of the ray `ℝ₊ξ`, the passage time `T(0, x)` is a random variable with
`E[exp(|T(0, x) − μ(x)| / (C |x|^{(1−ε)/2}))] ≤ 2`.

The paper writes `Λ` for `M` and `λ` for `c`, and (Curv) with these constants is
`AssumptionCWith μ ξ δ r M c`. The numbers `ε` and `C` depend only on `d`, `F`, `δ`, `r`, `M` and
`c`, not on `ξ` or `x`. Here `|·|` is the Euclidean norm, and `x` is within distance `|x|^{3/4}` of
the ray when some `βξ` with `β ≥ 0` is: the ray is closed, so it contains a nearest point of `x`.
The constant `C` is positive, so the denominator is positive. -/
theorem lintegral_exp_passageTime_le {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (P : Measure (Config m))
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) (μ : PtNorm m) (hμ : IsTimeConstant P μ)
    (δ r M c : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ ξ : Pt m, ‖ξ‖ = 1 → AssumptionCWith μ ξ δ r M c →
      ∀ x : Vertex m, x ≠ 0 →
        (∃ β : ℝ, 0 ≤ β ∧ ‖point x - β • ξ‖ ≤ ‖point x‖ ^ (3 / 4 : ℝ)) →
          AEMeasurable (fun ω => (passageTime ω 0 x : ℝ)) P ∧
            ∫⁻ ω, ENNReal.ofReal (Real.exp
                (|(passageTime ω 0 x : ℝ) - μ.1 (point x)| /
                  (C * ‖point x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 :=
  CurvatureVariance.Paper.Closing.lintegral_exp_passageTime_le
    hm F hW P hP μ hμ δ r M c hδ hδ₁ hr hM hc

end CurvatureVariance.Providers
