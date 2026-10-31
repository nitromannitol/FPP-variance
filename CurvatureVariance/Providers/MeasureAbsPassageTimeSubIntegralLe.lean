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
public import CurvatureVariance.Statements.Inputs.L1Norm
public import CurvatureVariance.Statements.Lattice.Config
public import CurvatureVariance.Statements.Lattice.Edge
public import CurvatureVariance.Statements.Lattice.PassageTime
public import CurvatureVariance.Statements.Lattice.Vertex
public import CurvatureVariance.Statements.Weights.AssumptionW
public import CurvatureVariance.Statements.Weights.IsIIDWeights
import CurvatureVariance.Infra.FPP.Statements

/-!
# Provider of `CurvatureVariance.measure_abs_passageTime_sub_integral_le`

Proves `CurvatureVariance.Providers.measure_abs_passageTime_sub_integral_le` with exactly the type
of the statement `CurvatureVariance.Statements.Inputs.MeasureAbsPassageTimeSubIntegralLe`, from
`Infra.FPP.measure_abs_passageTime_sub_integral_le` (stated with the copy `Infra.FPP.l1Norm`, whose
body is that of the definition `l1Norm`: they agree definitionally). The statement is proved by
`by exact` of this theorem applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- **[ADH, Theorem 3.13]**, specialized to (W) (cited for equation `eq:classical`, in the proof of
Lemma `lem:good` and in the proof of Lemma `lem:parent`): for `d ≥ 2` there are `C₁, C₂ > 0` such
that, for every `x ∈ ℤ^d \ {0}`, `T(0, x)` is integrable,
`P(T(0,x) − E T(0,x) ≥ t √‖x‖₁) ≤ e^{−C₁ t²}` for `t ∈ [0, C₂ √‖x‖₁]`, and
`P(T(0,x) − E T(0,x) ≤ −t √‖x‖₁) ≤ e^{−C₁ t²}` for all `t ≥ 0`. The constants depend only on `d` and
the law `F`. The point `x = 0` is excluded: there `T(0, 0) = 0` and the lower-tail event is the
whole space ([ADH] leave `x ≠ 0` implicit). -/
theorem measure_abs_passageTime_sub_integral_le {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ (P : Measure (Config m)) [IsProbabilityMeasure P],
      IsIIDWeights P F → ∀ x : Vertex m, x ≠ 0 →
        Integrable (fun ω => (passageTime ω 0 x : ℝ)) P ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ C₂ * √(l1Norm x : ℝ) →
          P {ω | t * √(l1Norm x : ℝ) ≤
              (passageTime ω 0 x : ℝ) - ∫ ω', (passageTime ω' 0 x : ℝ) ∂P} ≤
            ENNReal.ofReal (Real.exp (-(C₁ * t ^ 2)))) ∧
        (∀ t : ℝ, 0 ≤ t →
          P {ω | (passageTime ω 0 x : ℝ) - ∫ ω', (passageTime ω' 0 x : ℝ) ∂P ≤
              -(t * √(l1Norm x : ℝ))} ≤
            ENNReal.ofReal (Real.exp (-(C₁ * t ^ 2)))) :=
  Infra.FPP.measure_abs_passageTime_sub_integral_le hm F hW

end CurvatureVariance.Providers
