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
public import CurvatureVariance.Statements.Inputs.CoordDiff
public import CurvatureVariance.Statements.Inputs.Entropy
import CurvatureVariance.Infra.Entropy.Instance

/-!
# Provider of `CurvatureVariance.variance_mul_log_le_of_entropy_le`

Proves `CurvatureVariance.Providers.variance_mul_log_le_of_entropy_le` with exactly the type of the
statement `CurvatureVariance.Statements.Inputs.VarianceMulLogLeOfEntropyLe`, from
`Infra.Entropy.br_instance_of_coordinate_lsi` (stated with `Infra.Entropy.entropy` and
`Infra.Entropy.coordDiff`, whose bodies are those of the definitions `entropy` and `coordDiff`: they
agree definitionally). The statement is proved by `by exact` of this theorem applied to its binders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Providers

/-- **[BR, Proposition 2.1]**, the instance the paper applies (through [AB26, Proposition 1.3], in
[AB26, proof of Proposition 6.5], which the proof of Proposition `prop:gain` applies): countably
many independent coordinates with values in finite sets, `Aᵢ = L²(µᵢ)` and `Rᵢ = √c (Id − Eᵢ)`. If
every `µᵢ` satisfies `Ent_{µᵢ}(g²) ≤ c Var_{µᵢ}(g)` (that is, `Ent_{µᵢ}(g²) ≤ E_{µᵢ}(Rᵢ g)²`), then
for every measurable `f ∈ L²(µ^I)` with `∑ᵢ ‖Δᵢ f‖₂² < ∞`,
`Var(f) log (Var(f) / ∑ᵢ ‖Δᵢ f‖₁²) ≤ c ∑ᵢ ‖Δᵢ f‖₂²`, which is `∑ᵢ E(Rᵢ f)²`. Every premise of [BR]
holds for these operators: they vanish on constants and commute with integration over the other
coordinates. -/
theorem variance_mul_log_le_of_entropy_le {ι : Type*} [Countable ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, MeasurableSingletonClass (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] {c : ℝ} (hc : 0 ≤ c)
    (hLSI : ∀ i (g : X i → ℝ), entropy (μ i) (fun y => g y ^ 2) ≤ c * variance g (μ i))
    {f : (∀ i, X i) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (Measure.infinitePi μ))
    (hA : Summable fun i => ∫ x, coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ) :
    variance f (Measure.infinitePi μ) *
        Real.log (variance f (Measure.infinitePi μ) /
          ∑' i, (∫ x, |coordDiff μ i f x| ∂Measure.infinitePi μ) ^ 2) ≤
      c * ∑' i, ∫ x, coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ :=
  Infra.Entropy.br_instance_of_coordinate_lsi hc hLSI hfm hf hA

end CurvatureVariance.Providers
