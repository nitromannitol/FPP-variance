/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Minimum

/-!
# Statements of Section `sec:prelim`, part 1: the noise interface and the classical bounds

Each statement is a `def …Statement : Prop` over the definitions of `IsotropicVariance.Paper.Defs`,
proved in `IsotropicVariance.Paper.Proofs`.

* `SettingOfRealizationStatement`: the bridge from the data of the main theorems to the noise
  interface `Setting`; passage times between any two points are random variables.
* `ClassicalBoundsStatement`: Lemma `lem:classical`.

The statements of Lemmas `lem:straight`, `lem:slab` and `lem:polynomialarray` are in
`IsotropicVariance.Paper.Contracts.Slab`. The other facts of Section `sec:prelim` are proved
directly: the density `ψ(χ∗ω)` satisfies
Assumption `ass:local` (`Infra.Example.isLocalDensity_convolutionDensity`); the time constant
`μ = lim E T_t / t` exists, is positive, and `E T_t ≥ μ t`
(`Infra.TimeConstant.exists_timeConstant`); and dividing the density by `μ` keeps Assumption
`ass:local` and normalizes it (`Infra.TimeConstant.normalized`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

universe u

namespace IsotropicVariance.Paper.Contracts

/-- **The noise interface realizes the data of the main theorems**, for the Poisson process and
for white noise: every realization of the data of Theorems `thm:general` and `thm:main`
(`Realization`: a noise on a standard Borel space and a density satisfying `IsLocalDensity`,
Assumption `ass:local`) has a `Setting` whose passage times `T(u, v)` have the same laws, for all
points `u` and `v`, both almost everywhere measurable. -/
def SettingOfRealizationStatement : Prop :=
  ∀ (m : ℕ) (X : Realization.{u} m), ∃ S : Setting.{0} m, ∀ u v : Pt m,
    AEMeasurable (fun ω => passageTime (X.ρ (X.config ω)) u v) X.P ∧
      AEMeasurable (fun ω => S.passTime ω u v) S.P ∧
        X.P.map (fun ω => passageTime (X.ρ (X.config ω)) u v) =
          S.P.map (fun ω => S.passTime ω u v)

/-- **Lemma `lem:classical`** (classical bounds, equation `eq:classical`):
for the density normalized by `μ = 1` there is `C > 0` such that for every `t ≥ 1`,
`|T_t − E T_t| ≤ O_2(C √t)` and `0 ≤ E T_t − t ≤ C √(t log(2 + t))`. -/
def ClassicalBoundsStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized →
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      Cited.IsOs X.P 2 (C * Real.sqrt t) (fun ω => |X.TRV t ω - X.mean t|) ∧
        0 ≤ X.mean t - t ∧ X.mean t - t ≤ C * Real.sqrt (t * Real.log (2 + t))

end IsotropicVariance.Paper.Contracts
