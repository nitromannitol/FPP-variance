/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Basic
public import CurvatureVariance.Statements.Inputs.CoordDiff
public import CurvatureVariance.Statements.Inputs.IsOs
public import CurvatureVariance.Infra.Os.Sum
public import CurvatureVariance.Paper.Proofs.OsSum
public import CurvatureVariance.Infra.Os.Maximum
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Contracts: the rules of Section `ssec:notation` and [AB26, Proposition 1.3]

The cited inputs are stated in their source form (the modules `CurvatureVariance.Statements.Inputs`).
The forms the paper uses are internal statements:

* `OsUnionStatement` — equation `eq:union`: the union bound for every `s > 0`; proved here from
  `Infra.Os.isOs_finset_sup'_log`.
* `SignedOsSumStatement` — equation `eq:sum`, for signed finite sums, in the stronger form for every
  `s > 0`; proved here: for `s ≥ 1` from [AKM, Lemma A.4] (`Paper.isOs_sum_of_one_le`), for
  `s < 1` from `Infra.Os.isOs_sum_le`.
* `OsSumStatement` — equation `eq:sum` as in the paper, for `s ≥ 1` with constant `1`, over the
  cited `CurvatureVariance.IsOs`: a corollary of `SignedOsSumStatement`.
* `ModifiedPoincareStatement` — [AB26, Proposition 1.3], the instance of [BR, Proposition 2.1] for
  finitely many values. It is a result of the companion paper, not of the literature, so this
  library proves it (`Proofs.Modified.modifiedPoincareStatement_holds`), by the proof of the
  continuum library, from the cited `CurvatureVariance.variance_mul_log_le_of_entropy_le`.

The contracts are written with the cited `CurvatureVariance.IsOs`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper

universe u v

/-- **Equation `eq:union`** ([AB26, (1.6)]): for every `s > 0` there is `C(s)` such that, if
`X_j ≤ O_s(θ)` for `j` in a nonempty finite set of `J` indices, then
`max_j X_j ≤ O_s(C(s) θ log^{1/s}(2 + J))`.

The paper writes `j ≤ J`: `J` is the number of indices. The maximum needs a nonempty index set, and
`θ > 0` is the range of the notation (Section `ssec:notation`). -/
def OsUnionStatement : Prop :=
  ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type v}
      (T : Finset ι) (hT : T.Nonempty) (θ : ℝ), 0 < θ → ∀ X : ι → Ω → ℝ,
      (∀ i ∈ T, CurvatureVariance.IsOs P s θ (X i)) →
        CurvatureVariance.IsOs P s (C * θ * Real.log (2 + T.card) ^ (1 / s)) (T.sup' hT X)

/-- The union bound holds, with `C(s) = (2/log 2)^{1/s}`. -/
theorem osUnionStatement_holds : OsUnionStatement.{u, v} := by
  intro s hs
  refine ⟨((2 : ℝ) / Real.log 2) ^ (1 / s),
    Real.rpow_pos_of_pos (div_pos two_pos (Real.log_pos one_lt_two)) _, ?_⟩
  intro Ω _ P _ ι T hT θ hθ X hX
  exact Infra.Os.isOs_finset_sup'_log hs hθ T hT X hX

/-- **Equation `eq:sum` for signed finite sums, every `s > 0`** (in the paper for `s ≥ 1`): for each
`s > 0` there is `C_s` (`C_s = 1` for `s ≥ 1`) such that `Xᵢ ≤ O_s(θᵢ)` for `i` in a nonempty finite
set gives `∑ᵢ Xᵢ ≤ O_s(C_s ∑ᵢ θᵢ)`, without independence or signs.

This is stronger than the paper's statement in `s`. The paper names no index set: every use in the
paper and in the cited proofs is a finite sum, with `θᵢ > 0`. The paper's range `s ≥ 1` goes through
[AKM, Lemma A.4], the cited `CurvatureVariance.exists_isOs_integral` (`Paper.isOs_sum_of_one_le`);
the case `s < 1` is not in the paper, and is proved by `Infra.Os.isOs_sum_le`. -/
def SignedOsSumStatement : Prop :=
  ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧ (1 ≤ s → C = 1) ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type v}
      (T : Finset ι), T.Nonempty → ∀ (θ : ι → ℝ), (∀ i ∈ T, 0 < θ i) →
      ∀ X : ι → Ω → ℝ, (∀ i ∈ T, CurvatureVariance.IsOs P s (θ i) (X i)) →
        CurvatureVariance.IsOs P s (C * ∑ i ∈ T, θ i) (fun ω => ∑ i ∈ T, X i ω)

theorem signedOsSumStatement_holds : SignedOsSumStatement.{u, v} := by
  intro s hs
  refine ⟨Infra.Os.sumConstant s, Infra.Os.sumConstant_pos hs, fun h1 => ?_, ?_⟩
  · simp [Infra.Os.sumConstant, h1]
  · intro Ω _ P _ ι T hT θ hθ X hX
    by_cases h1 : 1 ≤ s
    · have := Paper.isOs_sum_of_one_le h1 T hT θ hθ X hX
      simpa [Infra.Os.sumConstant, h1] using this
    · exact Infra.Os.isOs_sum_le hs T θ hθ X hX hT

/-- **Equation `eq:sum`**, over the cited `CurvatureVariance.IsOs`: if `s ≥ 1` and `Xᵢ ≤ O_s(θᵢ)`
for `i` in a nonempty finite set, then `∑ᵢ Xᵢ ≤ O_s(∑ᵢ θᵢ)`.

The paper's index set is read as finite, as in `SignedOsSumStatement`. This is the corollary of that
statement at `s ≥ 1`, where its constant is `1`; its proof is the paper's. -/
def OsSumStatement : Prop :=
  ∀ s : ℝ, 1 ≤ s →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type v}
      (T : Finset ι), T.Nonempty → ∀ (θ : ι → ℝ), (∀ i ∈ T, 0 < θ i) →
      ∀ X : ι → Ω → ℝ, (∀ i ∈ T, IsOs P s (θ i) (X i)) →
        IsOs P s (∑ i ∈ T, θ i) (fun ω => ∑ i ∈ T, X i ω)

/-- Equation `eq:sum`, by [AKM, Lemma A.4] applied to the positive parts
(`Paper.isOs_sum_of_one_le`). -/
theorem osSumStatement_holds : OsSumStatement.{u, v} := by
  intro s hs Ω _ P _ ι T hT θ hθ X hX
  exact Paper.isOs_sum_of_one_le hs T hT θ hθ X hX

/-- **[AB26, Proposition 1.3]** ([BR, Proposition 2.1] for finitely many values; used in the proof
of [AB26, Proposition 6.5], which the proof of Proposition `prop:gain` applies): let
`α ∈ (0, 1]`, and let `μ j` be the laws of countably many independent variables `X_j` with values in
finite sets, each value of probability `0` or at least `α`. Then every measurable `f ∈ L²` with
`Σ_j E[(f − E_j[f])²] < ∞` satisfies
`Var[f] log(Var[f] / Σ_j E[|f − E_j[f]|]²) ≤ (4/α) Σ_j E[(f − E_j[f])²]`,
where `f − E_j[f]` is `coordDiff μ j f`.

Readings, as in the model `IsotropicVariance.Paper.Contracts.ModifiedPoincareStatement`:
* [AB26] asks that each value have probability at least `α`. That is the case where the finite
  set `X j` is the set of the values taken, so the form "`0` or at least `α`" contains that of
  [AB26];
* the hypothesis of summability is not in [AB26]. If the sum is infinite, the right side of its
  bound is infinite and the bound is trivial, while a real `∑'` of a family that is not summable is
  `0`. Under the hypothesis both real sums are those of [AB26], since
  `E[|f − E_j[f]|]² ≤ E[(f − E_j[f])²]`;
* `f` is measurable, as a random variable is. -/
def ModifiedPoincareStatement : Prop :=
  ∀ {ι : Type u} [Countable ι] [DecidableEq ι] {X : ι → Type v} [∀ i, Fintype (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] {α : ℝ}, 0 < α → α ≤ 1 →
    (∀ i (x : X i), μ i {x} = 0 ∨ ENNReal.ofReal α ≤ μ i {x}) →
    ∀ {f : (∀ i, X i) → ℝ}, Measurable f → MemLp f 2 (Measure.infinitePi μ) →
      (Summable fun i => ∫ x, coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ) →
      variance f (Measure.infinitePi μ) *
          Real.log (variance f (Measure.infinitePi μ) /
            ∑' i, (∫ x, |coordDiff μ i f x| ∂Measure.infinitePi μ) ^ 2) ≤
        4 / α * ∑' i, ∫ x, coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ

end CurvatureVariance.Paper.Contracts
