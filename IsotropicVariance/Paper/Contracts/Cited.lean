/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.SurfaceDefs
public import IsotropicVariance.Infra.Os.Maximum
public import IsotropicVariance.Infra.Os.Moments
public import IsotropicVariance.Infra.EfronStein.Finite

/-!
# The cited results in the forms the paper uses

The statements `IsotropicVariance.Cited.*` are the literal statements of the sources. This file
states the forms the paper uses that none of them gives:

* `OsUnionBoundStatement`: the union bound for maxima, equation `eq:union`, proved by
  `Infra.Os.isOs_finset_sup'_log` (`osUnionBoundStatement_holds`).
* `OsMomentStatement`: the moment bound of Section `ssec:notation`, proved by
  `Cited.IsOs.lintegral_pos_rpow_le` (`osMomentStatement_holds`).
* `ModifiedPoincareStatement`: Proposition `prop:BR`, the instance of [BR, Proposition 2.1] for
  finitely many values. It is proved in `Paper.Proofs.Modified`, from the cited instance below and
  the paper's logarithmic Sobolev inequality,
  `Infra.Entropy.entropy_sq_le_four_div_mul_variance_of_atoms`.

The paper takes the first two from [AKM, Appendix A]. They are short consequences of the definition
of `O_s`, so they are stated and proved here.

## The statements of the paper's citations

* [AKM, (0.41)–(0.42)], the notation `X ≤ O_s(θ)`: `Cited.IsOs`.
* [AKM, Lemma A.1], the tail bound of Section `ssec:notation` and its converse:
  `Cited.IsOs.measure_ge_le` and `Cited.isOs_of_measure_ge_le`.
* [AKM, Lemma A.4], the sum rule, equation `eq:sum`, which the paper states for `s ≥ 1`:
  `Cited.isOs_integral_of_one_le`, read on finite sums by `Infra.Os.isOs_sum_of_one_le`.
* [BLM03, Corollary 3] and [BLM03, Theorem 7], for the first bound of Lemma `lem:classical`:
  `Cited.blm_corollary3` and `Cited.blm_theorem7`.
* [HN, Lemma 4.2], for the second bound of Lemma `lem:classical`: `Cited.hn_lemma4_2`. The doubling
  inequality of [HN, Lemma 4.1] is not among these statements; it is proved in
  `IsotropicVariance.Paper.Proofs.Classical`.
* [BLM03, Proposition 1], the Efron–Stein inequality: `Cited.blm_proposition1`. The paper extends it
  to countably many variables, which is `Infra.EfronStein.evariance_le_half_tsum_resampleEnergy`,
  and applies it conditionally in the proof of Lemma `lem:residual`, which is
  `Infra.EfronStein.lintegral_sub_condExp_allLabelSigma_le`.
* [BR, Proposition 2.1], for Proposition `prop:BR`: `Cited.variance_mul_log_le_of_entropy_le`.

These are all the theorems of `IsotropicVariance.Statements.Cited`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u v

namespace IsotropicVariance.Paper.Contracts

/-- **The union bound, equation `eq:union`**: for `s, θ > 0`, if
`X_j ≤ O_s(θ)` for every `j` in a nonempty finite set of `J` indices, then
`max_j X_j ≤ O_s(C(s) θ log^{1/s}(2 + J))`, with `C(s) = (2/log 2)^{1/s}`. -/
def OsUnionBoundStatement : Prop :=
  ∀ {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s θ : ℝ}, 0 < s → 0 < θ → ∀ (T : Finset ι) (hT : T.Nonempty) (X : ι → Ω → ℝ),
    (∀ i ∈ T, Cited.IsOs P s θ (X i)) →
      Cited.IsOs P s (((2 : ℝ) / Real.log 2) ^ (1 / s) * θ *
        Real.log (2 + (T.card : ℝ)) ^ (1 / s)) (T.sup' hT X)

/-- The union bound holds. -/
theorem osUnionBoundStatement_holds : OsUnionBoundStatement.{u, v} :=
  fun hs hθ T hT X hX => Infra.Os.isOs_finset_sup'_log hs hθ T hT X hX

/-- **The moment bound** of Section `ssec:notation`: `X ≤ O_s(θ)` gives
`E X₊^p ≤ 2(1 + ⌈p/s⌉!) θ^p` for every `p ≥ 0`. -/
def OsMomentStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {s θ p : ℝ} {X : Ω → ℝ},
    Cited.IsOs P s θ X → 0 < s → 0 < θ → 0 ≤ p →
      (∫⁻ ω, ENNReal.ofReal (max (X ω) 0 ^ p) ∂P) ≤
        ENNReal.ofReal (2 * (1 + ((Nat.ceil (p / s)).factorial : ℝ)) * θ ^ p)

/-- The moment bound holds. -/
theorem osMomentStatement_holds : OsMomentStatement.{u} :=
  fun hX hs hθ hp => Cited.IsOs.lintegral_pos_rpow_le hX hs hθ hp

/-- **Proposition `prop:BR`** ([BR, Proposition 2.1]): let `α ∈ (0, 1]`, and let
`μ j` be the laws of countably many independent variables `X_j` with values in finite sets, each
value of probability `0` or at least `α`. Then every measurable `f ∈ L²` with
`Σ_j E[(f − E_j[f])²] < ∞` satisfies
`Var[f] log(Var[f] / Σ_j E[|f − E_j[f]|]²) ≤ (4/α) Σ_j E[(f − E_j[f])²]`,
where `f − E_j[f]` is `Cited.coordDiff μ j f`.

Readings:
* the paper asks that each value have probability at least `α`. That is the case where the finite
  set `X j` is the set of the values taken, so the form "`0` or at least `α`" contains the paper's.
  It is also the form the use needs: Lemma `lem:labels` gives variables `X_G` whose values each have
  probability at least `α_L`, and the labels of a `Setting.LabelFamily` take their values in one
  finite type, where a value that a label does not take has probability `0`;
* the paper does not state the hypothesis of summability. If the sum is infinite, the right side of
  the paper's bound is infinite and the bound is trivial, while a real `∑'` of a family that is not
  summable is `0`. Under the hypothesis both real sums are those of the paper, since
  `E[|f − E_j[f]|]² ≤ E[(f − E_j[f])²]`;
* `f` is measurable, as a random variable is. -/
def ModifiedPoincareStatement : Prop :=
  ∀ {ι : Type u} [Countable ι] [DecidableEq ι] {X : ι → Type v} [∀ i, Fintype (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] {α : ℝ}, 0 < α → α ≤ 1 →
    (∀ i (x : X i), μ i {x} = 0 ∨ ENNReal.ofReal α ≤ μ i {x}) →
    ∀ {f : (∀ i, X i) → ℝ}, Measurable f → MemLp f 2 (Measure.infinitePi μ) →
      (Summable fun i => ∫ x, Cited.coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ) →
      variance f (Measure.infinitePi μ) *
          Real.log (variance f (Measure.infinitePi μ) /
            ∑' i, (∫ x, |Cited.coordDiff μ i f x| ∂Measure.infinitePi μ) ^ 2) ≤
        4 / α * ∑' i, ∫ x, Cited.coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ

end IsotropicVariance.Paper.Contracts
