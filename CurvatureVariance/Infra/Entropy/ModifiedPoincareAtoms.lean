/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Inputs.VarianceMulLogLeOfEntropyLe
import CurvatureVariance.Infra.Entropy.Atoms

/-!
# [AB26, Proposition 1.3]: the modified Poincaré inequality

As `IsotropicVariance.Paper.Proofs.Modified` in the continuum library. The statement is the
continuum's contract `IsotropicVariance.Paper.Contracts.ModifiedPoincareStatement`, written out as
a theorem, since this file is in `Infra` and the contracts are in `Paper.Contracts`. The proof is
the continuum's, with this library's definitions `coordDiff` and `entropy`.

[AB26, Proposition 1.3] is [BR, Proposition 2.1], whose hypothesis is the logarithmic Sobolev
inequality `Ent[g²] ≤ (4/α) Var[g]` for the functions `g` of each coordinate. [AB26] proves that
inequality in one sentence, after the proposition, which is
`Infra.Entropy.entropy_sq_le_four_div_mul_variance_of_atoms`. The proposition then follows from the
instance `CurvatureVariance.variance_mul_log_le_of_entropy_le` of [BR, Proposition 2.1] with
`c = 4/α`. No other cited result enters.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CurvatureVariance.Infra.Entropy

/-- **[AB26, Proposition 1.3]** ([BR, Proposition 2.1]), with the logarithmic Sobolev inequality
of each coordinate from the sentence after it: let `α ∈ (0, 1]`, and
let `μ j` be the laws of countably many independent variables `X_j` with values in finite sets, each
value of probability `0` or at least `α`. Then every measurable `f ∈ L²` with
`Σ_j E[(f − E_j[f])²] < ∞` satisfies
`Var[f] log(Var[f] / Σ_j E[|f − E_j[f]|]²) ≤ (4/α) Σ_j E[(f − E_j[f])²]`,
where `f − E_j[f]` is `coordDiff μ j f`.

Readings, as in the continuum's `ModifiedPoincareStatement`:
* [AB26] asks that each value have probability at least `α`. That is the case where the finite set
  `X j` is the set of the values taken, so the form "`0` or at least `α`" contains it. It is also
  the form the lattice needs: Lemma `lem:labels` gives a variable `X_G`, determined by `τ|_G`,
  taking finitely many values, each with probability at least `α_L`. To apply this theorem with
  `α = α_L`, the coordinate `j = G` needs a finite type `X G` that holds those values, with `μ G`
  the law of `X_G` on it. A value of `X G` that `X_G` does not take has probability `0`, so `X G`
  may be larger than the set of values taken. The family must also be countable and independent: the
  blocks are countably many, and `X_G` is determined by `τ|_G`. This independence is what the
  product law `Measure.infinitePi μ` encodes;
* the hypothesis of summability is not in [AB26]. If the sum is infinite, the right side of the
  inequality of [AB26] is infinite and the bound is trivial, while a real `∑'` of a family that is
  not summable is `0`. Under the hypothesis both real sums are those of [AB26], since
  `E[|f − E_j[f]|]² ≤ E[(f − E_j[f])²]`;
* `f` is measurable, as a random variable is;
* `α ≤ 1` is in the statement of [AB26], and the proof does not use it. -/
theorem variance_mul_log_le_of_atoms {ι : Type*} [Countable ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] {α : ℝ} (hα : 0 < α)
    (_hα1 : α ≤ 1) (hatom : ∀ i (x : X i), μ i {x} = 0 ∨ ENNReal.ofReal α ≤ μ i {x})
    {f : (∀ i, X i) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (Measure.infinitePi μ))
    (hA : Summable fun i => ∫ x, CurvatureVariance.coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ) :
    variance f (Measure.infinitePi μ) *
        Real.log (variance f (Measure.infinitePi μ) /
          ∑' i, (∫ x, |CurvatureVariance.coordDiff μ i f x| ∂Measure.infinitePi μ) ^ 2) ≤
      4 / α * ∑' i, ∫ x, CurvatureVariance.coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ :=
  CurvatureVariance.variance_mul_log_le_of_entropy_le μ (div_pos four_pos hα).le
    (fun i g => entropy_sq_le_four_div_mul_variance_of_atoms (μ i) hα (hatom i) g)
    hfm hf hA

end CurvatureVariance.Infra.Entropy
