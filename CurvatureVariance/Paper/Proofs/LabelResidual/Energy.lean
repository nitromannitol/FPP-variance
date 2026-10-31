/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.LabelResidual.MixtureArrays
public import CurvatureVariance.Paper.Proofs.LabelResidual.Factor
public import CurvatureVariance.Paper.Proofs.Gain.AVLabels
public import CurvatureVariance.Paper.Proofs.Gain.RREfronStein

/-!
# The label energy by the reward arrays: averages over the offsets

The first bound of equation `eq:residual` (Lemma `lem:residual`) comes, as in the first paragraph
of [AB26, proof of Lemma 6.3], from equation `eq:blocksum` for the resampling of each block given
its label, on average over the offsets (`Proofs.Residual.exists_offsetAverage_blockEnergy_le`).
`offsetAverage_eq_offsetAvg` identifies the two forms of the average over the offset families
`σ` that it uses: `offsetAverage` of a function of the offsets `offsetOf σ`, and `offsetAvg`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain.LabelResidual

open CurvatureVariance.Paper CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-- The average over offsets of `AVLabels` is the average over offset families. -/
theorem offsetAverage_eq_offsetAvg {K L : ℕ} (E : (ℕ → Fin m → ℤ) → ℝ≥0∞) :
    offsetAverage K L E = offsetAvg (fun σ : Fin K → Fin m → Fin L => E (offsetOf σ)) := by
  unfold offsetAverage offsetAvg
  congr 2
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [← pow_mul, mul_comm]

end CurvatureVariance.Paper.Gain.LabelResidual
