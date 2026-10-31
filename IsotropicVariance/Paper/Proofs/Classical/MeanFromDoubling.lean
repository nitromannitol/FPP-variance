/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.MeanAnalytic
public import IsotropicVariance.Infra.TimeConstant.Limit

/-! # The classical mean bound after the sphere comparison

The step from the doubling inequality of [HN, Lemma 4.1] to the second bound of Lemma
`lem:classical`, by [HN, Lemma 4.2] with `a(ℓ) = E[T_ℓ]`, as in the proof of that lemma. The sphere
comparison producing the doubling inequality is in
`IsotropicVariance.Paper.Proofs.Classical.Mean`; this lemma alone does not prove
`ClassicalBoundsStatement`.
-/

@[expose] public section
open MeasureTheory Real Set Filter Topology
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra

/-- The doubling inequality of [HN, Lemma 4.1] implies the second bound of `eq:classical` at every
real `t ≥ 1` (proof of Lemma `lem:classical`). The lower bound `E[T_t] ≥ t` is the subadditivity
of the mean with `μ = 1`. The upper bound for large `t` is [HN, Lemma 4.2], and the other `t ≥ 1`
come from a deterministic `E[T_t] ≤ b t`, after enlarging `C`. -/
theorem classical_mean_bound_of_doubling {m : ℕ} (X : Setting m) (hNorm : X.IsNormalized)
    {K : ℝ} (hK : 0 ≤ K)
    (hDouble : ∀ s : ℝ, 1 ≤ s → 2 * X.mean s - K * errorScale s ≤ X.mean (2 * s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      0 ≤ X.mean t - t ∧ X.mean t - t ≤ C * sqrt (t * log (2 + t)) := by
  have hLarge := eventually_sub_le_errorScale_of_doubling X.mean hNorm hK
    ((eventually_ge_atTop (1 : ℝ)).mono hDouble)
  obtain ⟨a, b, ha, hBounds⟩ := TimeConstant.mean_bounds X
  have hb : 0 ≤ b := by
    obtain ⟨h₁, h₂⟩ := hBounds 1 zero_le_one
    linarith only [h₁, h₂, ha]
  obtain ⟨D, hD, hReal⟩ := le_errorScale_of_eventually X.mean hb
    (mul_nonneg (by norm_num) hK) (fun t ht => (hBounds t ht).2) hLarge
  exact ⟨D, hD, fun t ht => ⟨sub_nonneg.mpr (TimeConstant.mean_ge_of_isNormalized X hNorm
    (zero_le_one.trans ht)), hReal t ht⟩⟩

end IsotropicVariance.Paper.Proofs.Classical
