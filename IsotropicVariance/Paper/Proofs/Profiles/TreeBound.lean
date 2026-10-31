/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.DyadicTree
public import IsotropicVariance.Paper.Contracts.Profiles
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:tree`: the statement `TreeStatement`

The proof in the paper, from the induction hypothesis `eq:premise` alone: the
pairs of `𝒜_j`, `j < j₀`, have lengths in `[1, N/2]`, so `eq:premise`, isotropy and
`Q_{2^{−j} t} ≤ 2^{−2j/5} Q_t` bound their excess, and `dyadicTree_bound` concludes. There is no
regime hypothesis and no threshold on `N`, and the constant depends on the setting only.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

universe u

namespace IsotropicVariance.Paper.Proofs.Profiles

open Infra.Os

/-- **Lemma `lem:tree`, equation `eq:tree`**, by the paper's proof, which uses `eq:premise`,
isotropy, `eq:union` and `eq:sum` only. The second sentence of the lemma is proved directly, with
isotropy applied to each pair of `𝒜_j` (`steps_of_premise`), instead of moving the supremum over
`B` by a rigid motion. -/
theorem treeStatement_holds : Contracts.TreeStatement.{u} := by
  intro m hm X _
  obtain ⟨Bd, hBd0, hBd⟩ := exists_upperBound X
  refine ⟨dyadicTreeConst m Bd 1 (256 * (m + 1)), ?_,
    fun K A N hK hA _ hP t ht htN x e he B hB hdiam hline => ?_⟩
  · unfold dyadicTreeConst
    have := treeSeries_pos
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have htpos : 0 < t := by linarith only [ht]
  have hA0 : 0 < A := by linarith only [hA]
  refine dyadicTree_bound X hBd hBd0.le ht (one_le_Q hK hA (by linarith only [ht])) one_pos
    (le_of_eq (by rw [sq_tubeWidth hA0.le htpos.le])) ?_ he hB hdiam hline
  intro j hj p q h1 h2
  have h3 : 1 ≤ dist p q := by linarith only [h1, hj]
  have h4 : dist p q ≤ N / 2 := by linarith only [h2, genScale_le htpos.le j, htN]
  refine (steps_of_premise hm hA0 hP p q h3 h4).mono_scale zero_le_one
    (mul_pos one_pos (Q_pos hA0 (by linarith only [h3]))) ?_
  rw [mul_assoc, treeRatio_pow]
  refine mul_le_mul_of_nonneg_left ?_ zero_le_one
  refine Q_le_rpow_mul hK hA0.le dist_nonneg htpos.le (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))) ?_
  simpa [genScale, mul_comm] using h2

end IsotropicVariance.Paper.Proofs.Profiles
