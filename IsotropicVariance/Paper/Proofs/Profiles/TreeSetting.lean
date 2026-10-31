/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.Tree
public import IsotropicVariance.Paper.Proofs.Profiles.Scales
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The tree bound, equation `eq:tree`, for a setting

Lemma `lem:tree` and the proof of Proposition `prop:profiles`: the tree bound has `κ = Q_t`,
`w = 16√d W_t` (so `w² = 256 d t Q_t`), once every step `(p, q)` of length between `5` and a bound
`L` satisfies `T(p, q) − |q − p| ≤ O_1(C_s Q_{|q−p|})`. The steps are controlled by the induction
hypothesis (equation `eq:premise`) with stationarity and isotropy when `|q − p| ≤ N/2`
(`steps_of_premise`).
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Profiles

open Cited Infra.Os

variable {m : ℕ}

lemma treeRatio_pow (j : ℕ) : treeRatio ^ j = (((2 : ℝ) ^ j)⁻¹) ^ (2 / 5 : ℝ) := by
  rw [treeRatio, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    Real.inv_rpow (by positivity), ← Real.rpow_natCast 2 j, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_neg (by norm_num)]
  ring_nf

lemma genScale_le {t : ℝ} (ht : 0 ≤ t) (j : ℕ) : genScale t j ≤ t := by
  unfold genScale
  have : ((2 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  nlinarith

/-- `w = 16√d W_t` satisfies `w² = 256 d t Q_t`. -/
lemma sq_tubeWidth {K : ℕ} {A t : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t) :
    (16 * Real.sqrt (m + 1) * W K A t) ^ 2 = 256 * (m + 1) * t * Q K A t := by
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), W_sq hA ht]
  ring

/-- Steps of length at most `N/2` from the induction hypothesis (equation `eq:premise`) with
stationarity and isotropy (the proof of Lemma `lem:tree`). -/
theorem steps_of_premise {X : Setting m} (hm : 1 ≤ m) {K : ℕ} {A N : ℝ} (hA : 0 < A)
    (hP : Premise X K A N) (p q : Pt m) (h1 : 1 ≤ dist p q) (h2 : dist p q ≤ N / 2) :
    IsOs X.P 1 (1 * Q K A (dist p q)) fun ω => X.passTime ω p q - dist p q := by
  rw [one_mul]
  have H := isOs_passTime_of_TRV hm (f := fun y => |y - dist p q|)
    (by fun_prop) p q (hP (dist p q) h1 h2)
  exact IsOs.mono H zero_le_one (Q_pos hA (by linarith)) ((aemeasurable_passTime p q).sub_const _)
    (ae_of_all _ fun ω => le_abs_self _)

/-- The scale of a step controlled by the parent bound (equation `eq:parent`). -/
noncomputable def parentStepConst (C : ℝ) : ℝ := 1 / 100 + (C + 1) / Real.log 2

end IsotropicVariance.Paper.Proofs.Profiles
