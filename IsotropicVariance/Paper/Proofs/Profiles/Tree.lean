/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.Basic
public import IsotropicVariance.Paper.Proofs.Profiles.OsTools
public import IsotropicVariance.Paper.Proofs.Profiles.TreeGeometry
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The dyadic tree of passage times: series and chains (the proof of Lemma `lem:tree`)

The tools of the dyadic tree bound, Lemma `lem:tree`, which is proved by
`Proofs.Profiles.treeStatement_holds`: the ratio `treeRatio`, the series `treeSeries`, the scales
`genScale` of the generations, the bound of a passage time by the sum over the steps of a chain
(`passTime_le_sum_chain`), and the factor of the union bound over the steps of a generation
(`union_factor_le`).
-/

@[expose] public section

open MeasureTheory Set Metric Finset
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Profiles

open Infra.Os

variable {m : ℕ}

/-! ## Constants -/

/-- `2^{−2/5}`, the decay ratio of the step scales `Q_{2^{−j} t} ≤ 2^{−2j/5} Q_t`. -/
noncomputable def treeRatio : ℝ := (2 : ℝ) ^ (-(2 / 5 : ℝ))

lemma treeRatio_pos : 0 < treeRatio := Real.rpow_pos_of_pos (by norm_num) _

lemma treeRatio_lt_one : treeRatio < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- `Σ_j (j + 1) 2^{−2j/5}`. -/
noncomputable def treeSeries : ℝ := ∑' j : ℕ, ((j : ℝ) + 1) * treeRatio ^ j

lemma summable_treeSeries : Summable fun j : ℕ => ((j : ℝ) + 1) * treeRatio ^ j := by
  have hr : ‖treeRatio‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos treeRatio_pos]; exact treeRatio_lt_one
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_lt_one treeRatio_pos.le treeRatio_lt_one
  simpa [add_mul, pow_one] using h1.add h0

lemma sum_le_treeSeries (n : ℕ) :
    ∑ j ∈ range n, ((j : ℝ) + 1) * treeRatio ^ j ≤ treeSeries :=
  summable_treeSeries.sum_le_tsum _ fun j _ => by
    have := treeRatio_pos; positivity

lemma treeSeries_pos : 0 < treeSeries := by
  have h := sum_le_treeSeries 1
  simp at h
  linarith

/-! ## The chain -/

/-- The scale `2^{−j} t` of generation `j`. -/
noncomputable def genScale (t : ℝ) (j : ℕ) : ℝ := t * ((2 : ℝ) ^ j)⁻¹

lemma genScale_pos {t : ℝ} (ht : 0 < t) (j : ℕ) : 0 < genScale t j := by
  unfold genScale; positivity

/-- Telescoping triangle inequality along a chain. -/
lemma passTime_le_sum_chain {X : Setting m} {Bd : ℝ} (hBd : ∀ ω x, X.ρ ω x ≤ Bd)
    (hBd0 : 0 ≤ Bd) (ω : X.Ω) (p : ℕ → Pt m) (n : ℕ) :
    X.passTime ω (p 0) (p n) ≤ ∑ j ∈ range n, X.passTime ω (p j) (p (j + 1)) := by
  induction n with
  | zero =>
    simp only [range_zero, sum_empty]
    have := passTime_le_mul_dist hBd hBd0 ω (p 0) (p 0)
    rwa [dist_self, mul_zero] at this
  | succ n ih =>
    rw [sum_range_succ]
    exact (passTime_triangle hBd ω _ (p n) _).trans (add_le_add_left ih _)

lemma inv_two_pow_succ (j : ℕ) : ((2 : ℝ) ^ (j + 1))⁻¹ = ((2 : ℝ) ^ j)⁻¹ / 2 := by
  rw [pow_succ, mul_inv]; ring

lemma sum_inv_two_pow_le (n : ℕ) : ∑ j ∈ range n, ((2 : ℝ) ^ j)⁻¹ ≤ 2 := by
  have := sum_geometric_two_le n
  simpa [one_div, inv_pow] using this

/-- The union bound costs at most `4 d (j + 1)` at generation `j`. -/
lemma union_factor_le (m j : ℕ) {c : ℕ} (hc : c ≤ 2 ^ ((2 * j + 1) * (m + 1))) :
    2 / Real.log 2 * Real.log (2 + c) ≤ 4 * (m + 1) * (j + 1) := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  set n := (2 * j + 1) * (m + 1) with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : (2 : ℝ) + c ≤ 2 ^ (n + 1) := by
    have : (c : ℝ) ≤ 2 ^ n := by exact_mod_cast hc
    have h2n : (2 : ℝ) ≤ 2 ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn1
    rw [pow_succ]; linarith
  have hlog : Real.log (2 + c) ≤ (n + 1) * Real.log 2 := by
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this
  rw [div_mul_eq_mul_div, div_le_iff₀ hl]
  have hnr : ((n : ℝ) + 1) ≤ 2 * (m + 1) * (j + 1) := by
    rw [hn]; push_cast; nlinarith
  nlinarith

end IsotropicVariance.Paper.Proofs.Profiles
