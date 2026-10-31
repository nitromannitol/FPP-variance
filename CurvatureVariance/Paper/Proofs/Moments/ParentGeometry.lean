/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.ParentTuples
public import CurvatureVariance.Statements.Inputs.L1Norm
import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The reduction of Lemma `lem:parent` to `M` slabs: geometry

The proof of Lemma `lem:parent`: for `κN ≤ ℓ ≤ 3N` and `|y − ℓt₀| ≤ 2ℓ^{3/4+δ/100}`, let
`s = ⌊ℓ/M⌋`, and compare the passage time to `(ℓ, y)` with that to the endpoint `(Ms, Mst)` of `M`
slabs of width `s`. Then:

* `pathBound m M |t₀| = (m + 1)((M + 1)(|t₀| + 1) + 2√m)` bounds the number of edges of the
  coordinate path from `(Ms, Mst)` to `(ℓ, y)`, for `ℓ ≥ 32`;
* `l1Norm_parent_le`, `abs_round_le`: `|(Ms, Mst)|₁ + 1 ≤ (m + 2)(1 + |t₀|) ℓ` and
  `|Mst|_∞ ≤ (1 + |t₀|) Ms`;
* `sqrt_le_parentS`: `s ≥ √N` once `√N ≥ 2M/κ + 1`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Moments.Parent

open CurvatureVariance.Paper

variable {m : ℕ}

/-- The bound `(m + 1)((M + 1)(τ + 1) + 2√m)` on the length of the coordinate path from
`(Ms, Mst)` to `(ℓ, y)`, with `τ = |t₀|`. -/
noncomputable def pathBound (m Ms : ℕ) (τ : ℝ) : ℝ :=
  (m + 1) * ((Ms + 1) * (τ + 1) + 2 * Real.sqrt m)

theorem pathBound_nonneg (m Ms : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ pathBound m Ms τ := by
  unfold pathBound; positivity

section

variable {M : Model m}

/-- `ℓ^{δ/100−1/4} ≤ 1/2` for `ℓ ≥ 32`. -/
theorem rpow_e_le_half (hM : M.Standing) {ℓ : ℝ} (hℓ : 32 ≤ ℓ) :
    ℓ ^ (M.δ / 100 - 1 / 4) ≤ 1 / 2 := by
  have hδ1 := hM.delta_le_one
  have h1 : ℓ ^ (M.δ / 100 - 1 / 4) ≤ ℓ ^ (-(1 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : ℓ ^ (-(1 / 5 : ℝ)) ≤ (32 : ℝ) ^ (-(1 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hℓ (by norm_num)
  have h3 : (32 : ℝ) ^ (-(1 / 5 : ℝ)) = 1 / 2 := by
    rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), show ((5 : ℕ) : ℝ) * (-(1 / 5)) = -1 by norm_num,
      Real.rpow_neg_one]
    norm_num
  linarith

/-- `|y| ≤ 2ℓ^{3/4+δ/100}` implies `|y| ≤ ℓ` for `ℓ ≥ 32`. -/
theorem norm_le_of_le_rpow (hM : M.Standing) {ℓ : ℝ} (hℓ : 32 ≤ ℓ) {x : ℝ}
    (hx : x ≤ 2 * ℓ ^ ((3 : ℝ) / 4 + M.δ / 100)) : x ≤ ℓ := by
  have h1 := rpow_e_le_half hM hℓ
  have h2 : ℓ ^ ((3 : ℝ) / 4 + M.δ / 100) = ℓ * ℓ ^ (M.δ / 100 - 1 / 4) := by
    rw [show (3 : ℝ) / 4 + M.δ / 100 = 1 + (M.δ / 100 - 1 / 4) by ring,
      Real.rpow_add (by linarith), Real.rpow_one]
  have h3 : 0 ≤ ℓ := by linarith
  nlinarith

end

section Ratio

variable {ℓ Ms : ℕ}

theorem mul_div_le (ℓ Ms : ℕ) : Ms * (ℓ / Ms) ≤ ℓ := by
  rw [Nat.mul_comm]; exact Nat.div_mul_le_self ℓ Ms

theorem lt_mul_div_add (hMs : 0 < Ms) (ℓ : ℕ) : ℓ < Ms * (ℓ / Ms) + Ms := by
  rw [Nat.mul_comm]; exact Nat.lt_div_mul_add hMs

end Ratio

section Target

variable {M : Model m} {ℓ Ms : ℕ} {y z : Fin m → ℤ}

/-- `|x| ≤ (1 + |t₀|) ℓ` for `ℓ ≥ 32` and `|x − ℓt₀| ≤ 2ℓ^{3/4+δ/100}`. -/
theorem norm_le_of_sub_le (hM : M.Standing) {ℓ : ℝ} (hℓ : 32 ≤ ℓ) {x : EuclideanSpace ℝ (Fin m)}
    (hx : ‖x - ℓ • M.t₀‖ ≤ 2 * ℓ ^ ((3 : ℝ) / 4 + M.δ / 100)) : ‖x‖ ≤ (1 + ‖M.t₀‖) * ℓ := by
  have h1 := norm_le_of_le_rpow hM hℓ hx
  have h2 : ‖x‖ ≤ ‖x - ℓ • M.t₀‖ + ℓ * ‖M.t₀‖ := by
    calc ‖x‖ = ‖(x - ℓ • M.t₀) + ℓ • M.t₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - ℓ • M.t₀‖ + ‖ℓ • M.t₀‖ := norm_add_le _ _
      _ = ‖x - ℓ • M.t₀‖ + ℓ * ‖M.t₀‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by linarith)]
  linarith

/-- The coordinates of a point within `2L^{1+(δ/100−1/4)}` of `Lt₀` are at most `(1 + |t₀|) L`,
for `L ≥ 32`. -/
theorem abs_round_le (hM : M.Standing) {L : ℕ} (hL : 32 ≤ L)
    (hz : ‖transversePoint z - (L : ℝ) • M.t₀‖ ≤ 2 * (L : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)))
    (k : Fin m) : |(z k : ℝ)| ≤ (1 + ‖M.t₀‖) * L := by
  have hL' : (32 : ℝ) ≤ L := by exact_mod_cast hL
  rw [show (1 : ℝ) + (M.δ / 100 - 1 / 4) = 3 / 4 + M.δ / 100 by ring] at hz
  have h1 := norm_le_of_sub_le hM hL' hz
  have h2 := ExpArray.abs_apply_le_norm (transversePoint z) k
  rw [Infra.FPP.transversePoint_apply] at h2
  linarith

/-- `|(Ms, Mst)|₁ + 1 ≤ (m + 2)(1 + |t₀|) ℓ`. -/
theorem l1Norm_parent_le (hM : M.Standing) (hℓ : 32 ≤ ℓ) (hL : 32 ≤ Ms * (ℓ / Ms))
    (hz : ‖transversePoint z - ((Ms * (ℓ / Ms) : ℕ) : ℝ) • M.t₀‖ ≤
      2 * ((Ms * (ℓ / Ms) : ℕ) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4))) :
    (l1Norm ((((Ms * (ℓ / Ms) : ℕ) : ℤ)), z) : ℝ) + 1 ≤ (m + 2) * (1 + ‖M.t₀‖) * ℓ := by
  have hℓ' : (32 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hLℓ : ((Ms * (ℓ / Ms) : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast mul_div_le ℓ Ms
  have hτ := norm_nonneg M.t₀
  have h1 : (((((Ms * (ℓ / Ms) : ℕ) : ℤ)).natAbs : ℕ) : ℝ) ≤ ℓ := by
    rw [Int.natAbs_natCast]; exact_mod_cast mul_div_le ℓ Ms
  have h2 : ∀ j, (((z j).natAbs : ℕ) : ℝ) ≤ (1 + ‖M.t₀‖) * ℓ := by
    intro j
    have := abs_round_le hM hL hz j
    have h : (((z j).natAbs : ℕ) : ℝ) = |(z j : ℝ)| := by simp
    rw [h]
    exact this.trans (mul_le_mul_of_nonneg_left hLℓ (by linarith))
  unfold l1Norm
  push_cast
  have h3 : ∑ j, (((z j).natAbs : ℕ) : ℝ) ≤ ∑ _j : Fin m, (1 + ‖M.t₀‖) * ℓ :=
    Finset.sum_le_sum fun j _ => h2 j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  push_cast at h1 h3 ⊢
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [mul_nonneg hτ (by linarith : (0 : ℝ) ≤ ℓ)]

end Target

/-- **`s ≥ √N`** (the proof of Lemma `lem:parent`): if `κN ≤ ℓ` and `√N ≥ 2M/κ + 1`, then
`⌊ℓ/M⌋ ≥ √N`. -/
theorem sqrt_le_parentS {κ : ℝ} (hκ : 0 < κ) {N ℓ Ms : ℕ} (hMs : 0 < Ms) (hℓ : κ * N ≤ ℓ)
    (hN : 2 * Ms / κ + 1 ≤ Real.sqrt N) : Real.sqrt N ≤ ((ℓ / Ms : ℕ) : ℝ) := by
  set u := Real.sqrt N with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hMs' : (0 : ℝ) < Ms := by exact_mod_cast hMs
  have hu1 : 1 ≤ u := by have : 0 ≤ 2 * (Ms : ℝ) / κ := by positivity
                         linarith
  have hNu : (N : ℝ) = u ^ 2 := by rw [hu, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h1 := lt_mul_div_add hMs ℓ
  have h2 : (ℓ : ℝ) < Ms * ((ℓ / Ms : ℕ) : ℝ) + Ms := by exact_mod_cast h1
  have h3 : κ * u ≥ 2 * Ms + κ := by
    have := mul_le_mul_of_nonneg_left hN hκ.le
    rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ _ hκ.ne', mul_one] at this
    linarith
  have h4 : κ * u ^ 2 ≥ Ms * u + Ms * u := by nlinarith
  have h5 : (Ms : ℝ) * (u + 1) ≤ Ms * ((ℓ / Ms : ℕ) : ℝ) + Ms := by
    have : (Ms : ℝ) * u + Ms * u ≥ Ms * u + Ms := by nlinarith
    rw [hNu] at hℓ
    nlinarith
  have h6 : u + 1 ≤ ((ℓ / Ms : ℕ) : ℝ) + 1 := by
    have h7 : (Ms : ℝ) * (u + 1) ≤ Ms * (((ℓ / Ms : ℕ) : ℝ) + 1) := by linarith
    exact le_of_mul_le_mul_left h7 hMs'
  linarith

end CurvatureVariance.Paper.Moments.Parent
