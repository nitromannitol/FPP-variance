/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.ModulusCover
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The scales of equation `eq:modulus`

The proof of equation `eq:modulus` at the mesh `h` uses the cut ratio `cutRatio h = h^{1/3}` (the
`γ` of the proof of Lemma `lem:modulus`), the tube ratio `tubeRatio h = h^{−1/3}` and the radius
`boxRadius m h` of the index box of the small cubes.
-/

@[expose] public section

open Filter Topology Set

namespace IsotropicVariance.Paper.Proofs.Modulus

/-- The cut ratio `κ = h^{1/3}`. -/
noncomputable def cutRatio (h : ℝ) : ℝ := h ^ (1 / 3 : ℝ)

/-- The tube ratio `Λ = h^{-1/3}`. -/
noncomputable def tubeRatio (h : ℝ) : ℝ := h ^ (-(1 / 3 : ℝ))

/-- The radius of the index box of the small cubes. -/
noncomputable def boxRadius (m : ℕ) (h : ℝ) : ℕ :=
  ⌈(3 / 2 * tubeRatio h + 4 * Real.sqrt m) * cutRatio h ^ (-(3 / 4 : ℝ))⌉₊ + 1

lemma card_box (m L : ℕ) : (box m L).card = (2 * L + 1) ^ m := by
  rw [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Icc]
  congr 1
  omega

lemma cutRatio_pos {h : ℝ} (hh : 0 < h) : 0 < cutRatio h := Real.rpow_pos_of_pos hh _

lemma cutRatio_le_half {h : ℝ} (hh : 0 < h) (h8 : h ≤ 1 / 8) : cutRatio h ≤ 1 / 2 := by
  have e : ((1 / 2 : ℝ) ^ 3) ^ (1 / 3 : ℝ) = 1 / 2 := by
    rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  calc cutRatio h = h ^ (1 / 3 : ℝ) := rfl
    _ ≤ ((1 / 2 : ℝ) ^ 3) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hh.le (by norm_num; linarith) (by norm_num)
    _ = 1 / 2 := e

lemma one_le_tubeRatio {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) : 1 ≤ tubeRatio h :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh h1 (by norm_num)

lemma tubeRatio_eq_inv {h : ℝ} (hh : 0 < h) : tubeRatio h = (cutRatio h)⁻¹ :=
  Real.rpow_neg hh.le _

/-- The logarithm of the number of pairs of small cubes is at most `c₀ − 4m log κ`. -/
lemma log_card_box_le (m : ℕ) {h : ℝ} (hh : 0 < h) (h8 : h ≤ 1 / 8) :
    Real.log (2 + 4 * ((box m (boxRadius m h)).card : ℝ) ^ 2) ≤
      (Real.log 6 + 2 * m * Real.log (2 * (3 / 2 + 4 * Real.sqrt m + 2) + 1)) -
        4 * m * Real.log (cutRatio h) := by
  set κ := cutRatio h with hκdef
  set c : ℝ := 3 / 2 + 4 * Real.sqrt m + 2 with hcdef
  have hκ : 0 < κ := cutRatio_pos hh
  have hκ1 : κ ≤ 1 := (cutRatio_le_half hh h8).trans (by norm_num)
  have hΛ : tubeRatio h = κ⁻¹ := tubeRatio_eq_inv hh
  have hΛ1 : 1 ≤ κ⁻¹ := (one_le_inv₀ hκ).mpr hκ1
  have hsq := Real.sqrt_nonneg (m : ℝ)
  -- `L ≤ c Λ²`
  set L := boxRadius m h with hLdef
  have hpow : κ ^ (-(3 / 4 : ℝ)) ≤ κ⁻¹ := by
    rw [Real.rpow_neg hκ.le]
    refine inv_anti₀ hκ ?_
    have := Real.rpow_le_rpow_of_exponent_ge hκ hκ1 (show (3 / 4 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have hy0 : 0 ≤ (3 / 2 * tubeRatio h + 4 * Real.sqrt m) * κ ^ (-(3 / 4 : ℝ)) := by
    rw [hΛ]
    have := Real.rpow_nonneg hκ.le (-(3 / 4 : ℝ))
    positivity
  have hL : (L : ℝ) ≤ c * κ⁻¹ ^ 2 := by
    have hceil := Nat.ceil_lt_add_one hy0
    have hLr : (L : ℝ) = (⌈(3 / 2 * tubeRatio h + 4 * Real.sqrt m) *
        κ ^ (-(3 / 4 : ℝ))⌉₊ : ℝ) + 1 := by
      simp only [hLdef, boxRadius, Nat.cast_add, Nat.cast_one]
      rfl
    rw [hLr]
    rw [hΛ] at hceil ⊢
    have h1 : (3 / 2 * κ⁻¹ + 4 * Real.sqrt m) * κ ^ (-(3 / 4 : ℝ)) ≤
        (3 / 2 * κ⁻¹ + 4 * Real.sqrt m) * κ⁻¹ :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have hΛsq : κ⁻¹ ≤ κ⁻¹ ^ 2 := by nlinarith
    have h2 : 1 ≤ κ⁻¹ ^ 2 := one_le_pow₀ hΛ1
    have h3 : Real.sqrt m * κ⁻¹ ≤ Real.sqrt m * κ⁻¹ ^ 2 := mul_le_mul_of_nonneg_left hΛsq hsq
    simp only [hcdef]
    nlinarith
  have hx1 : (1 : ℝ) ≤ 2 * (L : ℝ) + 1 := by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith
  have hx : 2 * (L : ℝ) + 1 ≤ (2 * c + 1) * κ⁻¹ ^ 2 := by
    have : 1 ≤ κ⁻¹ ^ 2 := one_le_pow₀ hΛ1
    nlinarith
  have hcard : ((box m L).card : ℝ) = (2 * (L : ℝ) + 1) ^ m := by
    rw [card_box]
    push_cast
    ring
  have hcard1 : (1 : ℝ) ≤ ((box m L).card : ℝ) := by
    rw [hcard]
    exact one_le_pow₀ hx1
  have hc0 : 0 < 2 * c + 1 := by positivity
  calc Real.log (2 + 4 * ((box m L).card : ℝ) ^ 2)
      ≤ Real.log (6 * ((box m L).card : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
    _ = Real.log 6 + 2 * m * Real.log (2 * (L : ℝ) + 1) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hcard, Real.log_pow]
        push_cast
        ring
    _ ≤ Real.log 6 + 2 * m * Real.log ((2 * c + 1) * κ⁻¹ ^ 2) := by
        gcongr
    _ = (Real.log 6 + 2 * m * Real.log (2 * c + 1)) - 4 * m * Real.log κ := by
        rw [Real.log_mul hc0.ne' (by positivity), Real.log_pow, Real.log_inv]
        push_cast
        ring

end IsotropicVariance.Paper.Proofs.Modulus
