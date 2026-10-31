/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The chains of equation `eq:F` exist

`chainsExistStatement_holds`: the contract `ChainsExistStatement`, the sentence "Chains exist, since
the points of `ℤ^d` to which the points `u + in(1,t)` are rounded form one" (the text after
equation `eq:F`).

A point `x` is rounded to the point with the coordinates `⌈x·e_j − 1/2⌉` (the beginning of
Section `sec:prelim`), so a coordinate moves by at most `1/2`, and the increments of the rounded
points are within `(d − 1)^{1/2}` of `n(1, t)`. The chain is admissible since
`(64d)^{3/4}/16 ≥ d^{1/2}`.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

variable {m : ℕ}

/-- The paper's rounding, one coordinate: `x − 1/2 ≤ ⌈x − 1/2⌉ < x + 1/2`. -/
theorem round_coord_bounds (x : ℝ) :
    x - 1 / 2 ≤ (⌈x - 1 / 2⌉ : ℝ) ∧ (⌈x - 1 / 2⌉ : ℝ) < x + 1 / 2 := by
  have h1 := Int.le_ceil (x - 1 / 2)
  have h2 := Int.ceil_lt_add_one (x - 1 / 2)
  exact ⟨h1, by linarith only [h2]⟩

/-- The paper's rounding fixes integers. -/
theorem ceil_sub_half_intCast (k : ℤ) : ⌈(k : ℝ) - 1 / 2⌉ = k := by
  rw [Int.ceil_eq_iff]
  constructor <;> linarith only

/-- The bound of the increments of the rounded chain: `n ≥ 64 d` gives
`16 (d−1)^{1/2} ≤ n^{3/4}`. -/
theorem sixteen_mul_sqrt_le_rpow {n : ℕ} (hn : 64 * (m + 1) ≤ n) :
    16 * Real.sqrt m ≤ (n : ℝ) ^ ((3 : ℝ) / 4) := by
  have hn' : 64 * ((m : ℝ) + 1) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn0 : (0 : ℝ) < n := by linarith only [hn', hm0]
  have hA : 0 ≤ 16 * Real.sqrt m := by positivity
  have hB : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hn0.le _
  refine (pow_le_pow_iff_left₀ hA hB (by norm_num : (4 : ℕ) ≠ 0)).1 ?_
  have e1 : ((n : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 = (n : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, ← Real.rpow_natCast]
    norm_num
  have e2 : (16 * Real.sqrt m) ^ 4 = 65536 * (m : ℝ) ^ 2 := by
    have h := Real.sq_sqrt hm0
    calc (16 * Real.sqrt m) ^ 4 = 65536 * (Real.sqrt m ^ 2) ^ 2 := by ring
      _ = 65536 * (m : ℝ) ^ 2 := by rw [h]
  rw [e1, e2]
  have h3 : (64 * ((m : ℝ) + 1)) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hn' 3
  nlinarith only [h3, hm0, sq_nonneg (m : ℝ), mul_nonneg hm0 (sq_nonneg (m : ℝ))]

/-- **The chains of equation `eq:F` exist** (the text after equation `eq:F`): the rounded points of
`u + in(1, t)`, whose increments are within `(d − 1)^{1/2}` of `n(1, t)`. -/
theorem chainsExistStatement_holds (m : ℕ) : ChainsExistStatement m := by
  intro M hM Ms n hMs hn t u v huv
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  -- the transverse coordinates of `v`
  have hv : ∀ j, (v.2 j : ℝ) = (u.2 j : ℝ) + (Ms : ℝ) * n * t j := by
    intro j
    have h := congrArg (fun w : Pt m => w.snd j) huv
    simp only [point, slopeVec] at h
    have h' : (v.2 j : ℝ) - u.2 j = (Ms : ℝ) * n * t j := by simpa using h
    linarith only [h']
  set y : Fin (Ms + 1) → Fin m → ℤ := fun i j => ⌈(u.2 j : ℝ) + (i : ℝ) * n * t j - 1 / 2⌉ with hy
  have hinc : ∀ i : Fin Ms,
      ‖transversePoint (y i.succ - y i.castSucc) - (n : ℝ) • t‖ ≤ Real.sqrt m := by
    intro i
    rw [← mul_one (Real.sqrt m)]
    refine Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le zero_le_one fun c => ?_
    have e : (u.2 c : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) * n * t c =
        (u.2 c : ℝ) + (i : ℝ) * n * t c + n * t c := by
      push_cast; ring
    obtain ⟨f1, f2⟩ := round_coord_bounds ((u.2 c : ℝ) + (i : ℝ) * n * t c)
    obtain ⟨f3, f4⟩ := round_coord_bounds ((u.2 c : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) * n * t c)
    simp only [hy, PiLp.sub_apply, PiLp.smul_apply, Infra.FPP.transversePoint_apply,
      Pi.sub_apply, Int.cast_sub, smul_eq_mul, Fin.val_succ, Fin.val_castSucc]
    rw [abs_le]
    constructor <;> linarith only [f1, f2, f3, f4, e]
  refine ⟨y, ⟨?_, ?_, fun i => (hinc i).trans ?_⟩, hinc⟩
  · funext j
    simp only [hy, Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
    exact ceil_sub_half_intCast _
  · funext j
    simp only [hy, Fin.val_last]
    rw [← hv j]
    exact ceil_sub_half_intCast _
  · have h1 := sixteen_mul_sqrt_le_rpow hn
    have h2 : (n : ℝ) ^ ((3 : ℝ) / 4) ≤ (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hM.delta_pos])
    linarith only [h1, h2]

end CurvatureVariance.Paper.Proofs.Geometry
