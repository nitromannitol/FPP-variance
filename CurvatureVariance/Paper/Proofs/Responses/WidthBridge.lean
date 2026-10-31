/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Proofs.Responses.RowGeometry
import CurvatureVariance.Paper.Proofs.Moments.Scales
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The width margin needed by the row arrays

The width-margin contract absorbs both integer rounding and the diameter of row cubes. The
large number of slabs puts the target slope strictly inside the localization range.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- The rounded width is positive whenever the amplitude and slab width are positive. -/
theorem one_le_wInt {M : Model m} {K n : ℕ} {A : ℝ} (hA : 1 ≤ A) (hn : 1 ≤ n) :
    1 ≤ wInt M K A n := by
  apply Nat.one_le_ceil_iff.mpr
  apply Real.sqrt_pos.mpr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact mul_pos hnpos (mul_pos (lt_of_lt_of_le zero_lt_one hA) (Real.rpow_pos_of_pos hnpos _))

/-- The side of the closed row cube is at most the unrounded width. -/
theorem wInt_sub_one_le_W (M : Model m) (K : ℕ) (A : ℝ) (n : ℕ) :
    (wInt M K A n : ℝ) - 1 ≤ W M K A n := by
  have h := Nat.ceil_lt_add_one (Real.sqrt_nonneg ((n : ℝ) * Q M K A n))
  change (⌈Real.sqrt ((n : ℝ) * Q M K A n)⌉₊ : ℝ) - 1 ≤ Real.sqrt ((n : ℝ) * Q M K A n)
  linarith only [h]

/-- The deviation of the target slope from `t₀` is at most half the slab-scale margin. -/
theorem targetSlope_norm_le_half {M : Model m} (hM : M.Standing) {K n ℓ : ℕ}
    (hK : 10 ^ 4 ≤ K) (hn : 1 ≤ n) (hℓ : ℓ = K * n) {y : Fin m → ℤ}
    (hy : y ∈ premiseDomain M ℓ) :
    ‖targetSlope ℓ y - M.t₀‖ ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (M.δ / 100 - 1 / 4) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hK256 : (256 : ℝ) ≤ K := by exact_mod_cast (show 256 ≤ K by omega)
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK256
  have he : M.δ / 100 - 1 / 4 ≤ (-1 / 8 : ℝ) := by linarith only [hM.delta_le_one]
  have h256 : (256 : ℝ) ^ (-1 / 8 : ℝ) = 1 / 2 := by norm_num
  have hKpow : (K : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ 1 / 2 := by
    calc
      _ ≤ (K : ℝ) ^ (-1 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith only [hK256]) he
      _ ≤ (256 : ℝ) ^ (-1 / 8 : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hK256 (by norm_num)
      _ = _ := h256
  have hlen : 1 ≤ ℓ := by
    rw [hℓ]
    exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  have ht := targetSlope_norm_le_rpow hM hlen (le_refl ℓ) hy
  rw [hℓ, Nat.cast_mul, Real.mul_rpow hKpos.le hnpos.le] at ht
  rw [hℓ]
  exact ht.trans (mul_le_mul_of_nonneg_right hKpow (Real.rpow_nonneg hnpos.le _))

/-- Equation `eq:scales` gives the deterministic rounding bound for every slab length at least
`√N`, uniformly in the amplitude, from the width margin `Moments.exists_width_margin` and
`n^{3/4+δ/100} → ∞`. -/
theorem eventually_row_width_small (h : Contracts.ScalesStatement m)
    (bd : Bounds m) (hbd : bd.Valid) (Cstar : ℝ) (K : ℕ) (hK : 10 ^ 4 ≤ K) :
    ∃ N₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd → ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
      RangeA M K A N Cstar → ∀ n : ℕ, Real.sqrt N ≤ n →
        32 * Real.sqrt m * ((wInt M K A n : ℝ) + 1) ≤
          (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hbd.law.one_le_m)
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have ha : 0 < (3 : ℝ) / 4 + bd.law.δ / 100 := by have hδ := hbd.law.delta_pos; linarith only [hδ]
  obtain ⟨Nwidth, hwidth⟩ :=
    Moments.exists_width_margin h bd hbd Cstar (η := 1 / (128 * Real.sqrt m)) (by positivity)
  have hlarge : ∀ᶠ n : ℕ in atTop,
      128 * Real.sqrt m ≤ (n : ℝ) ^ ((3 : ℝ) / 4 + bd.law.δ / 100) :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (128 * Real.sqrt m))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max Nwidth (n₀ ^ 2), ?_⟩
  intro M hM hfit N hN A hA hRange n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) ^ 2 := (Real.sqrt_le_iff.mp hn).2
  have hn0N : (n₀ : ℝ) ^ 2 ≤ N := by exact_mod_cast ((le_max_right _ _).trans hN)
  have hn0n : n₀ ≤ n := by
    have hnr : (n₀ : ℝ) ≤ n := by
      nlinarith only [hNn, hn0N, Nat.cast_nonneg (α := ℝ) n₀, Nat.cast_nonneg (α := ℝ) n]
    exact_mod_cast hnr
  have hp := hn₀ n hn0n
  rw [← hfit.δ_eq] at hp
  have hw := hwidth K hK M hM hfit N ((le_max_left _ _).trans hN) A hA hRange n
    ((div_le_self (Real.sqrt_nonneg _) (by norm_num : (1 : ℝ) ≤ 16)).trans hn)
  have hmul := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 32 * Real.sqrt m)
  have heq : 32 * Real.sqrt m * (1 / (128 * Real.sqrt m) *
      (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)) =
      (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 4 := by field_simp; ring
  rw [heq] at hmul
  have hceil := (Nat.ceil_lt_add_one (Real.sqrt_nonneg ((n : ℝ) * Q M K A n))).le
  change (wInt M K A n : ℝ) ≤ W M K A n + 1 at hceil
  nlinarith only [hmul, hceil, hp, hsqrt.le]

end CurvatureVariance.Paper.Responses
