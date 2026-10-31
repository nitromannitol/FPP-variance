/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Asymptotics in the size `N`

The smallness requirements of Lemma `lem:slabs` hold for `N` large: `N^{-r} ≤ ε` and
`N^{-r} log N ≤ ε` eventually for `r > 0` (`exists_nat_rpow_neg_le`,
`exists_nat_rpow_neg_mul_log_le`), and `log N ≥ 1` for `N ≥ 3` (`one_le_log_of_three_le`).
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace CurvatureVariance.Paper.Proofs.Geometry

theorem exists_nat_rpow_neg_le {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) ^ (-r) ≤ ε := by
  have h := ((tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop).eventually
    (Iic_mem_nhds hε)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 h
  exact ⟨N₀, fun N hN => hN₀ N hN⟩

theorem exists_nat_rpow_neg_mul_log_le {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) ^ (-r) * Real.log N ≤ ε := by
  have h := ((isLittleO_log_rpow_atTop hr).def hε).and (eventually_gt_atTop (0 : ℝ))
  obtain ⟨X, hX⟩ := eventually_atTop.1 h
  refine ⟨⌈X⌉₊, fun N hN => ?_⟩
  have hNX : X ≤ N := (Nat.le_ceil X).trans (by exact_mod_cast hN)
  obtain ⟨h1, h2⟩ := hX N hNX
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos h2 r)] at h1
  have hlog : Real.log N ≤ ε * (N : ℝ) ^ r := (le_abs_self _).trans h1
  rw [Real.rpow_neg h2.le]
  calc ((N : ℝ) ^ r)⁻¹ * Real.log N ≤ ((N : ℝ) ^ r)⁻¹ * (ε * (N : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 (Real.rpow_nonneg h2.le r))
    _ = ε := by field_simp

theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hx

end CurvatureVariance.Paper.Proofs.Geometry
