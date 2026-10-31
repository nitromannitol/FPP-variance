/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Numerics of the continuity estimate (Lemma `lem:modulus`)

The grid size `n(T, b, g)` of the covering by cubes of side `W_{gℓ}`, for slopes `|t| ≤ T`, the
bound `g^{1/3} log(2 + (2n+1)^{2m}) ≤ (2m+1)(log(11T(b+3)) + 12) g^{1/6}` on the cost of the finite
maximum (the term `g^{1/3} log(2/g)` of the bound `C(b)(g + g^{1/3} log(2/g)) Q_ℓ` in the proof of
Lemma `lem:modulus`), and the constant `K₀` with total bound `K₀ g^{1/6} Q_ℓ`. The slope bound
`T = T₀ + 1`, with `T₀ = bd.T` a bound for `|t₀|`, depends only on the bounds `bd`.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Localization.Modulus

/-- The grid size `n(T, b, g) = ⌈T (2/g + b + 1)(2/g)⌉ + 1`. -/
noncomputable def gridSize (T b g : ℝ) : ℕ := ⌈T * (2 / g + b + 1) * (2 / g)⌉₊ + 1

theorem le_gridSize (T b g : ℝ) : T * (2 / g + b + 1) * (2 / g) + 1 / 2 ≤ gridSize T b g := by
  unfold gridSize
  push_cast
  have := Nat.le_ceil (T * (2 / g + b + 1) * (2 / g))
  linarith only [this]

/-- `log(1/g) ≤ 6 g^{−1/6}`. -/
theorem log_inv_le {g : ℝ} (hg : 0 < g) : Real.log g⁻¹ ≤ 6 * g⁻¹ ^ ((1 : ℝ) / 6) := by
  have h1 : Real.log (g⁻¹ ^ ((1 : ℝ) / 6)) = 1 / 6 * Real.log g⁻¹ :=
    Real.log_rpow (inv_pos.mpr hg) _
  have h2 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (inv_pos.mpr hg) ((1 : ℝ) / 6))
  linarith only [h1, h2]

/-- The constant `c_p = 2(1 + p!)` of the `L^p` bounds, at `p = 8(m+1)`. -/
noncomputable def momentConst (p : ℕ) : ℝ := 2 * (1 + (p.factorial : ℝ))

theorem momentConst_pos (p : ℕ) : 0 < momentConst p := by unfold momentConst; positivity

end CurvatureVariance.Paper.Localization.Modulus
