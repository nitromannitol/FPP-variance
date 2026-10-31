/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.FAClip
public import CurvatureVariance.Paper.Proofs.Gain.FARate
public import CurvatureVariance.Paper.Proofs.Gain.FACore
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The functions of `L` in the finite approximation of Lemma `lem:labels`

Quantities of the finite approximation, equation `eq:labelprofile`, that depend only on `L` and on
the dimension, never on `K`, `N`, `A`, the target, the subgradient, the slab, the offset or the
block:

* `faExp m = 8d`, `d = m + 1`: the exponent `k` (`one_le_faExp`);
* `faStep L = 1/(L + 1)`: the quantization step, the clipping error and the merging error
  (`faStep_pos`);
* `labelAlphabet_card_pos`: the alphabet of quantized clipped vectors is nonempty;
* `pow_mul_mul_one_div_eq`, `rpow_one_div_two_mul_pow`: two identities of exponents.
-/

@[expose] public section

open Filter Topology

namespace CurvatureVariance.Paper.Gain

/-- The exponent `k = 8d` of equation `eq:labelprofile`, `d = m + 1`. -/
abbrev faExp (m : ℕ) : ℕ := 8 * (m + 1)

/-- The step `1/(L + 1)`: the quantization step, the clipping error and the merging error. -/
noncomputable def faStep (L : ℕ) : ℝ := 1 / ((L : ℝ) + 1)

variable {m : ℕ}

theorem faStep_pos (L : ℕ) : 0 < faStep L := by
  unfold faStep
  positivity

theorem one_le_faExp (m : ℕ) : 1 ≤ faExp m := by
  unfold faExp
  omega

/-- The alphabet of quantized clipped vectors is nonempty. -/
theorem labelAlphabet_card_pos {S : Type*} [Fintype S] [DecidableEq S] {B ξ : ℝ} (hB : 0 ≤ B)
    (hξ : 0 < ξ) : 0 < (labelAlphabet S B ξ).card := by
  refine Finset.card_pos.mpr (Fintype.piFinset_nonempty.mpr fun _ => Finset.nonempty_Icc.mpr ?_)
  refine Int.floor_mono (div_le_div_of_nonneg_right ?_ hξ.le)
  linarith

/-- `b^k |Λ| / ((X b)^k |Λ|) = X^{−k}`. -/
theorem pow_mul_mul_one_div_eq {b X c : ℝ} (hb : 0 < b) (hX : 0 < X) (hc : 0 < c) (k : ℕ) :
    b ^ k * (c * (1 / ((X * b) ^ k * c))) = (1 / X) ^ k := by
  rw [mul_pow, one_div_pow]
  field_simp

/-- `((x)^{1/(2k)})^k = √x` for `x ≥ 0`. -/
theorem rpow_one_div_two_mul_pow {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    (x ^ (1 / (2 * k : ℝ))) ^ k = Real.sqrt x := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, Real.sqrt_eq_rpow]
  congr 1
  field_simp

end CurvatureVariance.Paper.Gain
