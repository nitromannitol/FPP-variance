/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Targets
import CurvatureVariance.Infra.FPP.Lattice
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Elementary bounds on the scales of Section `sec:gain`

These bounds are used in the proof of Lemma `lem:labels`. For a target `(ℓ, y)` of Section
`sec:gain` (`ℓ = K n`, `N/9 ≤ ℓ ≤ N`, `|y − ℓ t₀| ≤ ℓ^{3/4+δ/100}`) and `K ≥ 10⁴`, `A ≥ 1`:

* `IsTarget.div_le_n`, `IsTarget.n_le`: `N/(9K) ≤ n ≤ N`;
* `norm_targetSlope_le_half`: `|t − t₀| ≤ ½ n^{δ/100 − 1/4}` (`K^{δ/100−1/4} ≤ ½`);
* `rpow_le_Q`, `one_le_W`, `wInt_le_two_mul_W`, `one_le_wInt`: `n^{1/4} ≤ Q_n`, `1 ≤ W_n`,
  `⌈W_n⌉ ≤ 2 W_n` (for `n ≥ 1`);
* `exists_log_sq_add_le`: `a log² N + b ≤ (N/c)^{1/4}` for `N` large.
-/

@[expose] public section

open Set
open scoped NNReal

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-- A target has `N/(9K) ≤ n`. -/
theorem IsTarget.div_le_n {M : Model m} {K N n ℓ : ℕ} {y : Fin m → ℤ}
    (hT : IsTarget M K N n ℓ y) (hK : 1 ≤ K) : (N : ℝ) / (9 * K) ≤ n := by
  obtain ⟨hℓ, h1, -, -⟩ := hT
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_le_iff₀ (by positivity)]
  have : (ℓ : ℝ) = K * n := by exact_mod_cast hℓ
  nlinarith

/-- A target has `n ≤ N`. -/
theorem IsTarget.n_le {M : Model m} {K N n ℓ : ℕ} {y : Fin m → ℤ}
    (hT : IsTarget M K N n ℓ y) (hK : 1 ≤ K) : n ≤ N := by
  obtain ⟨hℓ, -, h2, -⟩ := hT
  have : n ≤ ℓ := by rw [hℓ]; exact Nat.le_mul_of_pos_left n hK
  omega

/-- `K^{δ/100 − 1/4} ≤ 1/2` for `K ≥ 10⁴` and `δ ≤ 1`. -/
theorem rpow_K_le_half {δ : ℝ} (hδ : δ ≤ 1) {K : ℕ} (hK : 10 ^ 4 ≤ K) :
    (K : ℝ) ^ (δ / 100 - 1 / 4) ≤ 1 / 2 := by
  have hK1 : (32 : ℝ) ≤ K := by
    have : (32 : ℕ) ≤ K := le_trans (by norm_num) hK
    exact_mod_cast this
  have h1 : (K : ℝ) ^ (δ / 100 - 1 / 4) ≤ (K : ℝ) ^ (-(1 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (2 : ℝ) ≤ (K : ℝ) ^ (1 / 5 : ℝ) := by
    have h32 : ((32 : ℝ)) ^ (1 / 5 : ℝ) = 2 := by
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, one_div,
        show ((5 : ℝ)) = ((5 : ℕ) : ℝ) by norm_num, Real.pow_rpow_inv_natCast (by norm_num)
        (by norm_num)]
    rw [← h32]
    exact Real.rpow_le_rpow (by norm_num) hK1 (by norm_num)
  rw [Real.rpow_neg (by linarith)] at h1
  refine h1.trans ?_
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

/-- **The slope of a target**: `|t − t₀| ≤ ½ n^{δ/100 − 1/4}` (`K ≥ 10⁴`). -/
theorem norm_targetSlope_le_half {M : Model m} (hM : M.Standing) {K N n ℓ : ℕ}
    {y : Fin m → ℤ} (hK : 10 ^ 4 ≤ K) (hT : IsTarget M K N n ℓ y) (hn : 1 ≤ n) :
    ‖targetSlope ℓ y - M.t₀‖ ≤ 1 / 2 * (n : ℝ) ^ (M.δ / 100 - 1 / 4) := by
  obtain ⟨hℓ, -, -, hy⟩ := hT
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have hℓ1 : (1 : ℝ) ≤ ℓ := by
    have : 1 ≤ ℓ := by rw [hℓ]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hℓeq : (ℓ : ℝ) = K * n := by exact_mod_cast hℓ
  have hy' : ‖transversePoint y - (ℓ : ℝ) • M.t₀‖ ≤ (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := hy
  rw [Responses.targetSlope_sub_eq (by exact_mod_cast hℓ1), norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  calc (ℓ : ℝ)⁻¹ * ‖transversePoint y - (ℓ : ℝ) • M.t₀‖ ≤
        (ℓ : ℝ)⁻¹ * (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) :=
        mul_le_mul_of_nonneg_left hy' (by positivity)
    _ = (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) := by
        rw [show M.δ / 100 - 1 / 4 = ((3 : ℝ) / 4 + M.δ / 100) - 1 by ring,
          Real.rpow_sub_one (by positivity), inv_mul_eq_div]
    _ = (K : ℝ) ^ (M.δ / 100 - 1 / 4) * (n : ℝ) ^ (M.δ / 100 - 1 / 4) := by
        rw [hℓeq, Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ 1 / 2 * (n : ℝ) ^ (M.δ / 100 - 1 / 4) :=
        mul_le_mul_of_nonneg_right (rpow_K_le_half hM.delta_le_one hK) (by positivity)

/-- **`Q_n ≥ n^{1/4}`** for `n ≥ 1`, `A ≥ 1`, `K ≥ 10⁴`. -/
theorem rpow_le_Q {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) ^ (1 / 4 : ℝ) ≤ Q M K A n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK' : (10 ^ 4 : ℝ) ≤ K := by exact_mod_cast hK
  have hδK : M.δ / K ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith [hM.delta_le_one]
  have h1 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  unfold Q
  exact h1.trans (le_mul_of_one_le_left (by positivity) hA)

/-- `Q_n ≥ 1` for `n ≥ 1`. -/
theorem one_le_Q {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ Q M K A n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact (Real.one_le_rpow hn1 (by norm_num)).trans (rpow_le_Q hM hK hA hn)

/-- `W_n ≥ 1` for `n ≥ 1`. -/
theorem one_le_W {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ W M K A n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ := one_le_Q hM hK hA hn
  unfold W
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- `⌈W_n⌉ ≤ 2 W_n` for `n ≥ 1`. -/
theorem wInt_le_two_mul_W {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {n : ℕ} (hn : 1 ≤ n) : (wInt M K A n : ℝ) ≤ 2 * W M K A n := by
  have hW := one_le_W hM hK hA hn
  have h := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ W M K A n)
  unfold wInt
  linarith

/-- `⌈W_n⌉ ≥ 1` for `n ≥ 1`. -/
theorem one_le_wInt {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ wInt M K A n := by
  have hW := one_le_W hM hK hA hn
  unfold wInt
  exact Nat.one_le_iff_ne_zero.mpr fun h => by
    rw [Nat.ceil_eq_zero] at h
    linarith

/-- **`log² N = o(N^{1/4})`**: `a log² N + b ≤ (N/c)^{1/4}` for `N` large. -/
theorem exists_log_sq_add_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → a * Real.log N ^ 2 + b ≤ ((N : ℝ) / c) ^ (1 / 4 : ℝ) := by
  set Y : ℝ := c ^ (1 / 4 : ℝ) * (256 * a + b) + 1 with hY
  have hY1 : 1 ≤ Y := by
    have : 0 ≤ c ^ (1 / 4 : ℝ) * (256 * a + b) := by positivity
    linarith
  refine ⟨⌈Y ^ (8 : ℕ)⌉₊ + 1, fun N hN => ?_⟩
  have hN' : Y ^ (8 : ℕ) ≤ (N : ℝ) := by
    have h1 := Nat.le_ceil (Y ^ (8 : ℕ))
    have h2 : ((⌈Y ^ (8 : ℕ)⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (Nat.le_succ _).trans hN
    linarith
  have hN1 : (1 : ℝ) ≤ N := le_trans (one_le_pow₀ hY1) hN'
  set X : ℝ := (N : ℝ) ^ (1 / 8 : ℝ) with hX
  have hXY : Y ≤ X := by
    have := Real.rpow_le_rpow (by positivity) hN' (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast
      (by positivity) (by norm_num)] at this
    rw [hX, show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num]
    exact this
  have hX1 : 1 ≤ X := hY1.trans hXY
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlog : Real.log N ≤ 16 * (N : ℝ) ^ (1 / 16 : ℝ) := by
    have := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ N) (by norm_num : (0 : ℝ) < 1 / 16)
    linarith [show (N : ℝ) ^ (1 / 16 : ℝ) / (1 / 16) = 16 * (N : ℝ) ^ (1 / 16 : ℝ) by ring]
  have hsq16 : ((N : ℝ) ^ (1 / 16 : ℝ)) ^ 2 = X := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hlog2 : Real.log N ^ 2 ≤ 256 * X := by
    have := pow_le_pow_left₀ hlog0 hlog 2
    rw [mul_pow, hsq16] at this
    linarith
  have hsq8 : X ^ 2 = (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hc4 : 0 < c ^ (1 / 4 : ℝ) := by positivity
  rw [Real.div_rpow (by positivity) hc.le, ← hsq8, le_div_iff₀ hc4]
  have h1 : c ^ (1 / 4 : ℝ) * (256 * a + b) ≤ X := by linarith
  have h2 : (a * Real.log N ^ 2 + b) ≤ 256 * a * X + b * X := by
    have := mul_le_mul_of_nonneg_left hlog2 ha
    nlinarith
  calc (a * Real.log N ^ 2 + b) * c ^ (1 / 4 : ℝ) ≤ (256 * a * X + b * X) * c ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right h2 hc4.le
    _ = X * (c ^ (1 / 4 : ℝ) * (256 * a + b)) := by ring
    _ ≤ X * X := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = X ^ 2 := by ring

end CurvatureVariance.Paper.Gain
