/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.MeshPairs
public import IsotropicVariance.Paper.Proofs.SlabComparison.Logarithms

/-! # Polynomial bounds for the containing-cube mesh -/

@[expose] public section
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

/-- The number of mesh pairs in the `R³` cube is bounded by one fixed polynomial in `2+R`. -/
theorem card_meshPairs_polynomial {R : ℝ} (hR : 1 ≤ R) (z : Pt m) (G : Finset (Pt m))
    (hG : G.card ≤ ⌈(m + 1 : ℝ) * R ^ 3⌉₊ ^ (m + 1)) :
    2 * ((meshPairs z G).card : ℝ) ≤
      (4 * (m + 2 : ℝ) ^ (2 * (m + 1))) * (2 + R) ^ (6 * (m + 1)) := by
  let n := ⌈(m + 1 : ℝ) * R ^ 3⌉₊
  have hn : (n : ℝ) ≤ (m + 2 : ℝ) * (2 + R) ^ 3 := by
    have hc := (Nat.ceil_lt_add_one (show 0 ≤ (m + 1 : ℝ) * R ^ 3 by positivity)).le
    change (n : ℝ) ≤ _ at hc
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hpow : R ^ 3 ≤ (2 + R) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have hpow1 : (1 : ℝ) ≤ (2 + R) ^ 3 := one_le_pow₀ (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (m + 1 : ℝ) by positivity)
    nlinarith
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hgn : (G.card : ℝ) ≤ (n : ℝ) ^ (m + 1) := by
    have hg : G.card ≤ n ^ (m + 1) := hG
    have hh : (G.card : ℝ) ≤ ((n ^ (m + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hg
    simpa only [Nat.cast_pow] using hh
  have hp := card_meshPairs_le z G
  have hpR : ((meshPairs z G).card : ℝ) ≤ (G.card : ℝ) ^ 2 + 1 := by exact_mod_cast hp
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg G.card) hgn 2
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ (2 * (m + 1)) :=
    one_le_pow₀ (by exact_mod_cast hn1)
  have hpn : 2 * ((meshPairs z G).card : ℝ) ≤ 4 * (n : ℝ) ^ (2 * (m + 1)) := by
    rw [← pow_mul] at hs
    have hcomm : (m + 1) * 2 = 2 * (m + 1) := by omega
    rw [hcomm] at hs
    nlinarith
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg n) hn (2 * (m + 1))
  apply hpn.trans
  apply (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 4)).trans_eq
  rw [mul_pow, ← pow_mul]
  have he : 3 * (2 * (m + 1)) = 6 * (m + 1) := by omega
  rw [he]
  ring

/-- The largest pair distance, including the default pair, is polynomially bounded too. -/
lemma mesh_diameter_polynomial {R : ℝ} (hR : 1 ≤ R) :
    2 + (2 * (m + 1 : ℝ) * R ^ 3 + 1) ≤
      (2 * (m + 1 : ℝ) + 3) * (2 + R) ^ 3 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hpow : R ^ 3 ≤ (2 + R) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hpow1 : (1 : ℝ) ≤ (2 + R) ^ 3 := one_le_pow₀ (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2 * (m + 1 : ℝ) by positivity)
  nlinarith

end IsotropicVariance.Paper.Proofs.SlabComparison
