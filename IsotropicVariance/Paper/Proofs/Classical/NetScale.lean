/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.ErrorScale
public import IsotropicVariance.Paper.Proofs.Classical.SphereNet
import IsotropicVariance.Paper.Proofs.SlabComparison.Logarithms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The square-root logarithmic loss of the sphere net

The sphere-net cardinality is polynomial in its radius. The maximum of Gaussian
fluctuations on the net therefore has scale `sqrt(s log(2+s))`.
-/

@[expose] public section

namespace IsotropicVariance.Paper.Proofs.Classical

/-- The Gaussian maximum's net-cardinality loss is at most a dimension-dependent
multiple of the classical square-root-log error scale. -/
theorem sphere_net_scale_bound (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (s : ℝ), 1 ≤ s → ∀ H : Finset (Pt m), H.Nonempty →
      H.card ≤ ⌈(m + 1 : ℝ) * s⌉₊ ^ (m + 1) →
      (Real.log (2 * (H.card : ℝ)) / Real.log 2) ^ (1 / (2 : ℝ)) * Real.sqrt s ≤
        D * errorScale s := by
  let B : ℝ := 2 * (m + 2 : ℝ) ^ (m + 1)
  have hB : 1 ≤ B := by
    have hh := one_le_pow₀ (show (1 : ℝ) ≤ m + 2 by linarith only [Nat.cast_nonneg (α := ℝ) m]) (n := m + 1)
    dsimp only [B]
    linarith only [hh]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  let A : ℝ := (Real.log B / Real.log 2 + (m + 1 : ℝ)) / Real.log 2
  have hA : 0 < A := by
    have hLB := Real.log_nonneg hB
    dsimp only [A]
    positivity
  refine ⟨Real.sqrt A, Real.sqrt_pos.mpr hA, ?_⟩
  intro s hs H hH hcard
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  let n := ⌈(m + 1 : ℝ) * s⌉₊
  have hn : (n : ℝ) ≤ (m + 2 : ℝ) * (2 + s) := by
    have hh := (Nat.ceil_lt_add_one (show 0 ≤ (m + 1 : ℝ) * s by positivity)).le
    change (n : ℝ) ≤ _ at hh
    nlinarith only [hh, Nat.cast_nonneg (α := ℝ) m, hs]
  have hpoly : 2 * (H.card : ℝ) ≤ B * (2 + s) ^ (m + 1) := by
    have hcardn : H.card ≤ n ^ (m + 1) := hcard
    have hh : (H.card : ℝ) ≤ (n : ℝ) ^ (m + 1) := by
      simpa only [Nat.cast_pow] using (Nat.cast_le (α := ℝ)).mpr hcardn
    have hh' := pow_le_pow_left₀ (Nat.cast_nonneg n) hn (m + 1)
    rw [mul_pow] at hh'
    dsimp only [B]
    nlinarith only [hh, hh']
  have hcard0 : (0 : ℝ) < H.card := Nat.cast_pos.mpr hH.card_pos
  have hlogcard := SlabComparison.log_le_of_polynomial_bound hB hs
    (by positivity : 0 < 2 * (H.card : ℝ)) hpoly
  have hratio : Real.log (2 * (H.card : ℝ)) / Real.log 2 ≤ A * Real.log (2 + s) := by
    apply (div_le_div_of_nonneg_right hlogcard hlog.le).trans_eq
    dsimp only [A]
    push_cast
    ring
  have hroot := Real.sqrt_le_sqrt hratio
  rw [Real.sqrt_mul hA.le] at hroot
  calc
    _ = Real.sqrt (Real.log (2 * (H.card : ℝ)) / Real.log 2) * Real.sqrt s := by
      simp only [Real.sqrt_eq_rpow]
    _ ≤ (Real.sqrt A * Real.sqrt (Real.log (2 + s))) * Real.sqrt s :=
      mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)
    _ = Real.sqrt A * errorScale s := by
      rw [errorScale, Real.sqrt_mul hs0]
      ring

end IsotropicVariance.Paper.Proofs.Classical
