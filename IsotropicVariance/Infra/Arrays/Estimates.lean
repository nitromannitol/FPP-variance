/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Scalar estimates for penalized array sums

Elementary bounds used for penalized array sums: `y ^ α` against `exp y`, exponentially tilted
power sums, and a few explicit partial-sum bounds.
-/

@[expose] public section

open scoped ENNReal

namespace IsotropicVariance.Infra.Arrays

/-- The constant `1 + ⌈α⌉!` bounding `y ^ α` by a multiple of `exp y`. -/
noncomputable def expPowConst (α : ℝ) : ℝ := 1 + (Nat.ceil α).factorial

/-- The constant `1 + ⌈α⌉!` is at least `1`. -/
theorem one_le_expPowConst (α : ℝ) : 1 ≤ expPowConst α := by
  unfold expPowConst
  have : (0 : ℝ) ≤ (Nat.ceil α).factorial := Nat.cast_nonneg _
  linarith

/-- `y ^ α ≤ (1 + ⌈α⌉!) exp y` for `y, α ≥ 0`. -/
theorem rpow_le_expPowConst_mul_exp {α y : ℝ} (hα : 0 ≤ α) (hy : 0 ≤ y) :
    y ^ α ≤ expPowConst α * Real.exp y := by
  rcases le_total y 1 with h | h
  · calc y ^ α ≤ 1 := Real.rpow_le_one hy h hα
      _ ≤ expPowConst α * Real.exp y := by
        have h1 := one_le_expPowConst α
        have h2 := Real.one_le_exp hy
        nlinarith
  · have h1 : y ^ α ≤ y ^ (Nat.ceil α) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h (Nat.le_ceil α)
    have h2 : y ^ (Nat.ceil α) ≤ (Nat.ceil α).factorial * Real.exp y := by
      have := Real.pow_div_factorial_le_exp y hy (Nat.ceil α)
      have hf : (0 : ℝ) < (Nat.ceil α).factorial := by positivity
      rwa [div_le_iff₀ hf, mul_comm] at this
    refine h1.trans (h2.trans ?_)
    unfold expPowConst
    nlinarith [Real.exp_pos y]

/-- Scaled version of `rpow_le_expPowConst_mul_exp`: `x ^ α ≤ c ^ α (1 + ⌈α⌉!) exp (x / c)`. -/
theorem rpow_le_rpow_mul_expPowConst_mul_exp_div {α x c : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ x)
    (hc : 0 < c) : x ^ α ≤ c ^ α * expPowConst α * Real.exp (x / c) := by
  have hx' : 0 ≤ x / c := div_nonneg hx hc.le
  have : x = c * (x / c) := by field_simp
  calc x ^ α = (c * (x / c)) ^ α := by rw [← this]
    _ = c ^ α * (x / c) ^ α := Real.mul_rpow hc.le hx'
    _ ≤ c ^ α * (expPowConst α * Real.exp (x / c)) := by
        gcongr
        exact rpow_le_expPowConst_mul_exp hα hx'
    _ = _ := by ring

/-- The constant of the exponentially tilted power sum. -/
noncomputable def tiltConst (α : ℝ) : ℝ := 4 * 2 ^ α * expPowConst α

/-- Exponentially tilted power sum: `∑ n^α e^{-θ n} ≤ C_α θ^{-(1+α)}` for `0 < θ ≤ 1`. -/
theorem tsum_rpow_mul_exp_neg_le {α θ : ℝ} (hα : 0 ≤ α) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) ^ α * Real.exp (-θ * n)) ≤
      ENNReal.ofReal (tiltConst α * θ ^ (-(1 + α))) := by
  set K := expPowConst α with hK
  set r := Real.exp (-θ / 2) with hr
  have hc : 0 < 2 / θ := by positivity
  set a : ℝ := (2 / θ) ^ α * K with ha
  have hK0 : 0 ≤ K := (zero_le_one.trans (one_le_expPowConst α))
  have ha0 : 0 ≤ a := by positivity
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr]
    have := Real.exp_lt_exp.2 (show -θ / 2 < 0 by linarith)
    simpa using this
  have hterm : ∀ n : ℕ, (n : ℝ) ^ α * Real.exp (-θ * n) ≤ a * r ^ n := by
    intro n
    have h := rpow_le_rpow_mul_expPowConst_mul_exp_div hα (Nat.cast_nonneg n) hc
    have e : Real.exp (-θ * n) * Real.exp ((n : ℝ) / (2 / θ)) = r ^ n := by
      rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      field_simp
      ring
    calc (n : ℝ) ^ α * Real.exp (-θ * n)
        ≤ ((2 / θ) ^ α * K * Real.exp ((n : ℝ) / (2 / θ))) * Real.exp (-θ * n) := by
          gcongr
      _ = a * r ^ n := by rw [← e, ha]; ring
  have hsum : Summable (fun n : ℕ => a * r ^ n) := (summable_geometric_of_lt_one hr0 hr1).mul_left a
  calc ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) ^ α * Real.exp (-θ * n))
      ≤ ∑' n : ℕ, ENNReal.ofReal (a * r ^ n) := by
        exact ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal (hterm n)
    _ = ENNReal.ofReal (∑' n : ℕ, a * r ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
        have hu : 1 + θ / 2 ≤ Real.exp (θ / 2) := by linarith [Real.add_one_le_exp (θ / 2)]
        have hr' : r * Real.exp (θ / 2) = 1 := by
          have h0 : -θ / 2 + θ / 2 = 0 := by ring
          rw [hr, ← Real.exp_add, h0, Real.exp_zero]
        have h1r : θ / 4 ≤ 1 - r := by
          have hpos : 0 < 1 + θ / 2 := by positivity
          have : r * (1 + θ / 2) ≤ 1 := by
            calc r * (1 + θ / 2) ≤ r * Real.exp (θ / 2) := by gcongr
              _ = 1 := hr'
          nlinarith
        have hinv : (1 - r)⁻¹ ≤ 4 / θ := by
          rw [inv_le_comm₀ (by linarith) (by positivity)]
          rw [inv_div]; exact h1r
        have e : θ ^ (-(1 + α)) = 1 / (θ * θ ^ α) := by
          rw [Real.rpow_neg hθ0.le, Real.rpow_add hθ0, Real.rpow_one]; simp
        calc a * (1 - r)⁻¹ ≤ a * (4 / θ) := by gcongr
          _ = tiltConst α * θ ^ (-(1 + α)) := by
            rw [e, ha, Real.div_rpow (by norm_num) hθ0.le, tiltConst, ← hK]
            have : 0 < θ ^ α := Real.rpow_pos_of_pos hθ0 α
            field_simp

/-- Partial sums of `ℓ ^ (-θ)` are bounded by `M ^ (1 - θ) / (1 - θ)`. -/
theorem sum_Icc_rpow_neg_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (M : ℕ) :
    ∑ ℓ ∈ Finset.Icc 1 M, (ℓ : ℝ) ^ (-θ) ≤ (M : ℝ) ^ (1 - θ) / (1 - θ) := by
  have hp : 0 < 1 - θ := by linarith
  induction M with
  | zero => simp [Real.zero_rpow hp.ne']
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    set L : ℝ := ((M + 1 : ℕ) : ℝ) with hL
    have hL1 : 1 ≤ L := by rw [hL]; push_cast; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    have hL0 : 0 < L := by linarith
    have hM : (M : ℝ) = L - 1 := by rw [hL]; push_cast; ring
    have hb := _root_.rpow_one_add_le_one_add_mul_self (s := -1 / L) (p := 1 - θ)
      (by rw [le_div_iff₀ hL0]; linarith) hp.le (by linarith)
    have e1 : 1 + -1 / L = (M : ℝ) / L := by rw [hM]; field_simp; ring
    rw [e1, Real.div_rpow (Nat.cast_nonneg M) hL0.le] at hb
    have e2 : L ^ (1 - θ) = L * L ^ (-θ) := by
      rw [sub_eq_add_neg, Real.rpow_add hL0, Real.rpow_one]
    have hq : 0 < L ^ (-θ) := Real.rpow_pos_of_pos hL0 _
    rw [e2, div_le_iff₀ (by positivity)] at hb
    have hb' : (M : ℝ) ^ (1 - θ) ≤ L * L ^ (-θ) - (1 - θ) * L ^ (-θ) := by
      have : (1 + (1 - θ) * (-1 / L)) * (L * L ^ (-θ)) = L * L ^ (-θ) - (1 - θ) * L ^ (-θ) := by
        field_simp
        ring
      linarith
    rw [e2.symm] at hb'
    rw [le_div_iff₀ hp] at ih ⊢
    have : L ^ (-θ) * (1 - θ) ≤ L ^ (1 - θ) - (M : ℝ) ^ (1 - θ) := by linarith
    rw [add_mul]
    linarith

end IsotropicVariance.Infra.Arrays
