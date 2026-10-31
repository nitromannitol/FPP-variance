/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Fekete's lemma on the nonnegative real half-line

Integer Fekete plus a Lipschitz estimate gives the real-parameter limit.
Subadditivity on integer multiples of each fixed positive real parameter gives
the lower tangent bound at every scale, not just at integers.
-/

@[expose] public section
open Set Filter Topology
namespace IsotropicVariance.Infra.TimeConstant

/-- A linearly bounded subadditive Lipschitz function on the nonnegative half-line
has a positive finite asymptotic slope and lies above that slope at every scale. -/
theorem exists_slope_of_subadditive (H : ℝ → ℝ) {a b : ℝ} (ha : 0 < a)
    (hBounds : ∀ t, 0 ≤ t → a * t ≤ H t ∧ H t ≤ b * t)
    (hSub : ∀ s t, 0 ≤ s → 0 ≤ t → H (s + t) ≤ H s + H t)
    (hLip : ∀ s t, 0 ≤ s → 0 ≤ t → |H s - H t| ≤ b * |s - t|) :
    ∃ μ : ℝ, a ≤ μ ∧ μ ≤ b ∧
      Tendsto (fun t : ℝ => H t / t) atTop (𝓝 μ) ∧ ∀ t, 0 ≤ t → μ * t ≤ H t := by
  have hb : 0 ≤ b := by
    have hh := (hBounds 1 zero_le_one).1.trans (hBounds 1 zero_le_one).2
    nlinarith only [hh, ha]
  have h0 : H 0 = 0 := by
    have hh := hBounds 0 le_rfl
    simp only [mul_zero] at hh
    exact le_antisymm hh.2 hh.1
  have hN : Subadditive (fun n : ℕ => H n) := by
    intro m n
    simpa only [Nat.cast_add] using hSub m n (Nat.cast_nonneg m) (Nat.cast_nonneg n)
  have hBdd : BddBelow (range fun n : ℕ => H n / n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg ((mul_nonneg ha.le (Nat.cast_nonneg n)).trans (hBounds n (Nat.cast_nonneg n)).1) (Nat.cast_nonneg n)
  let μ := hN.lim
  have hNat : Tendsto (fun n : ℕ => H n / n) atTop (𝓝 μ) := hN.tendsto_lim hBdd
  have hFloor : Tendsto (fun t : ℝ => H (⌊t⌋₊ : ℝ) / (⌊t⌋₊ : ℝ)) atTop (𝓝 μ) :=
    hNat.comp tendsto_nat_floor_atTop
  have hMain : Tendsto (fun t : ℝ => H (⌊t⌋₊ : ℝ) / t) atTop (𝓝 μ) := by
    have hh := hFloor.mul (tendsto_nat_floor_div_atTop (R := ℝ))
    rw [mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hn : (⌊t⌋₊ : ℝ) ≠ 0 := by
      have hh : 1 ≤ ⌊t⌋₊ := (Nat.le_floor (by simpa only [Nat.cast_one] using ht))
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hh))
    field_simp
  have hErr : Tendsto (fun t : ℝ => (H t - H (⌊t⌋₊ : ℝ)) / t) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_nhds.div_atTop tendsto_id :
      Tendsto (fun t : ℝ => b / t) atTop (𝓝 0))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    have hFloorLe := Nat.floor_le ht0
    have hFrac : |t - (⌊t⌋₊ : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hFloorLe)]
      linarith only [Nat.lt_floor_add_one t]
    have hh := (hLip t ⌊t⌋₊ ht0 (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hFrac hb)
    rw [mul_one] at hh
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact div_le_div_of_nonneg_right hh ht0
  have hLim : Tendsto (fun t : ℝ => H t / t) atTop (𝓝 μ) := by
    have hh := hMain.add hErr
    rw [add_zero] at hh
    convert hh using 1
    funext t
    rw [← add_div]
    congr 1
    ring
  have hLo : a ≤ μ := ge_of_tendsto hLim (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (le_div_iff₀ ht).mpr (hBounds t ht.le).1)
  have hHi : μ ≤ b := le_of_tendsto hLim (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (div_le_iff₀ ht).mpr (by simpa only [mul_comm] using (hBounds t ht.le).2))
  refine ⟨μ, hLo, hHi, hLim, ?_⟩
  intro t ht
  rcases ht.eq_or_lt with rfl | ht
  · simp only [mul_zero, h0, le_refl]
  have hIter (n : ℕ) : H ((n : ℝ) * t) ≤ (n : ℝ) * H t := by
    induction n with
    | zero => simp only [Nat.cast_zero, zero_mul, h0, le_refl]
    | succ n hn =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      exact (hSub ((n : ℝ) * t) t (mul_nonneg (Nat.cast_nonneg n) ht.le) ht.le).trans
        (by linarith only [hn])
  have hRay := hLim.comp (tendsto_natCast_atTop_atTop.atTop_mul_const ht)
  have hSlope : μ ≤ H t / t := le_of_tendsto hRay (by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    apply (div_le_div_iff₀ (mul_pos hnR ht) ht).mpr
    have hh := mul_le_mul_of_nonneg_right (hIter n) ht.le
    nlinarith only [hh])
  exact (le_div_iff₀ ht).mp hSlope

end IsotropicVariance.Infra.TimeConstant
