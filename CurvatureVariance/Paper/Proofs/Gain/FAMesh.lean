/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.FAGeometry
import CurvatureVariance.Paper.Proofs.Responses.Finiteness
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The slope of fine pairs and the mesh error (the proof of Lemma `lem:labels`)

* `norm_rowPairSlope_le_of_wide`: the pairs of cubes `I_{i−1}(j), I_i(k)` of face points have slope
  within `n^{δ/100−1/4}` of a centre `t₀` once `|t − t₀| ≤ ½ n^{δ/100−1/4}` and
  `m (1 + L w) ≤ ½ n^{3/4+δ/100}`; `mul_one_add_le_of_W_le` gives the latter from the first bound of
  equation `eq:scales`. In use `t₀` is the slope of the direction.
* `abs_normSlabTime_sub_le`: the mesh error. The continuity estimate, equation `eq:modulus`, of `T`
  and the comparison, equation `eq:profiledifference`, of `D_i` with `T` bound
  `|N(u,v) − N(u₂,v₂)|`, `N` the normalized slab passage time (`normSlabTime`), by
  `(X_mod + 2 C log² N + 2 max(X_pd, 0))/Q_n` for close endpoints (the proof of Lemma `lem:labels`:
  by the conditional Jensen inequality, `Ψ` inherits equation `eq:modulus`).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- **The slope of the fine pairs of a block** is within `n^{δ/100−1/4}` of `t₀`. -/
theorem norm_rowPairSlope_le_of_wide {δ : ℝ} {n w L : ℕ} (hn : 1 ≤ n)
    {t₀ t : EuclideanSpace ℝ (Fin m)} (ht : ‖t - t₀‖ ≤ 1 / 2 * (n : ℝ) ^ (δ / 100 - 1 / 4))
    (hwide : (m : ℝ) * (1 + L * w) ≤ 1 / 2 * (n : ℝ) ^ ((3 : ℝ) / 4 + δ / 100)) (i : ℕ)
    {o g j k : Fin m → ℤ} (hj : j ∈ rowBox L o g) (hk : k ∈ rowBox L o g) :
    ‖rowPairSlope n w t i j k - t₀‖ ≤ (n : ℝ) ^ (δ / 100 - 1 / 4) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := norm_rowPairSlope_sub_le (w := w) hn t i hj hk
  have h2 : (m : ℝ) * (1 + L * w) / n ≤ 1 / 2 * (n : ℝ) ^ (δ / 100 - 1 / 4) := by
    rw [div_le_iff₀ hn0, show δ / 100 - 1 / 4 = ((3 : ℝ) / 4 + δ / 100) - 1 by ring,
      Real.rpow_sub_one hn0.ne', mul_assoc, div_mul_cancel₀ _ hn0.ne']
    exact hwide
  calc ‖rowPairSlope n w t i j k - t₀‖ = ‖(t - t₀) + (rowPairSlope n w t i j k - t)‖ := by
        congr 1; abel
    _ ≤ ‖t - t₀‖ + ‖rowPairSlope n w t i j k - t‖ := norm_add_le _ _
    _ ≤ (n : ℝ) ^ (δ / 100 - 1 / 4) := by linarith

/-- **The width condition from the first bound of equation `eq:scales`**: if `W_n ≤ η n^{3/4+δ/100}`
with `η = 1/(8(m+1)(L+1))`, `w ≤ 2 W_n`, `n ≥ 16(m+1)²` and `δ ≥ 0`, then
`m (1 + L w) ≤ ½ n^{3/4+δ/100}`. -/
theorem mul_one_add_le_of_W_le {δ : ℝ} (hδ : 0 ≤ δ) {n w L : ℕ} {Wn : ℝ}
    (hn : 16 * ((m : ℝ) + 1) ^ 2 ≤ n) (hw : (w : ℝ) ≤ 2 * Wn)
    (hW : Wn ≤ 1 / (8 * ((m : ℝ) + 1) * ((L : ℝ) + 1)) * (n : ℝ) ^ ((3 : ℝ) / 4 + δ / 100)) :
    (m : ℝ) * (1 + L * w) ≤ 1 / 2 * (n : ℝ) ^ ((3 : ℝ) / 4 + δ / 100) := by
  set E : ℝ := (3 : ℝ) / 4 + δ / 100
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hn1 : (1 : ℝ) ≤ n := le_trans (by nlinarith) hn
  have hsqrt : 4 * ((m : ℝ) + 1) ≤ (n : ℝ) ^ E := by
    have h1 : Real.sqrt n ≤ (n : ℝ) ^ E := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by simp only [E]; linarith)
    have h2 : 4 * ((m : ℝ) + 1) ≤ Real.sqrt n := by
      rw [show 4 * ((m : ℝ) + 1) = Real.sqrt ((4 * ((m : ℝ) + 1)) ^ 2) by
        rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hnE : 0 ≤ (n : ℝ) ^ E := by positivity
  have hLw : (m : ℝ) * L * w ≤ 1 / 4 * (n : ℝ) ^ E := by
    have h1 : (m : ℝ) * L * w ≤ (m : ℝ) * L * (2 * Wn) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have h2 : (m : ℝ) * L * (2 * Wn) ≤ (m : ℝ) * L * (2 * (1 / (8 * ((m : ℝ) + 1) *
        ((L : ℝ) + 1)) * (n : ℝ) ^ E)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : (m : ℝ) * L * (2 * (1 / (8 * ((m : ℝ) + 1) * ((L : ℝ) + 1)) * (n : ℝ) ^ E)) =
        (m / ((m : ℝ) + 1)) * (L / ((L : ℝ) + 1)) * (1 / 4 * (n : ℝ) ^ E) := by
      field_simp
      ring
    have h4 : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h5 : (L : ℝ) / ((L : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h6 : (m / ((m : ℝ) + 1)) * (L / ((L : ℝ) + 1)) ≤ 1 := by
      calc (m / ((m : ℝ) + 1)) * (L / ((L : ℝ) + 1)) ≤ 1 * 1 :=
            mul_le_mul h4 h5 (by positivity) zero_le_one
        _ = 1 := one_mul 1
    have h7 : (m / ((m : ℝ) + 1)) * (L / ((L : ℝ) + 1)) * (1 / 4 * (n : ℝ) ^ E) ≤
        1 * (1 / 4 * (n : ℝ) ^ E) := mul_le_mul_of_nonneg_right h6 (by positivity)
    linarith
  nlinarith

/-- **The mesh error** (the proof of Lemma `lem:labels`): if
`|T(u,v) − T(u₂,v₂) − P·(v − u − v₂ + u₂)| ≤ X_mod` and `0 ≤ D − T ≤ c + X_pd` at the four points,
`D` the slab passage time of slab `i` and `D` finite, then
`|N(u,v) − N(u₂,v₂)| ≤ (X_mod + 2c + 2 max(X_pd, 0))/Q_n`. -/
theorem abs_normSlabTime_sub_le {M : Model m} {K : ℕ} {A : ℝ} {ω : Config m} {n i : ℕ}
    {P : Pt m} {u v u₂ v₂ : Vertex m} {Xm Xp c : ℝ} (hQ : 0 < Q M K A n)
    (hmod : |passageTimeReal ω u v - passageTimeReal ω u₂ v₂ -
      inner ℝ P (point v - point u - point v₂ + point u₂)| ≤ Xm)
    (hpd1 : (passageTime ω u v : ℝ≥0∞) ≤ slabTime ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v)
    (hpd2 : slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v - passageTimeReal ω u v ≤ c + Xp)
    (hpd3 : (passageTime ω u₂ v₂ : ℝ≥0∞) ≤ slabTime ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u₂ v₂)
    (hpd4 : slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u₂ v₂ - passageTimeReal ω u₂ v₂ ≤
      c + Xp)
    (hfin1 : slabTime ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v ≠ ⊤)
    (hfin2 : slabTime ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u₂ v₂ ≠ ⊤) :
    |normSlabTime M K A ω n P i u v - normSlabTime M K A ω n P i u₂ v₂| ≤
      (Xm + 2 * c + 2 * max Xp 0) / Q M K A n := by
  have e1 : passageTimeReal ω u v ≤ slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v := by
    have := ENNReal.toReal_mono hfin1 hpd1
    rwa [ENNReal.coe_toReal] at this
  have e2 : passageTimeReal ω u₂ v₂ ≤
      slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u₂ v₂ := by
    have := ENNReal.toReal_mono hfin2 hpd3
    rwa [ENNReal.coe_toReal] at this
  unfold normSlabTime
  rw [← sub_div, abs_div, abs_of_pos hQ, div_le_div_iff_of_pos_right hQ]
  have hin : inner ℝ P (point v - point u - point v₂ + point u₂) =
      inner ℝ P (point v - point u) - inner ℝ P (point v₂ - point u₂) := by
    rw [show point v - point u - point v₂ + point u₂ =
      (point v - point u) - (point v₂ - point u₂) by abel, inner_sub_right]
  rw [hin] at hmod
  have hX : Xp ≤ max Xp 0 := le_max_left _ _
  rw [abs_le] at hmod ⊢
  constructor <;> linarith [hmod.1, hmod.2]

end CurvatureVariance.Paper.Gain
