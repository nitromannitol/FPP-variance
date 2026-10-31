/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.Walks

/-!
# From two tails to an exponential tail at the scale `L^{1/2}`

The `ℓ¹` norm of a vertex is at most `(d + 1)` times its Euclidean norm, and a lower Gaussian tail
together with an upper tail that is Gaussian up to level `1 + n` and exponential beyond give an
exponential tail for `|W - μ|` at the scale `L^{1/2}` whenever `1 + n ≤ k L`.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal

namespace CurvatureVariance.Infra.FPP


/-- Each coordinate of a vertex is at most its Euclidean norm, so `|x|₁ ≤ d |x|`. -/
theorem l1Dist_zero_le_norm_point {m : ℕ} (x : Vertex m) :
    (l1Dist 0 x : ℝ) ≤ (m + 1) * ‖point x‖ := by
  have hsq := norm_point_sq x
  have h0 := norm_nonneg (point x)
  have ht0 := norm_nonneg (transversePoint x.2)
  have h1 : |(x.1 : ℝ)| ≤ ‖point x‖ :=
    abs_le_of_sq_le_sq (by nlinarith only [hsq, ht0]) h0
  have h2 : ‖transversePoint x.2‖ ≤ ‖point x‖ := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg (x.1 : ℝ)]
  have h3 : ∀ j, |(x.2 j : ℝ)| ≤ ‖point x‖ := fun j => by
    have := PiLp.norm_apply_le (transversePoint x.2) j
    simpa [transversePoint] using this.trans h2
  have h4 : (l1Dist 0 x : ℝ) = |(x.1 : ℝ)| + ∑ j, |(x.2 j : ℝ)| := by
    simp [l1Dist, Nat.cast_sum, Nat.cast_natAbs]
  have h5 : ∑ j, |(x.2 j : ℝ)| ≤ ∑ _j : Fin m, ‖point x‖ :=
    Finset.sum_le_sum fun j _ => h3 j
  rw [h4]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h5
  linarith only [h1, h5]

/-- For `|x| ≥ 2`: `1 + |x|₁ ≤ (d + 1) |x|`. -/
theorem one_add_l1Dist_zero_le {m : ℕ} {x : Vertex m} (hx : 2 ≤ ‖point x‖) :
    1 + (l1Dist 0 x : ℝ) ≤ (m + 2) * ‖point x‖ := by
  have := l1Dist_zero_le_norm_point x
  linarith only [this, hx]

/-- **From two tails to an exponential tail at the scale `L^{1/2}`.** If the lower tail of
`W - μ` is Gaussian at scale `(1 + n)^{1/2}` and the upper tail is Gaussian up to level `1 + n` and
exponential beyond, and `1 + n ≤ k L` with `L ≥ 1`, `k ≥ 1`, then
`P(|W - μ| > u L^{1/2}) ≤ 2C e^{c/k} e^{-(c/k) u}`. -/
theorem measure_lt_abs_sub_le_of_tails {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : Ω → ℝ} {μ C c n k L : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hn : 0 ≤ n) (hk : 1 ≤ k)
    (hL : 1 ≤ L) (hnL : 1 + n ≤ k * L)
    (hlow : ∀ z : ℝ, 0 ≤ z →
      P {ω | W ω - μ ≤ -z} ≤ ENNReal.ofReal (C * exp (-(c * (z ^ 2 / (1 + n))))))
    (hup : ∀ z : ℝ, 0 ≤ z →
      P {ω | z ≤ W ω - μ} ≤ ENNReal.ofReal (C * exp (-(c * min (z ^ 2 / (1 + n)) z))))
    {u : ℝ} (hu : 0 ≤ u) :
    P {ω | u * Real.sqrt L < |W ω - μ|} ≤
      ENNReal.ofReal (2 * C * exp (c / k) * exp (-(c / k * u))) := by
  set s := u * Real.sqrt L with hs
  have hsq1 : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hL
  have hs0 : 0 ≤ s := mul_nonneg hu (by linarith only [hsq1])
  have hn1 : 0 < 1 + n := by linarith only [hn]
  have hk0 : 0 < k := by linarith only [hk]
  have hsu : u ≤ s := by nlinarith only [hu, hsq1]
  have hs2 : s ^ 2 = u ^ 2 * L := by
    rw [hs, mul_pow, Real.sq_sqrt (by linarith only [hL])]
  -- key inequality
  have hkey : (u - 1) / k ≤ min (s ^ 2 / (1 + n)) s := by
    apply le_min
    · have h1 : u ^ 2 / k ≤ s ^ 2 / (1 + n) := by
        rw [hs2, div_le_div_iff₀ hk0 hn1]
        nlinarith only [hnL, sq_nonneg u]
      have h2 : (u - 1) / k ≤ u ^ 2 / k := by
        apply div_le_div_of_nonneg_right _ hk0.le
        nlinarith only [sq_nonneg (u - 1), hu]
      exact h2.trans h1
    · have : (u - 1) / k ≤ u := by
        rw [div_le_iff₀ hk0]
        nlinarith only [hk, hu]
      exact this.trans hsu
  have hbound : ∀ a : ℝ, (u - 1) / k ≤ a →
      C * exp (-(c * a)) ≤ 2 * C * exp (c / k) * exp (-(c / k * u)) / 2 := by
    intro a ha
    have h1 : exp (-(c * a)) ≤ exp (c / k) * exp (-(c / k * u)) := by
      rw [← exp_add]
      apply exp_le_exp.2
      have : c * ((u - 1) / k) ≤ c * a := mul_le_mul_of_nonneg_left ha hc
      have e : c * ((u - 1) / k) = c / k * u - c / k := by ring
      linarith only [this, e]
    have := mul_le_mul_of_nonneg_left h1 hC
    linarith only [this]
  have hsub : {ω | s < |W ω - μ|} ⊆ {ω | s ≤ W ω - μ} ∪ {ω | W ω - μ ≤ -s} := by
    intro ω hω
    have hω' : s < |W ω - μ| := hω
    rcases lt_abs.1 hω' with h | h
    · exact Or.inl (show s ≤ W ω - μ from h.le)
    · exact Or.inr (show W ω - μ ≤ -s by linarith only [h])
  have hA := (hup s hs0).trans (ENNReal.ofReal_le_ofReal (hbound _ hkey))
  have hB := (hlow s hs0).trans (ENNReal.ofReal_le_ofReal
    (by
      have hm : min (s ^ 2 / (1 + n)) s ≤ s ^ 2 / (1 + n) := min_le_left _ _
      have hm2 : (u - 1) / k ≤ s ^ 2 / (1 + n) := hkey.trans hm
      exact hbound _ hm2))
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add hA hB).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith only
