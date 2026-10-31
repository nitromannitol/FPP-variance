/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.ModulusSupport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:modulus`: the excess `φ`

The steps on `φ(z) = μ(z) − ζ_t·z` of the proof of Lemma `lem:modulus`: by equations `eq:support`
and `eq:scales`, `φ ≤ C(b) g⁻³ Q_ℓ` at the points within distance `g⁻¹(ℓQ_ℓ)^{1/2}` of `x − u` and
of `v − x'`, so, since `φ` is convex and nonnegative, moving these two points by at most
`h(ℓQ_ℓ)^{1/2}`, with `h = g⁴`, changes `φ` by at most `C(b) g Q_ℓ`.

* `ball_bound_le`: the arithmetic of `φ ≤ C(b) g⁻³ Q_ℓ`;
* `abs_supportExcess_move_le`: the move.

The bound of `φ` on a ball is `supportExcess_le_of_mem_ball`
(`CurvatureVariance.Paper.Proofs.Localization.ModulusSupport`), and the secant step is
`abs_sub_le_of_convex` (`CurvatureVariance.Paper.Proofs.Localization.ModulusGeometry`), at the
radius `(ℓQ_ℓ)^{1/2}`: the exponents are `g⁴ · g⁻³ = g`. The paper's `γ` and `h = γ³` are here `g`
and `h = g⁴`.
-/

@[expose] public section

open Set
open scoped NNReal

namespace CurvatureVariance.Paper.Localization.Modulus

variable {m : ℕ}

/-- The arithmetic of `φ ≤ C(b) g⁻³ Q_ℓ`: with `W² = ℓ Q`, `gℓ ≤ s`, a transverse offset
`S ≤ C₂ g⁻¹ W` and `s x ≤ Q`, the two terms of `supportExcess_le_of_mem_ball` are at most
`(2 Cs C₂² + 3 Cs) g⁻³ Q`. -/
theorem ball_bound_le {Cs C₂ g s ℓ W Q x S : ℝ} (hCs : 0 < Cs) (hg : 0 < g) (hg1 : g ≤ 1)
    (hs : 0 < s) (hQ : 0 ≤ Q) (hS0 : 0 ≤ S) (hS : S ≤ C₂ * (g⁻¹ * W)) (hWsq : W ^ 2 = ℓ * Q)
    (hgs : g * ℓ ≤ s) (hsx : s * x ≤ Q) :
    2 * Cs * S ^ 2 / s + 3 * Cs * s * x ≤ (2 * Cs * C₂ ^ 2 + 3 * Cs) * g⁻¹ ^ 3 * Q := by
  have hginv : 0 < g⁻¹ := inv_pos.mpr hg
  have hginv1 : 1 ≤ g⁻¹ := one_le_inv_iff₀.mpr ⟨hg, hg1⟩
  have h1 : S ^ 2 ≤ C₂ ^ 2 * g⁻¹ ^ 2 * (ℓ * Q) := by
    have := pow_le_pow_left₀ hS0 hS 2
    rw [mul_pow, mul_pow, hWsq] at this
    linarith only [this]
  have hℓ : ℓ ≤ g⁻¹ * s := by
    rw [inv_mul_eq_div, le_div_iff₀ hg]; linarith only [hgs]
  have hc0 : 0 ≤ C₂ ^ 2 * g⁻¹ ^ 2 * Q := by positivity
  have h2 : S ^ 2 ≤ C₂ ^ 2 * g⁻¹ ^ 3 * Q * s := by
    have := mul_le_mul_of_nonneg_left hℓ hc0
    calc S ^ 2 ≤ C₂ ^ 2 * g⁻¹ ^ 2 * (ℓ * Q) := h1
      _ = C₂ ^ 2 * g⁻¹ ^ 2 * Q * ℓ := by ring
      _ ≤ C₂ ^ 2 * g⁻¹ ^ 2 * Q * (g⁻¹ * s) := this
      _ = _ := by ring
  have h3 : 2 * Cs * S ^ 2 / s ≤ 2 * Cs * C₂ ^ 2 * g⁻¹ ^ 3 * Q := by
    rw [div_le_iff₀ hs]
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * Cs)
    linarith only [this]
  have h4 : 3 * Cs * s * x ≤ 3 * Cs * Q := by
    have := mul_le_mul_of_nonneg_left hsx (by positivity : 0 ≤ 3 * Cs)
    linarith only [this]
  have h5 : 3 * Cs * Q ≤ 3 * Cs * g⁻¹ ^ 3 * Q := by
    have hg3 : 1 ≤ g⁻¹ ^ 3 := one_le_pow₀ hginv1
    have h0 : 0 ≤ 3 * Cs * Q := by positivity
    have := mul_le_mul_of_nonneg_left hg3 h0
    linarith only [this]
  have e : (2 * Cs * C₂ ^ 2 + 3 * Cs) * g⁻¹ ^ 3 * Q =
      2 * Cs * C₂ ^ 2 * g⁻¹ ^ 3 * Q + 3 * Cs * g⁻¹ ^ 3 * Q := by ring
  rw [e]
  linarith only [h3, h4, h5]

/-- **The move** (the proof of Lemma `lem:modulus`): let `y₁ = s`, `|y_⊥ − s t| ≤ σ` and
`σ + (1 + T) g⁻¹ W ≤ C₂ g⁻¹ W`. Then `φ` is at most `C(b) g⁻³ Q` on the ball of radius `g⁻¹ W`
around `y`, so, since `φ` is convex and nonnegative, moving `y` by at most `h W`, with `h = g⁴`,
changes `φ` by at most `C(b) g Q`. -/
theorem abs_supportExcess_move_le {μ : PtNorm m} {P : Pt m} {t t₀ : EuclideanSpace ℝ (Fin m)}
    {Cs r₁ δ T g C₂ s ℓ W Q σ : ℝ} (hP : IsSubgradient μ (slopeVec t) P) (hCs : 0 < Cs)
    (hup : ∀ h : EuclideanSpace ℝ (Fin m), ‖h‖ ≤ r₁ →
      supportExcess μ P (slopeVec (t + h)) ≤ Cs * ‖h‖ ^ 2 + Cs * ‖t - t₀‖ ^ (2 + δ))
    (hg : 0 < g) (hg2 : g ≤ 1 / 2) (hs : 0 < s) (hW : 0 < W) (hQ : 0 ≤ Q) (hT : ‖t‖ ≤ T)
    (hρL : g⁻¹ * W ≤ s / 2) (hsmall : 2 * (σ + (1 + T) * (g⁻¹ * W)) / s ≤ r₁)
    (hS : σ + (1 + T) * (g⁻¹ * W) ≤ C₂ * (g⁻¹ * W)) (hWsq : W ^ 2 = ℓ * Q) (hgs : g * ℓ ≤ s)
    (hsx : s * ‖t - t₀‖ ^ (2 + δ) ≤ Q) {y w : Pt m} (hyL : y.fst = s)
    (hσ : ‖y.snd - s • t‖ ≤ σ) (hw : ‖w‖ ≤ g ^ 4 * W) :
    |supportExcess μ P (y + w) - supportExcess μ P y| ≤ (2 * Cs * C₂ ^ 2 + 3 * Cs) * g * Q := by
  have hg1 : g ≤ 1 := by linarith only [hg2]
  have hginv0 : 0 < g⁻¹ := inv_pos.mpr hg
  have hginv2 : 2 ≤ g⁻¹ := by
    rw [show (2 : ℝ) = (1 / 2)⁻¹ by norm_num]
    exact inv_anti₀ hg hg2
  have hρ0 : 0 ≤ g⁻¹ * W := by positivity
  have hT0 : 0 ≤ T := (norm_nonneg t).trans hT
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans hσ
  set S := σ + (1 + T) * (g⁻¹ * W) with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hg4 : g ^ 4 ≤ 1 := pow_le_one₀ hg.le hg1
  have hw' : ‖w‖ ≤ W := hw.trans (mul_le_of_le_one_left hW.le hg4)
  have hB : ∀ z : Pt m, ‖z - y‖ ≤ W + ‖w‖ →
      supportExcess μ P z ≤ 2 * Cs * S ^ 2 / s + 3 * Cs * s * ‖t - t₀‖ ^ (2 + δ) := by
    intro z hz
    have hz' : ‖z - y‖ ≤ g⁻¹ * W := by
      have := mul_le_mul_of_nonneg_right hginv2 hW.le
      linarith only [hz, hw', this]
    exact supportExcess_le_of_mem_ball hCs.le hup hs hyL hσ hρ0 hρL hT hsmall hz'
  have hball := ball_bound_le hCs hg hg1 hs hQ hS0 hS hWsq hgs hsx
  have key := abs_sub_le_of_convex (supportExcess_convex μ P) (supportExcess_nonneg hP) hW hB
  have hB0 : 0 ≤ 2 * Cs * S ^ 2 / s + 3 * Cs * s * ‖t - t₀‖ ^ (2 + δ) := by
    have := Real.rpow_nonneg (norm_nonneg (t - t₀)) (2 + δ)
    positivity
  have hwW : ‖w‖ / W ≤ g ^ 4 := by rw [div_le_iff₀ hW]; exact hw
  refine key.trans ((mul_le_mul hwW hball hB0 (by positivity)).trans_eq ?_)
  have e : g ^ 4 * g⁻¹ ^ 3 = g := by field_simp
  calc g ^ 4 * ((2 * Cs * C₂ ^ 2 + 3 * Cs) * g⁻¹ ^ 3 * Q)
      = (2 * Cs * C₂ ^ 2 + 3 * Cs) * (g ^ 4 * g⁻¹ ^ 3) * Q := by ring
    _ = _ := by rw [e]

end CurvatureVariance.Paper.Localization.Modulus
