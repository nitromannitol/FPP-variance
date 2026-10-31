/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.TurningStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

/-!
# The constants of the dyadic chain

The constants of the induction of the proof of Lemma `lem:cone` (`ChainConstants`), for an excess
path `f` from `f 0` to `f n = f 0 + ℓ (1, t)`, and the norm distance `endDist` to the final point
`f n`. Put `R₀ = μ(f n − f 0)` and `R_j = 2^{−j} R₀`. While `R_j ≥ M S²`, the angle bound at the
chain point of radius `R_j` is the potential `P S^{1/2} R_j^{−1/4} + Q j |t − t₀|^{1+δ/2}`, for
slopes `‖t‖ ≤ T` and the slope factor `slopeFactor T`; since `R₀ ≤ μhi S² e^L`, at most `2 L` radii
are used (`chain_index_le`), and `chain_link_conditions` gives the conditions of one link. The
chain itself, through the last exits `z_j` of the paper, is in `Proofs.Geometry.ConeChain`.
-/

@[expose] public section

open InnerProductGeometry

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper

variable {m : ℕ}

/-! ### The constants of the chain -/

/-- The relations between the constants of the dyadic chain: `T` bounds the slopes, `Kc` compares
norm and Euclidean distances, `P` and `Q` are the coefficients of the potential, `η` and `ε₁` make
its superlinear correction small, `M S²` is the lowest radius used, and `ε₀` bounds the slope
deviation `|t − t₀|`. -/
structure ChainConstants (μlo μhi δ c C r₁ b T Kc P Q η ε₁ M ε₀ : ℝ) : Prop where
  μlo_pos : 0 < μlo
  μlo_le_μhi : μlo ≤ μhi
  δ_pos : 0 < δ
  δ_le_one : δ ≤ 1
  c_pos : 0 < c
  C_nonneg : 0 ≤ C
  b_nonneg : 0 ≤ b
  T_nonneg : 0 ≤ T
  four_div_le_Kc : 4 / μlo ≤ Kc
  two_mul_le_Kc : 2 * μhi ≤ Kc
  one_le_Kc : 1 ≤ Kc
  P_ge : 14 * stepConst Kc b c ≤ P
  Q_ge : 16 * Real.sqrt (C / c) ≤ Q
  η_le : 4 * slopeFactor T * Real.sqrt (C / c) * η ≤ 1 / 12
  rpow_ε₁_le : ε₁ ^ (δ / 2) ≤ η
  ε₁_le_r₁ : ε₁ ≤ r₁ / 2
  ε₁_le : ε₁ ≤ slopeFactor T * aperture T / 2
  one_le_M : 1 ≤ M
  two_mul_le_M : 2 * μhi ≤ M
  fluct_le : ∀ S R : ℝ, 0 ≤ S → 0 < R → M * S ^ 2 ≤ R →
    slopeFactor T * (P * turnErr S R) ≤ ε₁
  ε₀_le : ε₀ ≤ slopeFactor T * aperture T / 2
  ε₀_le_r₁ : ε₀ ≤ r₁ / 4
  ε₀_le_Q : 2 * slopeFactor T * Q * ε₀ ≤ 1

/-! ### The distance to the final point -/

variable {μ : Seminorm ℝ (Pt m)} {f : ℕ → Pt m} {n : ℕ}

/-- The norm distance from the `i`-th point to the final point `f n`. -/
noncomputable def endDist (μ : Seminorm ℝ (Pt m)) (f : ℕ → Pt m) (n i : ℕ) : ℝ :=
  μ (f n - f i)

theorem endDist_self : endDist μ f n n = 0 := by
  simp [endDist]

variable {b S : ℝ}

/-! ### The induction -/

variable {μlo μhi δ c C r₁ T Kc P Q η ε₁ M ε₀ : ℝ} {t₀ : EuclideanSpace ℝ (Fin m)}

/-- The chain radii above `M S²` number at most `2 L` when `‖f n − f 0‖ ≤ S² e^L`. -/
theorem chain_index_le (hK : ChainConstants μlo μhi δ c C r₁ b T Kc P Q η ε₁ M ε₀)
    (hhi : ∀ z, μ z ≤ μhi * ‖z‖) (hS : 1 ≤ S) {L : ℝ}
    (hlen : ‖f n - f 0‖ ≤ S ^ 2 * Real.exp L) {j : ℕ}
    (hj : M * S ^ 2 ≤ endDist μ f n 0 / 2 ^ j) : (j : ℝ) ≤ 2 * L := by
  apply nat_le_two_mul_of_two_pow_le_exp
  have hμhi : 0 < μhi := hK.μlo_pos.trans_le hK.μlo_le_μhi
  have hS2 : 0 < S ^ 2 := by positivity
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hR₀ : endDist μ f n 0 ≤ μhi * (S ^ 2 * Real.exp L) :=
    (hhi _).trans (mul_le_mul_of_nonneg_left hlen hμhi.le)
  rw [le_div_iff₀ h2j] at hj
  have hM : μhi ≤ M := by linarith [hK.two_mul_le_M]
  have : μhi * S ^ 2 * 2 ^ j ≤ μhi * S ^ 2 * Real.exp L := by
    have := mul_le_mul_of_nonneg_right hM (by positivity : (0 : ℝ) ≤ S ^ 2 * 2 ^ j)
    nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

/-- The conditions of one link of the chain at a chain point of radius `R ≥ M S²` and index
`j ≤ 2 L`: with `κ = slopeFactor T`, `X = P turnErr S R` and `Y = Q j |t − t₀|^{1+δ/2}`,
`κ X ≤ ε₁`, `κ Y ≤ |t − t₀|`, so the angle bound `X + Y` is at most `aperture T` and
`|t − t₀| + κ (X + Y) ≤ r₁`. -/
theorem chain_link_conditions (hK : ChainConstants μlo μhi δ c C r₁ b T Kc P Q η ε₁ M ε₀)
    (hS : 0 ≤ S) {t : EuclideanSpace ℝ (Fin m)} {L R j : ℝ} (ht : ‖t - t₀‖ ≤ ε₀)
    (htL : ‖t - t₀‖ ^ (δ / 2) * L ≤ ε₀) (hR : 0 < R) (hRM : M * S ^ 2 ≤ R)
    (hj : j ≤ 2 * L) :
    slopeFactor T * (P * turnErr S R) ≤ ε₁ ∧
      slopeFactor T * (Q * j * ‖t - t₀‖ ^ (1 + δ / 2)) ≤ ‖t - t₀‖ ∧
      P * turnErr S R + Q * j * ‖t - t₀‖ ^ (1 + δ / 2) ≤ aperture T ∧
      ‖t - t₀‖ + slopeFactor T * (P * turnErr S R + Q * j * ‖t - t₀‖ ^ (1 + δ / 2)) ≤ r₁ := by
  have hQ : 0 ≤ Q := le_trans (by have := Real.sqrt_nonneg (C / c); positivity) hK.Q_ge
  have hκ := slopeFactor_pos hK.T_nonneg
  have hX := hK.fluct_le S R hS hR hRM
  have hY := slope_term_le hK.δ_pos.le hκ.le hQ (norm_nonneg (t - t₀)) hj htL hK.ε₀_le_Q
  have h1 := hK.ε₁_le
  have h2 := hK.ε₀_le
  have h3 := hK.ε₁_le_r₁
  have h4 := hK.ε₀_le_r₁
  have hsum : slopeFactor T * (P * turnErr S R + Q * j * ‖t - t₀‖ ^ (1 + δ / 2)) =
      slopeFactor T * (P * turnErr S R) + slopeFactor T * (Q * j * ‖t - t₀‖ ^ (1 + δ / 2)) := by
    ring
  refine ⟨hX, hY, ?_, by linarith⟩
  refine le_of_mul_le_mul_left ?_ hκ
  linarith

end CurvatureVariance.Paper.Proofs.Geometry
