/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.ModulusGeometry
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes
import CurvatureVariance.Paper.Proofs.Localization.Common

/-!
# Scales and the supporting-hyperplane excess for the continuity estimate

For the proof of equation `eq:modulus`, in the proof of
Lemma `lem:modulus`:

* the scales `Q_s = A s^{1/2−δ/K}`, `W_s = √(s Q_s)`: positivity, `W_s² = s Q_s`, monotonicity,
  `W_ℓ ≤ (ℓ/L) W_L`, `Q_L ≤ g^{1/3} Q_ℓ` for `L ≤ gℓ`, and `ℓ |τ|^{2+δ} ≤ Q_ℓ` for
  `|τ| ≤ ℓ^{δ/100−1/4}`, applied to the slope deviation `τ = t − t₀`;
* the excess `f(z) = μ(z) − P·z` over a supporting hyperplane: nonnegative, convex, positively
  homogeneous, and bounded on balls around points of slope near `t` through the upper bound of
  equation `eq:support` at `t`, whose error `|t − t₀|^{2+δ}` is measured from the slope `t₀` of
  the direction.
-/

@[expose] public section

open Set
open scoped NNReal

namespace CurvatureVariance.Paper.Localization.Modulus

variable {m : ℕ}

/-! ## Norms of transverse vectors -/

/-- A vector of `ℝ^m` whose coordinates are bounded by `σ` has norm at most `m σ`. -/
theorem norm_le_of_forall_abs_le {v : EuclideanSpace ℝ (Fin m)} {σ : ℝ} (hσ : 0 ≤ σ)
    (h : ∀ j, |v j| ≤ σ) : ‖v‖ ≤ m * σ := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ j, ‖v j‖ ^ 2 ≤ ((m : ℝ) * σ) ^ 2 := by
    calc ∑ j, ‖v j‖ ^ 2 ≤ ∑ _j : Fin m, σ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
      _ = (m : ℝ) * σ ^ 2 := by simp
      _ ≤ ((m : ℝ) * σ) ^ 2 := by
          rw [mul_pow]
          have : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
            rcases Nat.eq_zero_or_pos m with h0 | h0
            · simp [h0]
            · have : (1 : ℝ) ≤ m := by exact_mod_cast h0
              nlinarith only [this]
          exact mul_le_mul_of_nonneg_right this (sq_nonneg σ)
  calc Real.sqrt (∑ j, ‖v j‖ ^ 2) ≤ Real.sqrt (((m : ℝ) * σ) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = m * σ := Real.sqrt_sq (by positivity)

/-- The transverse vector of a grid index in `{-n, …, n}^m` has norm at most `m n`. -/
theorem norm_transversePoint_le {k : Fin m → ℤ} {n : ℕ} (hk : ∀ j, |k j| ≤ (n : ℤ)) :
    ‖transversePoint k‖ ≤ m * n :=
  norm_le_of_forall_abs_le (Nat.cast_nonneg n) fun j => by
    have h : ((|k j| : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := Int.cast_le.mpr (hk j)
    rw [Int.cast_abs, Int.cast_natCast] at h
    rwa [Infra.FPP.transversePoint_apply]

/-! ## Scales -/

section Scales

variable (M : Model m) {K : ℕ} {A : ℝ}

/-- The exponent `1/2 − δ/K` of `Q` lies in `[1/3, 1/2]`. -/
theorem exponent_bounds (hM : M.Standing) (hK : 10 ^ 4 ≤ K) :
    (1 : ℝ) / 3 ≤ 1 / 2 - M.δ / K ∧ 1 / 2 - M.δ / K ≤ 1 / 2 ∧ M.δ / K ≤ M.δ / 10 ^ 4 := by
  have hK' : (10 : ℝ) ^ 4 ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK'
  have h1 : M.δ / K ≤ M.δ / 10 ^ 4 :=
    div_le_div_of_nonneg_left hM.delta_pos.le (by norm_num) hK'
  have h2 : 0 ≤ M.δ / K := div_nonneg hM.delta_pos.le hKpos.le
  refine ⟨?_, by linarith only [h2], h1⟩
  have : M.δ / 10 ^ 4 ≤ 1 / 10 ^ 4 := div_le_div_of_nonneg_right hM.delta_le_one (by norm_num)
  linarith only [this, h1]

theorem W_sq {s : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A) : W M K A s ^ 2 = s * Q M K A s :=
  Real.sq_sqrt (mul_nonneg hs (mul_nonneg hA (Real.rpow_nonneg hs _)))

theorem W_pos (hA : 0 < A) {s : ℝ} (hs : 0 < s) : 0 < W M K A s :=
  Real.sqrt_pos.mpr (mul_pos hs (Q_pos hA hs))

/-- `W_s ≥ √s` for `A ≥ 1` and `s ≥ 1`. -/
theorem sqrt_le_W (hM : M.Standing) (hK : 10 ^ 4 ≤ K) (hA : 1 ≤ A) {s : ℝ} (hs : 1 ≤ s) :
    Real.sqrt s ≤ W M K A s := by
  unfold W
  apply Real.sqrt_le_sqrt
  have := one_le_Q hM hK hA hs
  nlinarith only [this, hs]

/-- `W_ℓ ≤ (ℓ/L) W_L` for `0 < L ≤ ℓ`. -/
theorem W_le_div_mul (hM : M.Standing) (hK : 10 ^ 4 ≤ K) (hA : 0 < A) {L ℓ : ℝ} (hL : 0 < L)
    (hLℓ : L ≤ ℓ) : W M K A ℓ ≤ ℓ / L * W M K A L := by
  have he := exponent_bounds M hM hK
  have hℓ : 0 < ℓ := hL.trans_le hLℓ
  have hr : 1 ≤ ℓ / L := (one_le_div hL).mpr hLℓ
  have hWL := W_pos M (K := K) hA hL
  rw [← abs_of_pos hWL, ← abs_of_pos (W_pos M (K := K) hA hℓ), ← abs_of_pos (by positivity : 0 < ℓ / L),
    ← abs_mul]
  apply sq_le_sq.mp
  rw [mul_pow, W_sq M hℓ.le hA.le, W_sq M hL.le hA.le]
  unfold Q
  have hsplit : ℓ ^ ((1 : ℝ) / 2 - M.δ / K) = (ℓ / L) ^ ((1 : ℝ) / 2 - M.δ / K) *
      L ^ ((1 : ℝ) / 2 - M.δ / K) := by
    rw [← Real.mul_rpow (by positivity) hL.le, div_mul_cancel₀ _ hL.ne']
  have hpow : (ℓ / L) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ ℓ / L := by
    calc (ℓ / L) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ (ℓ / L) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hr (by linarith only [he.2.1])
      _ = ℓ / L := Real.rpow_one _
  rw [hsplit]
  have hLpow := Real.rpow_nonneg hL.le ((1 : ℝ) / 2 - M.δ / K)
  have hℓL : ℓ = ℓ / L * L := (div_mul_cancel₀ _ hL.ne').symm
  calc ℓ * (A * ((ℓ / L) ^ ((1 : ℝ) / 2 - M.δ / K) * L ^ ((1 : ℝ) / 2 - M.δ / K)))
      ≤ ℓ * (A * (ℓ / L * L ^ ((1 : ℝ) / 2 - M.δ / K))) := by gcongr
    _ = (ℓ / L) ^ 2 * (L * (A * L ^ ((1 : ℝ) / 2 - M.δ / K))) := by
        field_simp

end Scales

/-! ## The excess over a supporting hyperplane -/

/-- The excess `f(z) = μ(z) − P·z` of the norm `μ` over the linear function `P`. -/
noncomputable def supportExcess (μ : PtNorm m) (P z : Pt m) : ℝ := μ.1 z - inner ℝ P z

theorem supportExcess_nonneg {μ : PtNorm m} {x P : Pt m} (hP : IsSubgradient μ x P) (z : Pt m) :
    0 ≤ supportExcess μ P z :=
  sub_nonneg.mpr (hP.2 z)

theorem supportExcess_convex (μ : PtNorm m) (P : Pt m) (x y : Pt m) (l : ℝ) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) : supportExcess μ P ((1 - l) • x + l • y) ≤
      (1 - l) * supportExcess μ P x + l * supportExcess μ P y := by
  unfold supportExcess
  have h := map_add_le_add μ.1 ((1 - l) • x) (l • y)
  rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_of_nonneg (by linarith only [hl1]),
    Real.norm_of_nonneg hl0] at h
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  linarith only [h]

theorem supportExcess_smul (μ : PtNorm m) (P z : Pt m) {r : ℝ} (hr : 0 ≤ r) :
    supportExcess μ P (r • z) = r * supportExcess μ P z := by
  unfold supportExcess
  rw [map_smul_eq_mul, Real.norm_of_nonneg hr, real_inner_smul_right]
  ring

/-- The upper bound of equation `eq:support`, transported to a point `z` with `z₁ > 0` whose slope
differs from `t` by at most `r₁`: `f(z) ≤ C |z_⊥ − z₁ t|²/z₁ + z₁ E`, if
`f(1, t + h) ≤ C |h|² + E` for `|h| ≤ r₁`. -/
theorem supportExcess_le {μ : PtNorm m} {P : Pt m} {t : EuclideanSpace ℝ (Fin m)}
    {C r₁ E : ℝ}
    (hup : ∀ h : EuclideanSpace ℝ (Fin m), ‖h‖ ≤ r₁ →
      supportExcess μ P (slopeVec (t + h)) ≤ C * ‖h‖ ^ 2 + E)
    {z : Pt m} (hz : 0 < z.fst) (hr : ‖z.snd - z.fst • t‖ / z.fst ≤ r₁) :
    supportExcess μ P z ≤ C * ‖z.snd - z.fst • t‖ ^ 2 / z.fst + z.fst * E := by
  set h := z.fst⁻¹ • z.snd - t with hh
  have hth : t + h = z.fst⁻¹ • z.snd := by rw [hh]; abel
  have hnorm : ‖h‖ = ‖z.snd - z.fst • t‖ / z.fst := by
    rw [hh, show z.fst⁻¹ • z.snd - t = z.fst⁻¹ • (z.snd - z.fst • t) by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hz.ne', one_smul], norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hz), inv_mul_eq_div]
  have hb := hup h (by rw [hnorm]; exact hr)
  rw [hth, hnorm] at hb
  conv_lhs => rw [Proofs.Geometry.eq_smul_slopeVec z hz.ne']
  rw [supportExcess_smul μ P _ hz.le]
  calc z.fst * supportExcess μ P (slopeVec (z.fst⁻¹ • z.snd))
      ≤ z.fst * (C * (‖z.snd - z.fst • t‖ / z.fst) ^ 2 + E) :=
        mul_le_mul_of_nonneg_left hb hz.le
    _ = _ := by field_simp

/-- The excess is bounded on the ball of radius `ρ ≤ L/2` around a point `y` with `y₁ = L` and
`|y_⊥ − L t| ≤ σ`, for `|t| ≤ T`: by `2C (σ + (1 + T)ρ)²/L + 3C L |t − t₀|^{2+δ}`, if the
slopes stay within `r₁` of `t`. -/
theorem supportExcess_le_of_mem_ball {μ : PtNorm m} {P : Pt m} {t t₀ : EuclideanSpace ℝ (Fin m)}
    {C r₁ δ T : ℝ} (hC : 0 ≤ C)
    (hup : ∀ h : EuclideanSpace ℝ (Fin m), ‖h‖ ≤ r₁ →
      supportExcess μ P (slopeVec (t + h)) ≤ C * ‖h‖ ^ 2 + C * ‖t - t₀‖ ^ (2 + δ))
    {y : Pt m} {L σ ρ : ℝ} (hL : 0 < L) (hyL : y.fst = L) (hσ : ‖y.snd - L • t‖ ≤ σ)
    (hρ : 0 ≤ ρ) (hρL : ρ ≤ L / 2) (hT : ‖t‖ ≤ T) (hsmall : 2 * (σ + (1 + T) * ρ) / L ≤ r₁)
    {z : Pt m} (hz : ‖z - y‖ ≤ ρ) :
    supportExcess μ P z ≤ 2 * C * (σ + (1 + T) * ρ) ^ 2 / L + 3 * C * L * ‖t - t₀‖ ^ (2 + δ) := by
  have hT0 : 0 ≤ T := (norm_nonneg t).trans hT
  have hfst : |z.fst - L| ≤ ρ := by
    have := Proofs.Geometry.abs_fst_le_norm (z - y)
    rw [WithLp.sub_fst, hyL] at this
    exact this.trans hz
  have hsnd : ‖(z - y).snd‖ ≤ ρ := (WithLp.norm_snd_le (x := z - y)).trans hz
  rw [WithLp.sub_snd] at hsnd
  have hz1 : L / 2 ≤ z.fst := by linarith only [(abs_le.mp hfst).1, hρL]
  have hz2 : z.fst ≤ 3 / 2 * L := by linarith only [(abs_le.mp hfst).2, hρL]
  have hz0 : 0 < z.fst := by linarith only [hz1, hL]
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans hσ
  have hS0 : 0 ≤ σ + (1 + T) * ρ := by positivity
  have hdev : ‖z.snd - z.fst • t‖ ≤ σ + (1 + T) * ρ := by
    have : z.snd - z.fst • t = (z.snd - y.snd) + (y.snd - L • t) + (L - z.fst) • t := by
      rw [sub_smul]; abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
    have : |z.fst - L| * ‖t‖ ≤ ρ * T := mul_le_mul hfst hT (norm_nonneg _) hρ
    linarith only [this, hsnd, hσ]
  have hslope : ‖z.snd - z.fst • t‖ / z.fst ≤ r₁ := by
    have : ‖z.snd - z.fst • t‖ / z.fst ≤ 2 * (σ + (1 + T) * ρ) / L := by
      rw [div_le_div_iff₀ hz0 hL]
      have k1 := mul_le_mul_of_nonneg_right hdev hL.le
      have k2 := mul_le_mul_of_nonneg_left hz1 hS0
      linarith only [k1, k2]
    linarith only [this, hsmall]
  refine (supportExcess_le hup hz0 hslope).trans ?_
  have hpow := Real.rpow_nonneg (norm_nonneg (t - t₀)) (2 + δ)
  have h1 : C * ‖z.snd - z.fst • t‖ ^ 2 / z.fst ≤ 2 * C * (σ + (1 + T) * ρ) ^ 2 / L := by
    rw [div_le_div_iff₀ hz0 hL]
    have hsq : ‖z.snd - z.fst • t‖ ^ 2 ≤ (σ + (1 + T) * ρ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hdev 2
    have k1 : ‖z.snd - z.fst • t‖ ^ 2 * L ≤ (σ + (1 + T) * ρ) ^ 2 * (2 * z.fst) :=
      mul_le_mul hsq (by linarith only [hz1]) hL.le (sq_nonneg _)
    have k2 := mul_le_mul_of_nonneg_left k1 hC
    linarith only [k2]
  have h2 : z.fst * (C * ‖t - t₀‖ ^ (2 + δ)) ≤ 3 * C * L * ‖t - t₀‖ ^ (2 + δ) := by
    have h0 : 0 ≤ C * ‖t - t₀‖ ^ (2 + δ) := mul_nonneg hC hpow
    have := mul_le_mul_of_nonneg_right hz2 h0
    have h0' : 0 ≤ L * (C * ‖t - t₀‖ ^ (2 + δ)) := mul_nonneg hL.le h0
    linarith only [this, h0']
  linarith only [h1, h2]

end CurvatureVariance.Paper.Localization.Modulus
