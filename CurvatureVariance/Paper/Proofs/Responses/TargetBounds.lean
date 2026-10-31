/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Targets
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deterministic bounds for the targets of Section `sec:gain`

The target domain controls the slope and all transverse coordinates. Admissibility then gives a
linear bound for the length of a coordinate competitor in every slab.
-/

@[expose] public section

open Set

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- Each transverse coordinate is bounded by its Euclidean norm. -/
theorem abs_coord_le_norm_transversePoint (y : Fin m → ℤ) (j : Fin m) :
    |(y j : ℝ)| ≤ ‖transversePoint y‖ := by
  simpa only [Real.norm_eq_abs, transversePoint, WithLp.ofLp_toLp] using PiLp.norm_apply_le (transversePoint y) j

/-- The centered target norm is at most its longitudinal length. -/
theorem target_centered_norm_le_length {M : Model m} (hM : M.Standing) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {y : Fin m → ℤ} (hy : y ∈ premiseDomain M ℓ) :
    ‖transversePoint y - (ℓ : ℝ) • M.t₀‖ ≤ ℓ :=
  hy.trans (Real.rpow_le_self_of_one_le (by exact_mod_cast hℓ) (by linarith [hM.delta_le_one]))

/-- The transverse norm of a target is at most `(1 + |t₀|) ℓ`. -/
theorem target_norm_le_length {M : Model m} (hM : M.Standing) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {y : Fin m → ℤ} (hy : y ∈ premiseDomain M ℓ) :
    ‖transversePoint y‖ ≤ (1 + ‖M.t₀‖) * ℓ := by
  have ht := norm_add_le (transversePoint y - (ℓ : ℝ) • M.t₀) ((ℓ : ℝ) • M.t₀)
  rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg ℓ)] at ht
  linarith only [ht, target_centered_norm_le_length hM hℓ hy]

/-- Centering the target slope commutes with division by its length. -/
theorem targetSlope_sub_eq {M : Model m} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (y : Fin m → ℤ) :
    targetSlope ℓ y - M.t₀ = (ℓ : ℝ)⁻¹ • (transversePoint y - (ℓ : ℝ) • M.t₀) := by
  have hne : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul, targetSlope]

/-- The target slope lies within one of the fixed center slope. -/
theorem targetSlope_sub_norm_le_one {M : Model m} (hM : M.Standing) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {y : Fin m → ℤ} (hy : y ∈ premiseDomain M ℓ) : ‖targetSlope ℓ y - M.t₀‖ ≤ 1 := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  rw [targetSlope_sub_eq hℓ, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hℓpos)]
  exact (mul_le_mul_of_nonneg_left (target_centered_norm_le_length hM hℓ hy)
    (inv_nonneg.mpr hℓpos.le)).trans_eq (inv_mul_cancel₀ hℓpos.ne')

/-- The target slope has norm at most `|t₀| + 1`. -/
theorem targetSlope_norm_le_base_add_one {M : Model m} (hM : M.Standing) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {y : Fin m → ℤ} (hy : y ∈ premiseDomain M ℓ) : ‖targetSlope ℓ y‖ ≤ ‖M.t₀‖ + 1 := by
  have ht := norm_add_le (targetSlope ℓ y - M.t₀) M.t₀
  rw [sub_add_cancel] at ht
  linarith only [ht, targetSlope_sub_norm_le_one hM hℓ hy]

/-- The centered slope bound needed for the slab restriction estimate. -/
theorem targetSlope_norm_le_rpow {M : Model m} (hM : M.Standing) {n ℓ : ℕ}
    (hn : 1 ≤ n) (hnℓ : n ≤ ℓ) {y : Fin m → ℤ} (hy : y ∈ premiseDomain M ℓ) :
    ‖targetSlope ℓ y - M.t₀‖ ≤ (n : ℝ) ^ (M.δ / 100 - 1 / 4) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hℓpos : (0 : ℝ) < ℓ := hnpos.trans_le (by exact_mod_cast hnℓ)
  rw [targetSlope_sub_eq (by omega : 1 ≤ ℓ), norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hℓpos)]
  calc
    _ ≤ (ℓ : ℝ)⁻¹ * (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) :=
      mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hℓpos.le)
    _ = (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hℓpos]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hnpos (by exact_mod_cast hnℓ)
      (by linarith [hM.delta_le_one])

/-- Target endpoints lie in the box `[−3(1 + |t₀|)N, 3(1 + |t₀|)N]^d` of the slab estimate. -/
theorem target_inBox {M : Model m} (hM : M.Standing) {ℓ N : ℕ} (hℓ : 1 ≤ ℓ)
    (hℓN : ℓ ≤ N) {y : Fin m → ℤ} (hy : y ∈ premiseDomain M ℓ) :
    InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) ((ℓ : ℤ), y) := by
  have hℓN' : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓN
  have hN := Nat.cast_nonneg (α := ℝ) N
  have hbound : (1 + ‖M.t₀‖) * ℓ ≤ (1 + ‖M.t₀‖) * N :=
    mul_le_mul_of_nonneg_left hℓN' (by positivity)
  constructor
  · change |((ℓ : ℤ) : ℝ)| ≤ _
    simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) ℓ)]
    nlinarith only [hℓN', hN, norm_nonneg M.t₀]
  · intro j
    have h := (abs_coord_le_norm_transversePoint y j).trans (target_norm_le_length hM hℓ hy)
    nlinarith only [h, hbound, hN, norm_nonneg M.t₀]

/-- For a slope `|t| ≤ |t₀| + 1`, the transverse increments of an admissible tuple have norm at
most `(2 + |t₀|) n`. -/
theorem norm_increment_le_base_mul {M : Model m} (hM : M.Standing) {n K : ℕ}
    (hn : 1 ≤ n) {t : EuclideanSpace ℝ (Fin m)} (ht : ‖t‖ ≤ ‖M.t₀‖ + 1) {u v : Vertex m}
    {Y : Fin (K + 1) → Fin m → ℤ} (hY : IsAdmissibleTuple M n K t u v Y) (i : Fin K) :
    ‖transversePoint (Y i.succ - Y i.castSucc)‖ ≤ (2 + ‖M.t₀‖) * n := by
  have htri := norm_add_le
    (transversePoint (Y i.succ - Y i.castSucc) - (n : ℝ) • t) ((n : ℝ) • t)
  rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)] at htri
  have hr := Real.rpow_le_self_of_one_le (by exact_mod_cast hn : (1 : ℝ) ≤ n)
    (show (3 : ℝ) / 4 + M.δ / 100 ≤ 1 by linarith [hM.delta_le_one])
  have hmul := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hinc := hY.2.2 i
  linarith only [htri, hr, hmul, hinc]

/-- The geometric endpoint identity required by the slab contract. -/
theorem target_point_sub {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (y : Fin m → ℤ) :
    point ((ℓ : ℤ), y) - point (0 : Vertex m) = (ℓ : ℝ) • slopeVec (targetSlope ℓ y) := by
  have hℓne : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hℓ))
  rw [Infra.FPP.point_zero, sub_zero]
  apply Infra.FPP.pt_ext
  · change (ℓ : ℝ) = (ℓ : ℝ) * 1
    exact (mul_one _).symm
  · change transversePoint y = (ℓ : ℝ) • ((ℓ : ℝ)⁻¹ • transversePoint y)
    rw [smul_smul, mul_inv_cancel₀ hℓne, one_smul]

/-- A sufficiently large target has slab width at least `√N`, and hence at least two. -/
theorem target_size_bounds {M : Model m} {K N n ℓ : ℕ} {y : Fin m → ℤ}
    (hK : 1 ≤ K) (hN : (9 * K) ^ 2 ≤ N) (htar : IsTarget M K N n ℓ y) :
    2 ≤ n ∧ Real.sqrt N ≤ n ∧ n ≤ ℓ ∧ 1 ≤ ℓ := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hN' : (9 * (K : ℝ)) ^ 2 ≤ N := by exact_mod_cast hN
  have hNkn : (N : ℝ) ≤ 9 * K * n := by
    have h := htar.2.1
    rw [htar.1, Nat.cast_mul] at h
    linarith only [h]
  have hnK : 9 * (K : ℝ) ≤ n := by nlinarith only [hN', hNkn, hKpos]
  have hn2 : 2 ≤ n := by
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
    exact_mod_cast (show (2 : ℝ) ≤ n by linarith only [hnK, hK'])
  have hsq : (N : ℝ) ≤ (n : ℝ) ^ 2 :=
    hNkn.trans (by nlinarith only [hnK, Nat.cast_nonneg (α := ℝ) n])
  have hnℓ : n ≤ ℓ := by rw [htar.1]; exact Nat.le_mul_of_pos_left n (by omega)
  exact ⟨hn2, (Real.sqrt_le_iff).mpr ⟨Nat.cast_nonneg n, hsq⟩, hnℓ, by omega⟩

end CurvatureVariance.Paper.Responses
