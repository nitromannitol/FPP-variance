/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.SlabsCone
public import CurvatureVariance.Paper.Proofs.Geometry.SlabSurgery
public import CurvatureVariance.Paper.Proofs.Geometry.SlabsProb

/-!
# Lemma `lem:slabs` (1): small slopes and positive first coordinates

Two facts for the proof of Lemma `lem:slabs`, where, outside the balls of
radius `K₁S²` around `u` and `v`, the two cone bounds keep a nearly optimal path within the
aperture `aperture T`, `T = bd.T + 1 ≥ ‖t₀‖ + 1`, of `(1, t)` from both endpoints, hence strictly
between the faces (`slabOneAt_of`, `Proofs.Geometry.SlabsFirstPart`):

* `exists_slope_small`: for `N` large, slope deviations `‖t − t₀‖ ≤ Cs n^{δ/100−1/4}` with
  `n ≥ √N` satisfy `‖t − t₀‖ ≤ ε` and `‖t − t₀‖^{δ/2} log N ≤ ε`;
* `fst_pos_of_coneBound`: a cone bound far from the endpoint gives an angle within the aperture,
  so the first coordinate is positive.
-/

@[expose] public section

open InnerProductGeometry
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- For `N` large, vectors `‖t‖ ≤ Cs n^{δ/100−1/4}` with `n ≥ √N` have `‖t‖ ≤ ε` and
`‖t‖^{δ/2} log N ≤ ε`. In the proof of Lemma `lem:slabs` it is applied to the slope deviation
`t − t₀`. -/
theorem exists_slope_small {Cs δ ε : ℝ} (hCs : 0 ≤ Cs) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, Real.sqrt N ≤ n →
      ∀ t : EuclideanSpace ℝ (Fin m), ‖t‖ ≤ Cs * (n : ℝ) ^ (δ / 100 - 1 / 4) →
        ‖t‖ ≤ ε ∧ ‖t‖ ^ (δ / 2) * Real.log N ≤ ε := by
  set κ := (1 / 4 - δ / 100) / 2 with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  obtain ⟨N₁, hN₁⟩ := exists_nat_rpow_neg_le hκ (ε := ε / (Cs + 1)) (by positivity)
  obtain ⟨N₂, hN₂⟩ := exists_nat_rpow_neg_mul_log_le (r := κ * (δ / 2)) (by positivity)
    (ε := ε / ((Cs + 1) ^ (δ / 2))) (by positivity)
  refine ⟨max (max N₁ N₂) 1, fun N hN n hn t ht => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast this
  have htκ : ‖t‖ ≤ (Cs + 1) * (N : ℝ) ^ (-κ) := by
    have := rpow_le_rpow_neg_of_sqrt_le hδ1 hNpos hn
    rw [← hκdef] at this
    have h0 : 0 ≤ (N : ℝ) ^ (-κ) := Real.rpow_nonneg hNpos.le _
    calc ‖t‖ ≤ Cs * (n : ℝ) ^ (δ / 100 - 1 / 4) := ht
      _ ≤ Cs * (N : ℝ) ^ (-κ) := mul_le_mul_of_nonneg_left this hCs
      _ ≤ (Cs + 1) * (N : ℝ) ^ (-κ) := by linarith
  refine ⟨?_, ?_⟩
  · have h := hN₁ N hN1
    rw [le_div_iff₀ (by positivity)] at h
    linarith [mul_comm (Cs + 1) ((N : ℝ) ^ (-κ))]
  · have h1 : ‖t‖ ^ (δ / 2) ≤ ((Cs + 1) * (N : ℝ) ^ (-κ)) ^ (δ / 2) :=
      Real.rpow_le_rpow (norm_nonneg _) htκ (by positivity)
    have h2 : ((Cs + 1) * (N : ℝ) ^ (-κ)) ^ (δ / 2) =
        (Cs + 1) ^ (δ / 2) * (N : ℝ) ^ (-(κ * (δ / 2))) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hNpos.le _),
        ← Real.rpow_mul hNpos.le, neg_mul]
    have h3 := hN₂ N hN2
    rw [le_div_iff₀ (by positivity)] at h3
    rcases le_or_gt (Real.log N) 0 with hl | hl
    · have : 0 ≤ ‖t‖ ^ (δ / 2) := Real.rpow_nonneg (norm_nonneg _) _
      nlinarith only [this, hl, hε]
    · calc ‖t‖ ^ (δ / 2) * Real.log N
          ≤ (Cs + 1) ^ (δ / 2) * (N : ℝ) ^ (-(κ * (δ / 2))) * Real.log N := by
            rw [← h2]; exact mul_le_mul_of_nonneg_right h1 hl.le
        _ = (N : ℝ) ^ (-(κ * (δ / 2))) * Real.log N * (Cs + 1) ^ (δ / 2) := by ring
        _ ≤ ε := h3

/-- **A cone bound far from the endpoint gives a small angle**: with `q = aperture T / 2`, if
`(C/q)⁴ ≤ K₁`, `K₁ ≥ C`, `‖t‖ ≤ T` and `C ‖t − t₀‖^{1+δ/2} log N ≤ q`, then at distance at least
`K₁S²` the angle is at most `aperture T`, so the first coordinate is positive. -/
theorem fst_pos_of_coneBound {M : Model m} {C S K₁ T : ℝ} {N : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {a : Pt m} (hC : 0 < C) (hS : 1 ≤ S) (hK₁ : C ≤ K₁)
    (hK₁' : (C / (aperture T / 2)) ^ 4 ≤ K₁) (htT : ‖t‖ ≤ T)
    (htlog : C * (‖t - M.t₀‖ ^ (1 + M.δ / 2) * Real.log N) ≤ aperture T / 2)
    (hcb : ConeBound M C S N t a) (ha : K₁ * S ^ 2 ≤ ‖a‖) : 0 < a.fst := by
  have hT : 0 ≤ T := (norm_nonneg t).trans htT
  set q := aperture T / 2 with hqdef
  have hq : 0 < q := by have := aperture_pos hT; positivity
  have hS2 : 0 < S ^ 2 := by positivity
  have hK₁0 : 0 < K₁ := lt_of_lt_of_le hC hK₁
  have ha0 : 0 < ‖a‖ := lt_of_lt_of_le (by positivity) ha
  have hangle := hcb ((mul_le_mul_of_nonneg_right hK₁ hS2.le).trans ha)
  -- `S^{1/2} ‖a‖^{-1/4} ≤ q / C`
  set x := S ^ ((1 : ℝ) / 2) * ‖a‖ ^ (-(1 : ℝ) / 4) with hx
  have hx0 : 0 ≤ x := by positivity
  have e1 : (S ^ ((1 : ℝ) / 2)) ^ 4 = S ^ 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℕ) = 2 * 2 by rfl, pow_mul,
      Real.sq_sqrt (by linarith)]
  have e2 : (‖a‖ ^ (-(1 : ℝ) / 4)) ^ 4 = ‖a‖⁻¹ := by
    rw [← Real.rpow_mul_natCast ha0.le, ← Real.rpow_neg_one]
    norm_num
  have hx4 : x ^ 4 = S ^ 2 / ‖a‖ := by
    rw [hx, mul_pow, e1, e2, div_eq_mul_inv]
  have hCx : C * x ≤ q := by
    have h1 : (C * x) ^ 4 ≤ q ^ 4 := by
      rw [mul_pow, hx4]
      have h2 : C ^ 4 * S ^ 2 ≤ q ^ 4 * (K₁ * S ^ 2) := by
        have : C ^ 4 ≤ q ^ 4 * K₁ := by
          have h8 : (C / q) ^ 4 = C ^ 4 / q ^ 4 := by rw [div_pow]
          rw [h8, div_le_iff₀ (by positivity)] at hK₁'
          linarith
        have := mul_le_mul_of_nonneg_right this hS2.le
        linarith
      calc C ^ 4 * (S ^ 2 / ‖a‖) = C ^ 4 * S ^ 2 / ‖a‖ := by ring
        _ ≤ q ^ 4 * (K₁ * S ^ 2) / ‖a‖ := div_le_div_of_nonneg_right h2 ha0.le
        _ ≤ q ^ 4 * ‖a‖ / ‖a‖ :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by positivity)) ha0.le
        _ = q ^ 4 := by field_simp
    exact (pow_le_pow_iff_left₀ (by positivity) hq.le (by norm_num)).1 h1
  have hθ : angle a (slopeVec t) ≤ aperture T := by
    refine hangle.trans ?_
    rw [mul_add]
    linarith
  exact (fst_pos_and_norm_slope_sub_le htT hθ (le_refl _)).1

end CurvatureVariance.Paper.Proofs.Geometry
