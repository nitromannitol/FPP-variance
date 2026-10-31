/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Proofs.ShortLengths.Translate
public import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes
public import CurvatureVariance.Infra.Os.Sum
public import CurvatureVariance.Infra.FPP.Model
public import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes
public import CurvatureVariance.Paper.Proofs.Moments.Shear
import Mathlib.Analysis.MeanInequalitiesPow
import CurvatureVariance.Paper.Proofs.Moments.Basic
import CurvatureVariance.Paper.Proofs.Moments.Links

/-!
# Proposition `prop:profiles`: the deterministic estimates

* Powers of `s`: `W_s ≤ 16 W_r` for `s ≤ 16 r`; `Q_{s'} ≤ 2 Q_s` for `s' ≤ 2s`;
  `log² N ≤ 100 Q_s` for `s ≥ √N`; `s x^{2+δ} ≤ Q_s` for `x ≤ s^{δ/100−1/4}` (used with
  `x = |t − t₀|`); and
  `(4/5) s^{δ/100−1/4} ≤ (24/25) λ^{δ/100−1/4}` for `λ ≤ 2s`.
* Geometry: two points of the thickened cubes differ by `λ(1, t) + w` with `|λ − s|` at most twice
  the thickening and `|w| ≤ √m bW_s + 4√d` (`exists_decomp_of_thicken`); the rounded connector
  endpoints are linked by `λ(1, t) + (0, c' − c − st)` up to `√d` (`norm_round_link_le`).
* The cost from equation `eq:support`: `μ(v) − P_t·v ≤ (2(2 + |t₀|)² CB² + 2C) Q_s` for
  `v = λ(1, t) + w`, `|λ − s| ≤ s/4`, `|w| ≤ B W_s` and `4(2 + |t₀|) B W_s ≤ ρ s` for
  `ρ ≤ min(r₁, 1)`, at slopes `|t − t₀| ≤ ρ/2` (`cost_le_Q`).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.ShortLengths

open CurvatureVariance.Paper

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ### Powers of `s` -/

theorem five_sixths_le_two_rpow {e : ℝ} (he : -(1 / 4) ≤ e) : (5 / 6 : ℝ) ≤ 2 ^ e := by
  have h1 : (5 / 6 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
    calc (5 / 6 : ℝ) = ((5 / 6 : ℝ) ^ (4 : ℕ)) ^ (((4 : ℕ) : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
      _ ≤ (2⁻¹ : ℝ) ^ (((4 : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) (by norm_num) (by positivity)
      _ = (2⁻¹ : ℝ) ^ (1 / 4 : ℝ) := by norm_num
  exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) he)

/-- The slope `(4/5) s^{δ/100−1/4}` is at most `(24/25) λ^{δ/100−1/4}` for `0 < λ ≤ 2s`. -/
theorem slope_le_of_le_two_mul {δ s lam : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam)
    (hls : lam ≤ 2 * s) :
    4 / 5 * s ^ (δ / 100 - 1 / 4) ≤ 24 / 25 * lam ^ (δ / 100 - 1 / 4) := by
  have hs : 0 < s := by linarith only [hlam, hls]
  have h1 : (2 * s) ^ (δ / 100 - 1 / 4) ≤ lam ^ (δ / 100 - 1 / 4) :=
    Real.rpow_le_rpow_of_nonpos hlam hls (by linarith only [hδ1])
  rw [Real.mul_rpow (by norm_num) hs.le] at h1
  have h2 := five_sixths_le_two_rpow (e := δ / 100 - 1 / 4) (by linarith only [hδ])
  have h3 : 0 ≤ s ^ (δ / 100 - 1 / 4) := Real.rpow_nonneg hs.le _
  nlinarith only [h1, h2, h3]

theorem Q_exp_bounds {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) :
    2 / 5 ≤ (1 : ℝ) / 2 - M.δ / K ∧ (1 : ℝ) / 2 - M.δ / K ≤ 1 / 2 := by
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  have hK' : (10 : ℝ) ^ 4 ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith only [hK']
  have h1 : M.δ / K ≤ 1 / 10 := by rw [div_le_iff₀ hKpos]; linarith only [hδ1, hK']
  have h2 : 0 ≤ M.δ / K := div_nonneg hδ.le hKpos.le
  constructor <;> linarith only [h1, h2]

theorem Q_nonneg {M : Model m} {K : ℕ} {A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) :
    0 ≤ Q M K A s :=
  mul_nonneg hA (Real.rpow_nonneg hs _)

theorem one_le_Q {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A s : ℝ}
    (hA : 1 ≤ A) (hs : 1 ≤ s) : 1 ≤ Q M K A s :=
  one_le_mul_of_one_le_of_one_le hA
    (Real.one_le_rpow hs (by linarith only [(Q_exp_bounds hM hK).1]))

theorem Q_le_Q {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A r s : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r) (hrs : r ≤ s) : Q M K A r ≤ Q M K A s :=
  mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hr hrs (by linarith only [(Q_exp_bounds hM hK).1])) hA

/-- `Q_{s'} ≤ 2 Q_s` for `s' ≤ 2s`. -/
theorem Q_le_two_mul {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A r s : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ 2 * s) :
    Q M K A r ≤ 2 * Q M K A s := by
  obtain ⟨hq1, hq2⟩ := Q_exp_bounds hM hK
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hq2])
      _ = 2 := Real.rpow_one 2
  have hsq : 0 ≤ s ^ ((1 : ℝ) / 2 - M.δ / K) := Real.rpow_nonneg hs _
  calc Q M K A r ≤ Q M K A (2 * s) := Q_le_Q hM hK hA hr hrs
    _ = A * (2 ^ ((1 : ℝ) / 2 - M.δ / K) * s ^ ((1 : ℝ) / 2 - M.δ / K)) := by
        unfold Q; rw [Real.mul_rpow (by norm_num) hs]
    _ ≤ A * (2 * s ^ ((1 : ℝ) / 2 - M.δ / K)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hsq) hA
    _ = 2 * Q M K A s := by unfold Q; ring

theorem W_sq {M : Model m} {K : ℕ} {A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) :
    W M K A s ^ 2 = s * Q M K A s :=
  Real.sq_sqrt (mul_nonneg hs (Q_nonneg hA hs))

theorem one_le_W {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A s : ℝ}
    (hA : 1 ≤ A) (hs : 1 ≤ s) : 1 ≤ W M K A s :=
  Real.one_le_sqrt.mpr (one_le_mul_of_one_le_of_one_le hs (one_le_Q hM hK hA hs))

/-- `W_s ≤ 16 W_r` for `s ≤ 16 r`. -/
theorem W_le_sixteen_mul {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A r s : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r) (hs : 0 ≤ s) (hsr : s ≤ 16 * r) :
    W M K A s ≤ 16 * W M K A r := by
  obtain ⟨hq1, hq2⟩ := Q_exp_bounds hM hK
  have h16 : (16 : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ 16 := by
    calc (16 : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ 16 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hq2])
      _ = 16 := Real.rpow_one 16
  have hrq : 0 ≤ r ^ ((1 : ℝ) / 2 - M.δ / K) := Real.rpow_nonneg hr _
  have hQ : Q M K A s ≤ 16 * Q M K A r := by
    calc Q M K A s ≤ Q M K A (16 * r) := Q_le_Q hM hK hA hs hsr
      _ = A * (16 ^ ((1 : ℝ) / 2 - M.δ / K) * r ^ ((1 : ℝ) / 2 - M.δ / K)) := by
          unfold Q; rw [Real.mul_rpow (by norm_num) hr]
      _ ≤ A * (16 * r ^ ((1 : ℝ) / 2 - M.δ / K)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h16 hrq) hA
      _ = 16 * Q M K A r := by unfold Q; ring
  have h1 : s * Q M K A s ≤ 16 ^ 2 * (r * Q M K A r) := by
    calc s * Q M K A s ≤ (16 * r) * (16 * Q M K A r) :=
          mul_le_mul hsr hQ (Q_nonneg hA hs) (by positivity)
      _ = 16 ^ 2 * (r * Q M K A r) := by ring
  unfold W
  calc Real.sqrt (s * Q M K A s) ≤ Real.sqrt (16 ^ 2 * (r * Q M K A r)) := Real.sqrt_le_sqrt h1
    _ = 16 * Real.sqrt (r * Q M K A r) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- `log² N ≤ 100 Q_s` for `s ≥ √N`: `log N ≤ 10 N^{1/10}` and `N^{1/5} ≤ s^{2/5} ≤ Q_s`. -/
theorem log_sq_le_Q {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {N : ℕ} (hN : 1 ≤ N) {s : ℝ} (hs : Real.sqrt N ≤ s) :
    Real.log N ^ 2 ≤ 100 * Q M K A s := by
  obtain ⟨hq1, hq2⟩ := Q_exp_bounds hM hK
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs1 : 1 ≤ s := (Real.one_le_sqrt.mpr hN1).trans hs
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlog : Real.log N ≤ 10 * (N : ℝ) ^ ((1 : ℝ) / 10) := by
    have h := Real.log_le_rpow_div hN0 (by norm_num : (0 : ℝ) < 1 / 10)
    rw [div_div_eq_mul_div, div_one] at h
    linarith only [h]
  have hsq : ((N : ℝ) ^ ((1 : ℝ) / 10)) ^ 2 = (N : ℝ) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hNs : (N : ℝ) ^ ((1 : ℝ) / 5) ≤ s ^ ((1 : ℝ) / 2 - M.δ / K) := by
    have h1 : (N : ℝ) ^ ((1 : ℝ) / 5) = (Real.sqrt N) ^ ((2 : ℝ) / 5) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0]; norm_num
    rw [h1]
    calc (Real.sqrt N) ^ ((2 : ℝ) / 5) ≤ s ^ ((2 : ℝ) / 5) :=
          Real.rpow_le_rpow (Real.sqrt_nonneg _) hs (by norm_num)
      _ ≤ s ^ ((1 : ℝ) / 2 - M.δ / K) := Real.rpow_le_rpow_of_exponent_le hs1 hq1
  have hQ : s ^ ((1 : ℝ) / 2 - M.δ / K) ≤ Q M K A s :=
    le_mul_of_one_le_left (Real.rpow_nonneg (zero_le_one.trans hs1) _) hA
  calc Real.log N ^ 2 ≤ (10 * (N : ℝ) ^ ((1 : ℝ) / 10)) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
    _ = 100 * (N : ℝ) ^ ((1 : ℝ) / 5) := by rw [mul_pow, hsq]; norm_num
    _ ≤ 100 * Q M K A s := mul_le_mul_of_nonneg_left (hNs.trans hQ) (by norm_num)

/-- `s x^{2+δ} ≤ Q_s` for `0 ≤ x ≤ s^{δ/100−1/4}` (used with `x = |t − t₀|`), since
`1 + (δ/100 − 1/4)(2 + δ) ≤ 1/2 − δ/K`. -/
theorem mul_rpow_slope_le_Q {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {s x : ℝ} (hs : 1 ≤ s) (hx0 : 0 ≤ x) (hx : x ≤ s ^ (M.δ / 100 - 1 / 4)) :
    s * x ^ (2 + M.δ) ≤ Q M K A s := by
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  have hK' : (10 : ℝ) ^ 4 ≤ K := by exact_mod_cast hK
  have hs0 : 0 < s := by linarith only [hs]
  have h1 : x ^ (2 + M.δ) ≤ (s ^ (M.δ / 100 - 1 / 4)) ^ (2 + M.δ) :=
    Real.rpow_le_rpow hx0 hx (by linarith only [hδ])
  rw [← Real.rpow_mul hs0.le] at h1
  have h2 : s * s ^ ((M.δ / 100 - 1 / 4) * (2 + M.δ)) =
      s ^ (1 + (M.δ / 100 - 1 / 4) * (2 + M.δ)) := by
    rw [Real.rpow_add hs0, Real.rpow_one]
  have hexp : 1 + (M.δ / 100 - 1 / 4) * (2 + M.δ) ≤ 1 / 2 - M.δ / K := by
    have h3 : M.δ / K ≤ M.δ / 10 ^ 4 := div_le_div_of_nonneg_left hδ.le (by norm_num) hK'
    have h4 : M.δ ^ 2 ≤ M.δ := by rw [sq]; exact mul_le_of_le_one_left hδ.le hδ1
    linarith only [h3, h4, hδ]
  calc s * x ^ (2 + M.δ) ≤ s * s ^ ((M.δ / 100 - 1 / 4) * (2 + M.δ)) :=
        mul_le_mul_of_nonneg_left h1 hs0.le
    _ = s ^ (1 + (M.δ / 100 - 1 / 4) * (2 + M.δ)) := h2
    _ ≤ s ^ ((1 : ℝ) / 2 - M.δ / K) := Real.rpow_le_rpow_of_exponent_le hs hexp
    _ ≤ Q M K A s := le_mul_of_one_le_left (Real.rpow_nonneg hs0.le _) hA

/-! ### Geometry of the thickened cubes and of the connector endpoints -/

theorem norm_toLp_zero_le (y : E) : ‖(WithLp.toLp 2 ((0 : ℝ), y) : Pt m)‖ ≤ ‖y‖ := by
  have h := Moments.norm_le_abs_fst_add_norm_snd (WithLp.toLp 2 ((0 : ℝ), y) : Pt m)
  have h1 : (WithLp.toLp 2 ((0 : ℝ), y) : Pt m).fst = 0 := rfl
  have h2 : (WithLp.toLp 2 ((0 : ℝ), y) : Pt m).snd = y := rfl
  rw [h1, h2, abs_zero, zero_add] at h
  exact h

theorem toLp_sub_toLp_eq (p : ℤ) (s : ℕ) (c c' t : E) :
    (WithLp.toLp 2 ((((p + s : ℤ) : ℝ)), c') : Pt m) - WithLp.toLp 2 (((p : ℝ)), c) =
      (s : ℝ) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), c' - c - (s : ℝ) • t) := by
  apply Infra.FPP.pt_ext
  · simp only [WithLp.sub_fst, WithLp.add_fst, WithLp.smul_fst]
    change ((p + s : ℤ) : ℝ) - p = (s : ℝ) * 1 + 0
    push_cast; ring
  · simp only [WithLp.sub_snd, WithLp.add_snd, WithLp.smul_snd]
    change c' - c = (s : ℝ) • t + (c' - c - (s : ℝ) • t)
    abel

/-- The inner link `c + r(1, t) → c' − r(1, t)`, of length `s − 2r`. -/
theorem link_inner_eq (p : ℤ) (s : ℕ) (c c' t : E) (r : ℝ) :
    (WithLp.toLp 2 ((((p + s : ℤ) : ℝ)), c') - r • slopeVec t : Pt m) -
        (WithLp.toLp 2 (((p : ℝ)), c) + r • slopeVec t) =
      ((s : ℝ) - 2 * r) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), c' - c - (s : ℝ) • t) := by
  have h := toLp_sub_toLp_eq p s c c' t
  have h' : (WithLp.toLp 2 ((((p + s : ℤ) : ℝ)), c') : Pt m) = WithLp.toLp 2 (((p : ℝ)), c) +
      ((s : ℝ) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), c' - c - (s : ℝ) • t)) := by
    rw [← h]; abel
  rw [h']
  module

/-- The outer link `c − r(1, t) → c' + r(1, t)`, of length `s + 2r`. -/
theorem link_outer_eq (p : ℤ) (s : ℕ) (c c' t : E) (r : ℝ) :
    (WithLp.toLp 2 ((((p + s : ℤ) : ℝ)), c') + r • slopeVec t : Pt m) -
        (WithLp.toLp 2 (((p : ℝ)), c) - r • slopeVec t) =
      ((s : ℝ) + 2 * r) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), c' - c - (s : ℝ) • t) := by
  have h := toLp_sub_toLp_eq p s c c' t
  have h' : (WithLp.toLp 2 ((((p + s : ℤ) : ℝ)), c') : Pt m) = WithLp.toLp 2 (((p : ℝ)), c) +
      ((s : ℝ) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), c' - c - (s : ℝ) • t)) := by
    rw [← h]; abel
  rw [h']
  module

/-- Rounding both ends of a link `Z → Z'` moves the displacement by at most `√d`. -/
theorem norm_round_link_le {Z Z' : Pt m} {lam : ℝ} {t ω : E}
    (h : Z' - Z = lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω)) :
    ‖(point (Moments.roundVertex Z') - point (Moments.roundVertex Z)) -
        (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω))‖ ≤ Real.sqrt ((m : ℝ) + 1) := by
  rw [← h]
  have h1 := Moments.norm_point_roundVertex_sub_le Z'
  have h2 := Moments.norm_point_roundVertex_sub_le Z
  have heq : (point (Moments.roundVertex Z') - point (Moments.roundVertex Z)) - (Z' - Z) =
      (point (Moments.roundVertex Z') - Z') - (point (Moments.roundVertex Z) - Z) := by abel
  rw [heq]
  linarith only [h1, h2,
    norm_sub_le (point (Moments.roundVertex Z') - Z') (point (Moments.roundVertex Z) - Z)]

/-- A displacement within `ε` of `λ(1, t) + (0, ω)` is `λ(1, t) + w` with `|w| ≤ |ω| + ε`. -/
theorem exists_decomp_of_link {x : Pt m} {lam ε : ℝ} {t ω : E}
    (h : ‖x - (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω))‖ ≤ ε) :
    ∃ w : Pt m, x = lam • slopeVec t + w ∧ ‖w‖ ≤ ‖ω‖ + ε := by
  refine ⟨x - lam • slopeVec t, by abel, ?_⟩
  have heq : x - lam • slopeVec t =
      (x - (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω))) + WithLp.toLp 2 ((0 : ℝ), ω) := by
    abel
  rw [heq]
  linarith only [h, norm_add_le (x - (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω)))
    (WithLp.toLp 2 ((0 : ℝ), ω) : Pt m), norm_toLp_zero_le ω]

/-- **Two points of the thickened cubes**: `v − u = λ(1, t) + w` with `|λ − s| ≤ 2ρ` and
`|w| ≤ √m w₀ + 4√d`, for cubes of sides at most `w₀`. -/
theorem exists_decomp_of_thicken {p : ℤ} {s : ℕ} {c c' t : E} {a a' wd ρ : ℝ} (ha : 0 ≤ a)
    (ha' : 0 ≤ a') (haw : a ≤ wd) (haw' : a' ≤ wd)
    (hcc : ‖c' - c - (s : ℝ) • t‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1)) {u v : Vertex m}
    (hu : u ∈ thicken (transverseCube p c a) t ρ)
    (hv : v ∈ thicken (transverseCube (p + s) c' a') t ρ) :
    ∃ lam : ℝ, ∃ w : Pt m, point v - point u = lam • slopeVec t + w ∧ |lam - s| ≤ 2 * ρ ∧
      ‖w‖ ≤ Real.sqrt m * wd + 4 * Real.sqrt ((m : ℝ) + 1) := by
  obtain ⟨u₀, hu₀, τ, hτ, hu⟩ := hu
  obtain ⟨v₀, hv₀, τ', hτ', hv⟩ := hv
  have hy := norm_transverse_sub_le_of_cubes ha ha' haw haw' hcc hu₀ hv₀
  set Y : Pt m := WithLp.toLp 2 ((0 : ℝ), transversePoint (v₀.2 - u₀.2) - (s : ℝ) • t) with hY
  have h0 : point v₀ - point u₀ = (s : ℝ) • slopeVec t + Y := by
    apply Infra.FPP.pt_ext
    · simp only [WithLp.sub_fst, WithLp.add_fst, WithLp.smul_fst, Infra.FPP.point_fst]
      rw [hv₀.1, hu₀.1]
      change ((p + s : ℤ) : ℝ) - p = (s : ℝ) * 1 + 0
      push_cast; ring
    · simp only [WithLp.sub_snd, WithLp.add_snd, WithLp.smul_snd, Infra.FPP.point_snd]
      change _ = (s : ℝ) • t + (transversePoint (v₀.2 - u₀.2) - (s : ℝ) • t)
      rw [Infra.FPP.transversePoint_sub]
      abel
  have hY' : Y = point v₀ - point u₀ - (s : ℝ) • slopeVec t := by rw [h0]; abel
  refine ⟨s + τ' - τ, (point v - (point v₀ + τ' • slopeVec t)) -
    (point u - (point u₀ + τ • slopeVec t)) + Y, ?_, ?_, ?_⟩
  · rw [hY']; module
  · have h1 := abs_le.mp hτ
    have h2 := abs_le.mp hτ'
    rw [show (s : ℝ) + τ' - τ - s = τ' - τ by ring]
    exact abs_le.mpr ⟨by linarith only [h1.2, h2.1], by linarith only [h1.1, h2.2]⟩
  · have hYn : ‖Y‖ ≤ ‖transversePoint (v₀.2 - u₀.2) - (s : ℝ) • t‖ := norm_toLp_zero_le _
    have h3 := norm_add_le ((point v - (point v₀ + τ' • slopeVec t)) -
      (point u - (point u₀ + τ • slopeVec t))) Y
    have h4 := norm_sub_le (point v - (point v₀ + τ' • slopeVec t))
      (point u - (point u₀ + τ • slopeVec t))
    linarith only [h3, h4, hYn, hy, hu, hv]

/-- The first term of `cost_le_Q`, over abstract reals. -/
private theorem cost_numeric_left {c y a b q s f : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 0 ≤ q) (h2 : y ≤ a * b * (s * q)) (hf : s / 2 ≤ f) :
    c * y ≤ 2 * a * c * b * q * f := by
  have a1 := mul_le_mul_of_nonneg_left h2 hc
  have a2 := mul_le_mul_of_nonneg_left hf (mul_nonneg (mul_nonneg (mul_nonneg ha hc) hb) hq)
  have e1 : c * (a * b * (s * q)) = 2 * (a * c * b * q * (s / 2)) := by ring
  have e2 : 2 * a * c * b * q * f = 2 * (a * c * b * q * f) := by ring
  linarith only [a1, a2, e1, e2]

/-! ### The cost from equation `eq:support` -/

/-- **The cost from equation `eq:support` at scale `s`.** For `v = λ(1, t) + w` with
`|λ − s| ≤ s/4`, `|w| ≤ B W_s`, `4 (2 + |t₀|) B W_s ≤ ρ s`, `ρ ≤ min(r₁, 1)`, `|t − t₀| ≤ ρ/2` and
`|t − t₀| ≤ s^{δ/100−1/4}`: `μ(v) − P_t·v ≤ (2 (2 + |t₀|)² C B² + 2 C) Q_s`. The transverse error
`v₂ − v₁ t = w₂ − w₁ t` is at most `(1 + |t|) |w| ≤ (2 + |t₀|) B W_s`. -/
theorem cost_le_Q {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ} (hA : 1 ≤ A)
    {cS CS r₁ : ℝ} (hCS : 0 < CS)
    (h24 : ∀ t h : E, ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        cS * ‖h‖ ^ 2 - CS * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            CS * ‖h‖ ^ 2 + CS * ‖t - M.t₀‖ ^ (2 + M.δ))
    {ρ : ℝ} (hρ : ρ ≤ r₁) (hρ1 : ρ ≤ 1) {t : E} {P : Pt m}
    (hP : IsSubgradient M.μ (slopeVec t) P) {s : ℝ} (hs : 1 ≤ s)
    (ht : ‖t - M.t₀‖ ≤ s ^ (M.δ / 100 - 1 / 4)) (htr : ‖t - M.t₀‖ ≤ ρ / 2) {B : ℝ}
    {lam : ℝ} {w v : Pt m} (hv : v = lam • slopeVec t + w)
    (hlam : |lam - s| ≤ s / 4) (hw : ‖w‖ ≤ B * W M K A s)
    (hBW : 4 * (2 + ‖M.t₀‖) * B * W M K A s ≤ ρ * s) :
    M.μ.1 v - inner ℝ P v ≤ (2 * (2 + ‖M.t₀‖) ^ 2 * CS * B ^ 2 + 2 * CS) * Q M K A s := by
  have hδ1 := hM.delta_le_one
  have hρ0 : 0 ≤ ρ := by linarith only [norm_nonneg (t - M.t₀), htr]
  set T := ‖M.t₀‖ with hT
  have hT0 : 0 ≤ T := norm_nonneg _
  have hs0 : 0 ≤ s := by linarith only [hs]
  have hA0 : 0 ≤ A := by linarith only [hA]
  have htt : ‖t‖ ≤ T + 1 := by
    have h1 : ‖t - M.t₀‖ ≤ 1 := ht.trans (rpow_slope_le_one hs hδ1)
    have h2 := norm_le_norm_sub_add t M.t₀
    linarith only [h1, h2]
  have hQ0 : 0 ≤ Q M K A s := Q_nonneg hA0 hs0
  have hW2 := W_sq (M := M) (K := K) hA0 hs0
  have hBW0 : 0 ≤ B * W M K A s := (norm_nonneg w).trans hw
  have hBW' : (2 + T) * (B * W M K A s) ≤ ρ * s / 4 := by
    have : 4 * ((2 + T) * (B * W M K A s)) ≤ ρ * s := by linarith only [hBW]
    linarith only [this]
  have hws : ‖w‖ ≤ s / 8 := by
    have h1 : 2 * (B * W M K A s) ≤ (2 + T) * (B * W M K A s) :=
      mul_le_mul_of_nonneg_right (by linarith only [hT0]) hBW0
    have hρs : ρ * s ≤ s := mul_le_of_le_one_left hs0 hρ1
    linarith only [hw, hBW', h1, hρs]
  have hvfst : v.fst = lam + w.fst := by
    rw [hv, WithLp.add_fst, WithLp.smul_fst]
    change lam * 1 + w.fst = lam + w.fst
    ring
  have hvsnd : v.snd = lam • t + w.snd := by
    rw [hv, WithLp.add_snd, WithLp.smul_snd]
    rfl
  have hwf := Geometry.abs_fst_le_norm w
  have hwsn := Geometry.norm_snd_le_norm w
  have hl := abs_le.mp hlam
  have hwf' := abs_le.mp hwf
  have hf1 : s / 2 ≤ v.fst := by rw [hvfst]; linarith only [hl.1, hwf'.1, hws, hs0]
  have hf2 : v.fst ≤ 2 * s := by rw [hvfst]; linarith only [hl.2, hwf'.2, hws, hs0]
  have hf0 : 0 < v.fst := by linarith only [hf1, hs]
  -- the transverse error `v₂ − v₁ t = w₂ − w₁ t`
  have hy : v.snd - v.fst • t = w.snd - w.fst • t := by
    rw [hvfst, hvsnd, add_smul]; abel
  have hyn : ‖v.snd - v.fst • t‖ ≤ (2 + T) * (B * W M K A s) := by
    rw [hy]
    have h1 := norm_sub_le w.snd (w.fst • t)
    have h2 : ‖w.fst • t‖ ≤ (T + 1) * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, mul_comm (T + 1)]
      exact mul_le_mul hwf htt (norm_nonneg _) (norm_nonneg _)
    have h3 := mul_le_mul_of_nonneg_left hw (by linarith only [hT0] : 0 ≤ 2 + T)
    linarith only [h1, h2, hwsn, h3]
  -- the slope of `v` is within `r₁` of `t`
  have hv' : ‖v.snd - v.fst • t‖ ≤ r₁ * v.fst := by
    have a1 := mul_le_mul_of_nonneg_left hf1 hρ0
    have a2 := mul_le_mul_of_nonneg_right hρ hf0.le
    have h1 : ρ * s / 4 ≤ r₁ * v.fst := by linarith only [a1, a2, mul_nonneg hρ0 hs0]
    linarith only [hyn, hBW', h1]
  have hcost := Moments.cost_le_of_support h24 (htr.trans (by linarith only [hρ, hρ0])) hP hf0 hv'
  have h1 : CS * ‖v.snd - v.fst • t‖ ^ 2 / v.fst ≤ 2 * (2 + T) ^ 2 * CS * B ^ 2 * Q M K A s := by
    rw [div_le_iff₀ hf0]
    have h2 : ‖v.snd - v.fst • t‖ ^ 2 ≤ (2 + T) ^ 2 * B ^ 2 * (s * Q M K A s) := by
      rw [← hW2]
      calc ‖v.snd - v.fst • t‖ ^ 2 ≤ ((2 + T) * (B * W M K A s)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hyn 2
        _ = (2 + T) ^ 2 * B ^ 2 * W M K A s ^ 2 := by ring
    exact cost_numeric_left hCS.le (sq_nonneg _) (sq_nonneg _) hQ0 h2 hf1
  have h2 : CS * v.fst * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ 2 * CS * Q M K A s := by
    have h3 := mul_rpow_slope_le_Q hM hK hA hs (norm_nonneg (t - M.t₀)) ht
    have h4 : 0 ≤ ‖t - M.t₀‖ ^ (2 + M.δ) := Real.rpow_nonneg (norm_nonneg _) _
    have h5 : v.fst * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ 2 * (s * ‖t - M.t₀‖ ^ (2 + M.δ)) :=
      (mul_le_mul_of_nonneg_right hf2 h4).trans_eq (mul_assoc _ _ _)
    calc CS * v.fst * ‖t - M.t₀‖ ^ (2 + M.δ) = CS * (v.fst * ‖t - M.t₀‖ ^ (2 + M.δ)) := by ring
      _ ≤ CS * (2 * Q M K A s) :=
          mul_le_mul_of_nonneg_left (by linarith only [h3, h5]) hCS.le
      _ = 2 * CS * Q M K A s := by ring
  rw [add_mul]
  exact hcost.trans (add_le_add h1 h2)

end CurvatureVariance.Paper.Proofs.ShortLengths
