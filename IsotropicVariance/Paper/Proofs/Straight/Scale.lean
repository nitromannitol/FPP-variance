/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.Containment
public import IsotropicVariance.Paper.Proofs.SlabComparison.UniformScale

/-! # The first two steps of the proof of Lemma `lem:straight`

These are the steps of the paper's proof that precede the straightness argument of Howard and
Newman.

* `exists_containing_ball`: near-geodesics between points of the ball of radius `r` lie in the
  ball of radius `Kr`.
* `exists_metric_scale`: by Lemma `lem:classical`, isotropy and the union bound `eq:union`,
  there is `W ≥ log(2 + r)` with `W ≤ O_2(C log(2 + r))` and
  `|T(x, y) − |y − x|| ≤ A (W |y − x|^{1/2} + W²)` for all `x`, `y` in the larger ball.
-/

@[expose] public section
open Set Metric
namespace IsotropicVariance.Paper.Proofs.Straight
open Paper Contracts SlabComparison
universe u
variable {m : ℕ}

/-- **The near-geodesics between points of the ball lie in a larger ball**
(proof of Lemma `lem:straight`): there is a deterministic `K ≥ 1` such that near-geodesics between
points of the ball of radius `r ≥ 1` around `0` lie in the ball of radius `Kr`. -/
theorem exists_containing_ball (X : Setting m) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ r : ℝ, 1 ≤ r → ∀ ω : X.Ω,
      ∀ a ∈ closedBall (0 : Pt m) r, ∀ b ∈ closedBall (0 : Pt m) r,
        ∀ γ : IsotropicVariance.RectifiableCurve (Pt m), IsOneOptimal (X.ρ ω) univ a b γ →
          ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ closedBall (0 : Pt m) (K * r) := by
  obtain ⟨a₀, b₀, ha₀, hbound⟩ := Infra.TimeConstant.setting_passTime_bounds X
  have hquot : 0 ≤ (2 * |b₀| + 1) / a₀ := by positivity
  refine ⟨1 + (2 * |b₀| + 1) / a₀, by linarith only [hquot], fun r hr ω a ha b hb γ hγ t ht => ?_⟩
  rw [mem_closedBall_zero_iff] at ha hb ⊢
  have hr0 : 0 ≤ r := by linarith only [hr]
  have hab : dist a b ≤ 2 * r := by
    have h := dist_triangle a 0 b
    rw [dist_zero_right, dist_zero_left] at h
    linarith only [h, ha, hb]
  have hcurve := oneOptimal_image_bound X ω (hbound ω) γ hγ ht
  have hb₀ : b₀ * dist a b ≤ |b₀| * (2 * r) :=
    (mul_le_mul_of_nonneg_right (le_abs_self b₀) dist_nonneg).trans
      (mul_le_mul_of_nonneg_left hab (abs_nonneg b₀))
  have hmul : a₀ * dist a (γ.toFun t) ≤ (2 * |b₀| + 1) * r := by
    linarith only [hcurve, hb₀, hr]
  have hd : dist a (γ.toFun t) ≤ (2 * |b₀| + 1) / a₀ * r := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha₀, mul_comm]
    exact hmul
  have htri : ‖γ.toFun t‖ ≤ ‖a‖ + dist a (γ.toFun t) := by
    rw [← dist_zero_right, ← dist_zero_right a]
    have h := dist_triangle (0 : Pt m) a (γ.toFun t)
    rw [dist_comm 0 a, dist_comm 0 (γ.toFun t)] at h
    exact h
  linarith only [htri, ha, hd]

/-- The larger ball lies in the cube around `0` of half-side `R³`, for `R ≥ 1` its radius. -/
lemma mem_cubeAround_of_mem_closedBall {R : ℝ} (hR : 1 ≤ R) {x : Pt m}
    (hx : x ∈ closedBall (0 : Pt m) R) : x ∈ cubeAround (0 : Pt m) (R ^ 3) := by
  intro k
  rw [mem_closedBall_zero_iff] at hx
  have hcoord := abs_coord_le_norm (x - 0) k
  rw [sub_zero] at hcoord
  have hR3 : R ≤ R ^ 3 := le_self_pow₀ hR (by norm_num)
  rw [sub_zero]
  exact hcoord.trans (hx.trans hR3)

/-- **The random scale on the larger ball** (proof of Lemma `lem:straight`), for a fixed `K ≥ 1`:
there are `A` and `C` such that for every `r ≥ 1` there is `W ≥ log(2 + r)`, `W ≥ 1`,
with `W ≤ O_2(C log(2 + r))` and `|T(x, y) − |y − x|| ≤ A (W |y − x|^{1/2} + W²)` on every outcome,
for all `x`, `y` in the ball of radius `Kr`.

The classical bounds, the isotropy and the union bound are in `uniform_metric_scale_of`, for a mesh
of side `1` of a cube containing that ball, in place of the integer points of the paper. -/
theorem exists_metric_scale (hclassical : ClassicalBoundsStatement.{u}) (hm : 1 ≤ m)
    (X : Setting.{u} m) (hnorm : X.IsNormalized) {K : ℝ} (hK : 1 ≤ K) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      ∃ W : X.Ω → ℝ, (∀ ω, 1 ≤ W ω) ∧ (∀ ω, Real.log (2 + r) ≤ W ω) ∧
        Cited.IsOs X.P 2 (C * Real.log (2 + r)) W ∧
        ∀ ω, ∀ x ∈ closedBall (0 : Pt m) (K * r), ∀ y ∈ closedBall (0 : Pt m) (K * r),
          |X.passTime ω x y - dist x y| ≤ A * (W ω * Real.sqrt (dist x y) + W ω ^ 2) := by
  obtain ⟨A, C, hA, hC, hscale⟩ := uniform_metric_scale_of hclassical hm X hnorm
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlK : 0 ≤ Real.log K / Real.log 2 := div_nonneg (Real.log_nonneg hK) hl2.le
  refine ⟨A, C * (Real.log K / Real.log 2 + 1), hA, by positivity, fun r hr => ?_⟩
  have hR : 1 ≤ K * r := one_le_mul_of_one_le_of_one_le hK hr
  have hrR : r ≤ K * r := le_mul_of_one_le_left (by linarith only [hr]) hK
  obtain ⟨S, hfloor, hOs, hmetric⟩ := hscale (K * r) hR 0
  have hlogR : Real.log (2 + r) ≤ Real.log (2 + K * r) :=
    Real.log_le_log (by linarith only [hr]) (by linarith only [hrR])
  have hlog : 0 < Real.log (2 + K * r) := Real.log_pos (by linarith only [hR])
  have hpoly : Real.log (2 + K * r) ≤ (Real.log K / Real.log 2 + 1) * Real.log (2 + r) := by
    have hh := log_le_of_polynomial_bound (q := 1) hK hr (N := 2 + K * r) (by linarith only [hR])
      (by rw [pow_one]; linarith only [hK])
    rwa [Nat.cast_one] at hh
  refine ⟨S, fun ω => by linarith only [hfloor ω, hlog], fun ω => by
    linarith only [hfloor ω, hlogR], ?_, fun ω x hx y hy => ?_⟩
  · refine hOs.mono_scale (by norm_num) (by positivity) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hpoly hC.le
  · exact hmetric ω x (mem_cubeAround_of_mem_closedBall hR hx) y
      (mem_cubeAround_of_mem_closedBall hR hy)

end IsotropicVariance.Paper.Proofs.Straight
