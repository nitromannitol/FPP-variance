/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.TurningChain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

/-!
# The constants of the dyadic chain exist

`exists_chainConstants`: for a norm `μ` comparable to the Euclidean norm, the constants of the
dyadic chain of the proof of Lemma `lem:cone` (`ChainConstants`) exist, depending only on
`μlo, μhi, δ, c, C, r₁, b, T`. They are the constants of `cone_exit_bounds`
(`Proofs.Geometry.Cone`), equation `eq:cone` for a path in a set on which the passage time
concentrates.
-/

@[expose] public section

open InnerProductGeometry
open scoped NNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper

/-- The constants of the dyadic chain exist, depending only on `μlo, μhi, δ, c, C, r₁, b, T`. -/
theorem exists_chainConstants {μlo μhi δ c C r₁ b T : ℝ} (hμlo : 0 < μlo) (hμ : μlo ≤ μhi)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc : 0 < c) (hC : 0 ≤ C) (hr₁ : 0 < r₁) (hb : 0 < b)
    (hT : 0 ≤ T) :
    ∃ Kc P Q η ε₁ M ε₀ : ℝ, 0 < ε₀ ∧ ChainConstants μlo μhi δ c C r₁ b T Kc P Q η ε₁ M ε₀ := by
  have hμhi : 0 < μhi := hμlo.trans_le hμ
  set κ := slopeFactor T with hκdef
  have hκ : 0 < κ := slopeFactor_pos hT
  have hκap : 0 < κ * aperture T / 2 := by
    have := aperture_pos hT
    positivity
  set Kc := max (max (4 / μlo) (2 * μhi)) 1 with hKc
  have hKc1 : 1 ≤ Kc := le_max_right _ _
  have hKc0 : 0 < Kc := by linarith
  set A₂ := Real.sqrt (C / c) with hA₂
  have hA₂0 : 0 ≤ A₂ := Real.sqrt_nonneg _
  set P := 14 * stepConst Kc b c with hP
  have hP0 : 0 < P := by
    have : 0 < stepConst Kc b c := Real.sqrt_pos.2 (by positivity)
    positivity
  set Q := 16 * A₂ with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set η := 1 / (48 * κ * A₂ + 1) with hη
  have hη0 : 0 < η := by positivity
  set ε₁ := min (η ^ (2 / δ)) (min (r₁ / 2) (κ * aperture T / 2)) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (Real.rpow_pos_of_pos hη0 _) (lt_min (by positivity) hκap)
  set M := max (max 1 (2 * μhi)) ((κ * P / ε₁) ^ 4) with hM
  set ε₀ := min (min (κ * aperture T / 2) (r₁ / 4)) (1 / (2 * κ * Q + 1)) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (lt_min hκap (by positivity)) (by positivity)
  refine ⟨Kc, P, Q, η, ε₁, M, ε₀, hε₀0, ?_⟩
  exact
    { μlo_pos := hμlo
      μlo_le_μhi := hμ
      δ_pos := hδ
      δ_le_one := hδ1
      c_pos := hc
      C_nonneg := hC
      b_nonneg := hb.le
      T_nonneg := hT
      four_div_le_Kc := (le_max_left _ _).trans (le_max_left _ _)
      two_mul_le_Kc := (le_max_right _ _).trans (le_max_left _ _)
      one_le_Kc := hKc1
      P_ge := le_rfl
      Q_ge := le_rfl
      η_le := by
        rw [← hκdef, ← hA₂, hη, mul_one_div, div_le_iff₀ (by positivity)]
        linarith
      rpow_ε₁_le := by
        calc ε₁ ^ (δ / 2) ≤ (η ^ (2 / δ)) ^ (δ / 2) :=
              Real.rpow_le_rpow hε₁0.le (min_le_left _ _) (by positivity)
          _ = η := by
            rw [← Real.rpow_mul hη0.le, show 2 / δ * (δ / 2) = 1 by field_simp, Real.rpow_one]
      ε₁_le_r₁ := (min_le_right _ _).trans (min_le_left _ _)
      ε₁_le := (min_le_right _ _).trans (min_le_right _ _)
      one_le_M := (le_max_left _ _).trans (le_max_left _ _)
      two_mul_le_M := (le_max_right _ _).trans (le_max_left _ _)
      fluct_le := by
        intro S R hS hR hMR
        rw [← hκdef]
        set x := ε₁ / (κ * P) with hx
        have hx0 : 0 < x := by positivity
        have hxM : x ^ 4 * (κ * P / ε₁) ^ 4 = 1 := by
          rw [← mul_pow, hx, show ε₁ / (κ * P) * (κ * P / ε₁) = 1 by field_simp, one_pow]
        have hM' : (κ * P / ε₁) ^ 4 ≤ M := le_max_right _ _
        have hle : turnErr S R ≤ x := by
          refine turnErr_le_of_sq_le hS hR hx0.le ?_
          have h1 : S ^ 2 = x ^ 4 * (κ * P / ε₁) ^ 4 * S ^ 2 := by rw [hxM, one_mul]
          have h2 : x ^ 4 * (κ * P / ε₁) ^ 4 * S ^ 2 ≤ x ^ 4 * (M * S ^ 2) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hM' (sq_nonneg S)) (by positivity)
          have h3 : x ^ 4 * (M * S ^ 2) ≤ x ^ 4 * R :=
            mul_le_mul_of_nonneg_left hMR (by positivity)
          linarith
        calc κ * (P * turnErr S R) ≤ κ * (P * x) := by gcongr
          _ = ε₁ := by rw [hx]; field_simp
      ε₀_le := (min_le_left _ _).trans (min_le_left _ _)
      ε₀_le_r₁ := (min_le_left _ _).trans (min_le_right _ _)
      ε₀_le_Q := by
        rw [← hκdef]
        have h : ε₀ ≤ 1 / (2 * κ * Q + 1) := min_le_right _ _
        rw [le_div_iff₀ (by positivity)] at h
        have : 0 ≤ ε₀ := hε₀0.le
        linarith }

end CurvatureVariance.Paper.Proofs.Geometry
