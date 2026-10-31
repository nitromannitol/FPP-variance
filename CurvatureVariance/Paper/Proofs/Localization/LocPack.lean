/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.LocCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.Basic
import CurvatureVariance.Paper.Proofs.ShortLengths.ShortDet
import CurvatureVariance.Paper.Proofs.Localization.Common

/-!
# Lemma `lem:localization`: the numerical conditions, together

`Loc.Pack` collects the conditions "for `N` large" of the proof of Lemma `lem:localization`, and
`pack_of_base` proves them from the single fact `C Λ² ≤ ℓ^{δ/200}`, with `Λ = log(2 + N)`,
`exists_base`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts
  CurvatureVariance.Paper.Proofs.Geometry Radius

variable {m : ℕ}

/-- The conditions "for `N` large" at fixed `N`, `A`, `ℓ`. -/
structure Pack (M : Model m) (K : ℕ) (A : ℝ) (ℓ : ℕ) (t : EuclideanSpace ℝ (Fin m)) (p : ℤ)
    (c : EuclideanSpace ℝ (Fin m)) (a a' : Vertex m) (T c₀ C₀ : ℝ) (κT : ℕ)
    (D L₀ τ lg S K₁ Cc Γ Bq r₁ ρ Csl : ℝ) : Prop where
  cfg : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT
  hτ : ‖t - M.t₀‖ + 2 * Γ / ℓ ≤ τ
  hTT : ‖M.t₀‖ + τ ≤ T
  htlog : Cc * (τ ^ (1 + M.δ / 2) * lg) ≤ aperture T / 2
  hL : L₀ ≤ ℓ
  hDD : 5 * Γ + coneRadius M.δ Cc K₁ T S lg ℓ τ ≤ D
  hLW : L₀ ≤ W M K A ℓ
  hDr : 64 * D ≤ r₁ * ℓ
  ht₁ : ‖t - M.t₀‖ ≤ r₁
  hρ₁ : ‖t - M.t₀‖ ≤ ρ / 2
  hρ₂ : 4 * (2 + T) * Bq * W M K A ℓ ≤ ρ * ℓ
  hCsl : Csl * lg ^ 2 ≤ ℓ
  hDℓ : D ≤ ℓ
  hΓW : Γ ≤ Bq * W M K A ℓ

/-- **The numerical conditions** from `C Λ² ≤ y = ℓ^{δ/200}`, for `C` at least each of the constants
of the proof. -/
theorem pack_of_base {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {t : EuclideanSpace ℝ (Fin m)} {p : ℤ}
    {c : EuclideanSpace ℝ (Fin m)} {a a' : Vertex m} {T c₀ C₀ : ℝ} {κT : ℕ}
    (ht : ‖t - M.t₀‖ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4)) (ht₀ : ‖M.t₀‖ + 1 ≤ T) (hT : 1 ≤ T)
    (hκT : 1 ≤ κT) (hκT' : 4 * (1 + T) + 1 / 2 ≤ κT)
    (ha₁ : |(a.1 : ℝ) - ((p : ℝ) - (ℓ : ℝ) / 16)| ≤ rtd m)
    (ha₂ : |(a'.1 : ℝ) - ((p : ℝ) + 17 * (ℓ : ℝ) / 16)| ≤ rtd m)
    (hao : ‖ofs t p c a‖ ≤ C₀) (ha'o : ‖ofs t p c a'‖ ≤ C₀) (hc₀ : 0 < c₀)
    (hc₀1 : 2 ^ 16 * c₀ ≤ 1) (hc₀2 : 512 * Real.sqrt m * κT * c₀ ≤ 1)
    {C Λ lg Cs K₁ Cc Cw Bq Γ r₁ ρ Csl : ℝ} (hC1 : 1 ≤ C) (hΛ : 1 ≤ Λ) (hlgΛ : lg ≤ Λ)
    (hlg : 1 ≤ lg) (hCs : 1 ≤ Cs) (hK₁ : 0 ≤ K₁) (hCc : 0 < Cc) (hBq : 0 ≤ Bq) (hr₁ : 0 < r₁)
    (hρ0 : 0 < ρ) (hCw : 0 ≤ Cw)
    (hbase : C * Λ ^ 2 ≤ (ℓ : ℝ) ^ (M.δ / 200))
    (hW : W M K A ℓ ≤ Cw * (ℓ : ℝ) ^ ((3 : ℝ) / 4) * Λ)
    (hΓ₀ : 2 * rtd m ≤ W M K A ℓ → Γ ≤ Bq * W M K A ℓ)
    (c1 : 4 * ((1 + T) * rtd m + 1) ≤ C) (c2 : 2 * C₀ ≤ C) (c3 : 256 * Real.sqrt m * κT ≤ C)
    (c4 : 2 * (rtd m + K₁ * Cs ^ 2 + 1) / c₀ ≤ C) (c5 : 64 * (K₁ * Cs ^ 2 + rtd m) ≤ C)
    (c6 : Cw ≤ C)
    (c7 : 5 * (Bq * Cw) + (1 + T) * (K₁ * Cs ^ 2) +
      slopeFactor T * Cc * (Cs * (2 * (1 + T)) + 4) ≤ C)
    (c8 : 64 / r₁ ≤ C) (c9 : 4 * (2 + T) * Bq / ρ ≤ C) (c10 : 2 / ρ ≤ C) (c11 : 2 * Bq ≤ C)
    (c12 : 2 ≤ C) (c13 : 4 * Cc / aperture T ≤ C) (c14 : Csl ≤ C) (hCsl0 : 0 ≤ Csl) :
    Pack M K A ℓ t p c a a' T c₀ C₀ κT ((ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 200))
      (K₁ * (Cs * lg) ^ 2) (2 * (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4)) lg (Cs * lg) K₁ Cc Γ Bq r₁ ρ
      Csl := by
  have hx : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hx0 : (0 : ℝ) < ℓ := by linarith only [hx]
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  have hT0 : 0 ≤ T := by linarith only [hT]
  set y := (ℓ : ℝ) ^ (M.δ / 200) with hy
  set D := (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 200) with hD
  set e := (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) with he
  set X := (ℓ : ℝ) ^ ((3 : ℝ) / 4) with hX
  have hDy : D * y = ℓ * e := D_mul_y hx0
  have hey : e * y ≤ 1 := e_mul_y_le_one hx hδ1
  have hyy : y ^ 2 ≤ ℓ := y_sq_le hx hδ1
  have hy1 : 1 ≤ y := Real.one_le_rpow hx (by positivity)
  have hy0 : 0 < y := by linarith only [hy1]
  have hD0 : 0 ≤ D := by positivity
  have he0 : 0 ≤ e := by positivity
  have hX0 : 0 ≤ X := by positivity
  have hDX : D = X * y := Real.rpow_add hx0 _ _
  have hΛ2 : 1 ≤ Λ ^ 2 := one_le_pow₀ hΛ
  have hkey : ∀ C' : ℝ, C' ≤ C → C' * Λ ^ 2 ≤ y := fun C' h =>
    (mul_le_mul_of_nonneg_right h (by positivity)).trans hbase
  have hle : ∀ C' : ℝ, C' ≤ C → C' ≤ y := fun C' h => by
    have h1 := hkey C le_rfl
    have h2 : C ≤ C * Λ ^ 2 := le_mul_of_one_le_right (by linarith only [hC1]) hΛ2
    linarith only [h, h1, h2]
  -- `D y² ≤ ℓ`
  have hDyy : D * y ^ 2 ≤ ℓ := by
    have h1 := mul_le_mul_of_nonneg_left hey hx0.le
    have e1 : D * y ^ 2 = (D * y) * y := by ring
    rw [e1, hDy]
    linarith only [h1]
  have hDℓ : D ≤ ℓ := by
    have h1 : D ≤ D * y ^ 2 := le_mul_of_one_le_right hD0 (one_le_pow₀ hy1)
    linarith only [h1, hDyy]
  have heb : ∀ r : ℝ, 0 < r → 1 / r ≤ y → e ≤ r := fun r hr h => by
    rw [div_le_iff₀ hr] at h
    have h1 := mul_le_mul_of_nonneg_left h he0
    have h2 := mul_le_mul_of_nonneg_right hey hr.le
    linarith only [h1, h2, mul_assoc e y r]
  -- the width
  have hWQ : W M K A ℓ ^ 2 = ℓ * Q M K A ℓ :=
    Proofs.ShortLengths.W_sq (by linarith only [hA]) hx0.le
  have hQ1 : 1 ≤ Q M K A ℓ := Proofs.ShortLengths.one_le_Q hM hK hA hx
  have hWy : y ≤ W M K A ℓ := by
    have h1 : y ^ 2 ≤ ℓ * Q M K A ℓ := hyy.trans (le_mul_of_one_le_right hx0.le hQ1)
    exact Real.le_sqrt_of_sq_le h1
  have hWD : W M K A ℓ ≤ D := by
    have h1 : Cw * Λ ≤ y := by
      have h2 : Cw * Λ ≤ Cw * Λ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hCw
        nlinarith only [hΛ]
      exact h2.trans (hkey Cw c6)
    calc W M K A ℓ ≤ Cw * X * Λ := hW
      _ = X * (Cw * Λ) := by ring
      _ ≤ X * y := mul_le_mul_of_nonneg_left h1 hX0
      _ = D := hDX.symm
  have hW1 : 1 ≤ W M K A ℓ := hy1.trans hWy
  -- the confinement along `e₁`
  have hd0 := rtd_nonneg m
  have hΓ : Γ ≤ Bq * W M K A ℓ := hΓ₀ (by
    have h1 := hle _ c1
    have h2 : 0 ≤ T * rtd m := by positivity
    nlinarith only [h1, h2, hWy, hd0])
  have hlg0 : 0 ≤ lg := by linarith only [hlg]
  have hL₀ : 0 ≤ K₁ * (Cs * lg) ^ 2 := by positivity
  have hS2 : (Cs * lg) ^ 2 ≤ Cs ^ 2 * Λ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hlgΛ (by positivity)) 2
  have hL₀2 : K₁ * (Cs * lg) ^ 2 ≤ K₁ * Cs ^ 2 * Λ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hS2 hK₁
    linarith only [this]
  have h4 : 2 * (rtd m + K₁ * (Cs * lg) ^ 2 + 1) ≤ c₀ * y := by
    have h1 := hkey _ c4
    have h2 : 2 * (rtd m + K₁ * Cs ^ 2 + 1) * Λ ^ 2 ≤ c₀ * y := by
      have h3 := mul_le_mul_of_nonneg_left h1 hc₀.le
      have e1 : c₀ * (2 * (rtd m + K₁ * Cs ^ 2 + 1) / c₀ * Λ ^ 2) =
          2 * (rtd m + K₁ * Cs ^ 2 + 1) * Λ ^ 2 := by field_simp
      linarith only [h3, e1]
    have h3 : 0 ≤ rtd m + 1 := by positivity
    have h5 : (rtd m + 1) * 1 ≤ (rtd m + 1) * Λ ^ 2 := mul_le_mul_of_nonneg_left hΛ2 h3
    nlinarith only [h2, h5, hL₀2]
  have h5 : 64 * (K₁ * (Cs * lg) ^ 2 + rtd m) ≤ y := by
    have h1 := hkey _ c5
    have h2 : rtd m * 1 ≤ rtd m * Λ ^ 2 := mul_le_mul_of_nonneg_left hΛ2 hd0
    nlinarith only [h1, h2, hL₀2]
  have hcfg : Cfg M K A ℓ t p c a a' T c₀ C₀ D (K₁ * (Cs * lg) ^ 2) κT :=
    cfg_of hM hK hA hℓ ht (by
        have := norm_le_norm_sub_add t M.t₀
        have h1 : e ≤ 1 / 2 := heb _ (by norm_num) (by
          have := hle _ c12; norm_num; linarith only [this])
        have ht' : ‖t - M.t₀‖ ≤ 1 / 2 := ht.trans h1
        linarith only [this, ht', ht₀]) hT hκT hκT' ha₁ ha₂ hao ha'o hc₀ hc₀1 hc₀2 hWy hWD
      (hle _ c1) (hle _ c2) (hle _ c3) h4 hL₀ h5
  have hy2 : 2 ≤ y := hle _ c12
  have he2 : 2 * e ≤ 1 := by nlinarith only [hey, he0, hy2]
  have hτ : ‖t - M.t₀‖ + 2 * Γ / ℓ ≤ 2 * e := by
    have h1 : 2 * Γ ≤ ℓ * e := by
      rw [← hDy]
      have h2 := hle _ c11
      have h3 : Bq * W M K A ℓ ≤ Bq * D := mul_le_mul_of_nonneg_left hWD hBq
      have h4 := mul_le_mul_of_nonneg_left h2 hD0
      nlinarith only [hΓ, h3, h4]
    have h2 : 2 * Γ / ℓ ≤ e := by
      rw [div_le_iff₀ hx0]; linarith only [h1]
    linarith only [ht, h2]
  have hap := aperture_pos hT0
  have htlog : Cc * ((2 * e) ^ (1 + M.δ / 2) * lg) ≤ aperture T / 2 := by
    have h1 : (2 * e) ^ (1 + M.δ / 2) ≤ 2 * e :=
      rpow_one_add_le (by positivity) he2 (by positivity)
    have h2 := mul_le_mul_of_nonneg_right h1 hlg0
    have h3 := mul_le_mul_of_nonneg_left h2 hCc.le
    have h4 := hkey _ c13
    have h5 : lg ≤ Λ ^ 2 := by nlinarith only [hlgΛ, hΛ]
    have h6 : 4 * Cc * lg ≤ aperture T * y := by
      have h7 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 4 * Cc / aperture T)
      have h8 := h7.trans h4
      rw [div_mul_eq_mul_div, div_le_iff₀ hap] at h8
      linarith only [h8, mul_comm y (aperture T)]
    have h9 : 4 * Cc * lg * e ≤ aperture T := by
      have h10 := mul_le_mul_of_nonneg_right h6 he0
      have h11 := mul_le_mul_of_nonneg_left hey hap.le
      nlinarith only [h10, h11]
    nlinarith only [h3, h9]
  have hDD : 5 * Γ + coneRadius M.δ Cc K₁ T (Cs * lg) lg ℓ (2 * e) ≤ D := by
    have hS1 : 1 ≤ Cs * lg := by nlinarith only [hCs, hlg]
    have h1 := coneRadius_le (δ := M.δ) (C := Cc) (K₁ := K₁) (T := T) (S := Cs * lg) (lg := lg)
      (x := ℓ) (Γ := Γ) (Cs := Cs) (CΓ := Bq * Cw) (Λ := Λ) hδ hδ1 hCc hK₁ hT0 hS1 hx hlg0 hlgΛ
      (mul_le_mul_of_nonneg_left hlgΛ (by positivity)) hΛ (by
        have h2 := mul_le_mul_of_nonneg_left hW hBq
        linarith only [hΓ, h2, mul_assoc Bq Cw (X * Λ), mul_assoc Bq (Cw * X) Λ, mul_assoc Bq Cw X])
      (by positivity) (by positivity) (hkey _ c7)
    exact h1
  have hyyb : ∀ r : ℝ, 0 ≤ r → r ≤ y → r * D ≤ ℓ := fun r hr h => by
    have h1 : r * D ≤ y ^ 2 * D := by
      refine mul_le_mul_of_nonneg_right ?_ hD0
      nlinarith only [h, hy1]
    linarith only [h1, hDyy, mul_comm D (y ^ 2)]
  refine ⟨hcfg, hτ, ?_, htlog, ?_, hDD, ?_, ?_, ?_, ?_, ?_, ?_, hDℓ, hΓ⟩
  · linarith only [ht₀, he2]
  · have h1 := y_sq_le hx hδ1
    nlinarith only [h5, h1, hy1, hd0]
  · linarith only [h5, hWy, hd0, hL₀, hW1]
  · have h1 := hyyb _ (by positivity) (hle _ c8)
    have h2 := mul_le_mul_of_nonneg_left h1 hr₁.le
    have e1 : r₁ * (64 / r₁ * D) = 64 * D := by field_simp
    linarith only [h2, e1]
  · refine ht.trans (heb _ hr₁ ?_)
    have h1 := hle _ c8
    have h2 : 1 / r₁ ≤ 64 / r₁ := div_le_div_of_nonneg_right (by norm_num) hr₁.le
    linarith only [h1, h2]
  · refine ht.trans (heb _ (by positivity) ?_)
    have h1 := hle _ c10
    have e1 : 1 / (ρ / 2) = 2 / ρ := by field_simp
    rw [e1]; exact h1
  · have h1 := hyyb _ (by positivity) (hle _ c9)
    have h2 := mul_le_mul_of_nonneg_left h1 hρ0.le
    have e1 : ρ * (4 * (2 + T) * Bq / ρ * D) = 4 * (2 + T) * Bq * D := by field_simp
    have h3 : 4 * (2 + T) * Bq * W M K A ℓ ≤ 4 * (2 + T) * Bq * D :=
      mul_le_mul_of_nonneg_left hWD (by positivity)
    linarith only [h2, e1, h3]
  · have h1 := hkey _ c14
    have h2 : Csl * lg ^ 2 ≤ Csl * Λ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlg0 hlgΛ 2) hCsl0
    have h3 := y_sq_le hx hδ1
    nlinarith only [h1, h2, h3, hy1]

end CurvatureVariance.Paper.Localization.Loc
