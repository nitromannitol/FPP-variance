/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.LocCfg
public import CurvatureVariance.Paper.Proofs.Localization.LocConfine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.WidthMargin
import CurvatureVariance.Paper.Proofs.Localization.Common

/-!
# Lemma `lem:localization`: "for `N` large"

With `x = ℓ`, `y = x^{δ/200}` and `D = x^{3/4+δ/200}`, every condition "for `N` large" of the proof
of Lemma `lem:localization` follows from `C log²(2 + N) ≤ y`, for `C` large, which is `exists_base`:

* `D_mul_y`, `e_mul_y_le_one`, `y_sq_le`, `mul_e_rpow_le`: the exponents, the last one being the
  paper's `1 − (1/4 − δ/100)(1 + δ/2) < 3/4`;
* `W_le_of_range`: `W_ℓ ≤ C x^{3/4} log(2 + N)`, from equation `eq:regime` directly, and
  not from equation `eq:scales`, whose bound at `s ≈ N` is `x^{3/4+3δ/500}`: the paper's
  `(ℓQ_ℓ)^{1/2} ≤ ℓ^{3/4+δ/200}`, "since `K ≥ 10⁴`", is this bound;
* `cfg_of`: the record `Cfg`;
* `coneRadius_le`: the bound of the first change;
* `exists_holder`: the third change.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Paper CurvatureVariance.Paper.Proofs.Geometry

variable {m : ℕ}

section Powers

variable {x δ : ℝ}

theorem D_mul_y (hx : 0 < x) :
    x ^ ((3 : ℝ) / 4 + δ / 200) * x ^ (δ / 200) = x * x ^ (δ / 100 - 1 / 4) := by
  have h : x * x ^ (δ / 100 - 1 / 4) = x ^ (1 + (δ / 100 - 1 / 4)) := by
    rw [Real.rpow_add hx, Real.rpow_one]
  rw [h, ← Real.rpow_add hx]
  congr 1
  ring

theorem e_mul_y_le_one (hx : 1 ≤ x) (hδ1 : δ ≤ 1) :
    x ^ (δ / 100 - 1 / 4) * x ^ (δ / 200) ≤ 1 := by
  rw [← Real.rpow_add (by linarith only [hx])]
  exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith only [hδ1])

theorem y_sq_le (hx : 1 ≤ x) (hδ1 : δ ≤ 1) : (x ^ (δ / 200)) ^ 2 ≤ x := by
  rw [sq, ← Real.rpow_add (by linarith only [hx])]
  calc x ^ (δ / 200 + δ / 200) ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hδ1])
    _ = x := Real.rpow_one x

theorem mul_e_rpow_le (hx : 1 ≤ x) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    x * (x ^ (δ / 100 - 1 / 4)) ^ (1 + δ / 2) ≤ x ^ ((3 : ℝ) / 4) := by
  have hx0 : 0 < x := by linarith only [hx]
  rw [← Real.rpow_mul hx0.le]
  have h : x * x ^ ((δ / 100 - 1 / 4) * (1 + δ / 2)) =
      x ^ (1 + (δ / 100 - 1 / 4) * (1 + δ / 2)) := by
    rw [Real.rpow_add hx0, Real.rpow_one]
  rw [h]
  exact Real.rpow_le_rpow_of_exponent_le hx (by nlinarith only [hδ, hδ1])

/-- `u^{1+r} ≤ u` for `0 ≤ u ≤ 1` and `r ≥ 0`. -/
theorem rpow_one_add_le {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 ≤ r) :
    u ^ (1 + r) ≤ u := by
  calc u ^ (1 + r) ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge' hu0 hu1 zero_le_one
        (by linarith only [hr])
    _ = u := Real.rpow_one u

end Powers

/-- `W_ℓ ≤ C x^{3/4} log(2 + N)`, from equation `eq:regime` directly. -/
theorem W_le_of_range {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {N ℓ : ℕ} {Cstar κ : ℝ} (hκ : 0 < κ) (hrange : RangeA M K A N Cstar)
    (hκℓ : κ * N ≤ ℓ) (hℓN : ℓ ≤ N) (hΛ : 1 ≤ Real.log (2 + N)) :
    W M K A ℓ ≤ (1 + max Cstar 1 / Real.sqrt κ) * (ℓ : ℝ) ^ ((3 : ℝ) / 4) * Real.log (2 + N) := by
  set Λ := Real.log (2 + N) with hΛdef
  set x : ℝ := (ℓ : ℝ) with hx
  have hA0 : (0 : ℝ) ≤ A := by linarith only [hA]
  have hx0 : 0 ≤ x := Nat.cast_nonneg ℓ
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  set C := max Cstar 1 with hC
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCs : Cstar ≤ C := le_max_left _ _
  have hNr : x ≤ N := by simp only [hx]; exact_mod_cast hℓN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hQ : Q M K A x ≤ C * Real.sqrt (N * Λ) := by
    have h1 : Q M K A x ≤ Q M K A N := Localization.Q_le_Q hM hK hA0 hx0 hNr
    exact h1.trans (hrange.trans (mul_le_mul_of_nonneg_right hCs (Real.sqrt_nonneg _)))
  have hsN : Real.sqrt (N * Λ) ≤ Real.sqrt x / Real.sqrt κ * Λ := by
    rw [Real.sqrt_mul hN0]
    have h1 : Real.sqrt N ≤ Real.sqrt x / Real.sqrt κ := by
      rw [le_div_iff₀ hsκ, ← Real.sqrt_mul hN0]
      apply Real.sqrt_le_sqrt
      linarith only [hκℓ, hx, mul_comm κ (N : ℝ)]
    have h2 : Real.sqrt Λ ≤ Λ := by
      rw [Real.sqrt_le_left (by linarith only [hΛ])]
      nlinarith only [hΛ]
    exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
  set X := x ^ ((3 : ℝ) / 4) with hX
  have hX0 : 0 ≤ X := by positivity
  have hX2 : X ^ 2 = x * Real.sqrt x := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hx0, Real.sqrt_eq_rpow]
    rcases hx0.eq_or_lt with h0 | h0
    · rw [← h0]; norm_num
    · rw [← Real.rpow_one_add' hx0 (by norm_num)]
      norm_num
  have h1 : x * Q M K A x ≤ (C / Real.sqrt κ) * X ^ 2 * Λ := by
    have h2 := mul_le_mul_of_nonneg_left hQ hx0
    have h3 := mul_le_mul_of_nonneg_left hsN (by positivity : 0 ≤ x * C)
    rw [hX2]
    calc x * Q M K A x ≤ x * (C * Real.sqrt (N * Λ)) := h2
      _ = x * C * Real.sqrt (N * Λ) := by ring
      _ ≤ x * C * (Real.sqrt x / Real.sqrt κ * Λ) := h3
      _ = C / Real.sqrt κ * (x * Real.sqrt x) * Λ := by ring
  set B := 1 + C / Real.sqrt κ with hB
  have hB1 : 1 ≤ B := by have : 0 ≤ C / Real.sqrt κ := by positivity
                         linarith only [this, hB]
  rw [W]
  refine Real.sqrt_le_iff.2 ⟨by positivity, h1.trans ?_⟩
  have h4 : (B * X * Λ) ^ 2 = B ^ 2 * Λ ^ 2 * X ^ 2 := by ring
  rw [h4]
  have h5 : (C / Real.sqrt κ) * Λ ≤ B ^ 2 * Λ ^ 2 := by
    have h6 : C / Real.sqrt κ ≤ B ^ 2 := by nlinarith only [hB1, hB]
    have h7 : Λ ≤ Λ ^ 2 := by nlinarith only [hΛ]
    exact mul_le_mul h6 h7 (by linarith only [hΛ]) (by positivity)
  have := mul_le_mul_of_nonneg_right h5 (sq_nonneg X)
  linarith only [this]

/-- **The record `Cfg`** from the base fact: the conditions on `W`, `D` and `L₀`, all from
`D y = x · x^{δ/100−1/4}`, with `y = x^{δ/200} ≤ W`. -/
theorem cfg_of {M : Model m} {K : ℕ} {A : ℝ} {ℓ : ℕ} {t : EuclideanSpace ℝ (Fin m)} {p : ℤ}
    {c : EuclideanSpace ℝ (Fin m)} {a a' : Vertex m} {T c₀ C₀ L₀ : ℝ} {κT : ℕ}
    (hM : M.Standing) (hK : 10 ^ 4 ≤ K) (hA : 1 ≤ A) (hℓ : 1 ≤ ℓ)
    (ht : ‖t - M.t₀‖ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4)) (htT : ‖t‖ ≤ T) (hT : 1 ≤ T)
    (hκT : 1 ≤ κT) (hκT' : 4 * (1 + T) + 1 / 2 ≤ κT)
    (ha₁ : |(a.1 : ℝ) - ((p : ℝ) - (ℓ : ℝ) / 16)| ≤ rtd m)
    (ha₂ : |(a'.1 : ℝ) - ((p : ℝ) + 17 * (ℓ : ℝ) / 16)| ≤ rtd m)
    (hao : ‖ofs t p c a‖ ≤ C₀) (ha'o : ‖ofs t p c a'‖ ≤ C₀) (hc₀ : 0 < c₀)
    (hc₀1 : 2 ^ 16 * c₀ ≤ 1) (hc₀2 : 512 * Real.sqrt m * κT * c₀ ≤ 1)
    (hWy : (ℓ : ℝ) ^ (M.δ / 200) ≤ W M K A ℓ)
    (hWD : W M K A ℓ ≤ (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 200))
    (h1 : 4 * ((1 + T) * rtd m + 1) ≤ (ℓ : ℝ) ^ (M.δ / 200))
    (h2 : 2 * C₀ ≤ (ℓ : ℝ) ^ (M.δ / 200))
    (h3 : 256 * Real.sqrt m * κT ≤ (ℓ : ℝ) ^ (M.δ / 200))
    (h4 : 2 * (rtd m + L₀ + 1) ≤ c₀ * (ℓ : ℝ) ^ (M.δ / 200)) (hL₀ : 0 ≤ L₀)
    (h5 : 64 * (L₀ + rtd m) ≤ (ℓ : ℝ) ^ (M.δ / 200)) :
    Cfg M K A ℓ t p c a a' T c₀ C₀ ((ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 200)) L₀ κT := by
  have hx : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hx0 : (0 : ℝ) < ℓ := by linarith only [hx]
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  set y := (ℓ : ℝ) ^ (M.δ / 200) with hy
  set D := (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 200) with hD
  set e := (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) with he
  have hDy : D * y = ℓ * e := D_mul_y hx0
  have hy1 : 1 ≤ y := Real.one_le_rpow hx (by positivity)
  have hy0 : 0 < y := by linarith only [hy1]
  have hD0 : 0 ≤ D := by positivity
  have he1 : e ≤ 1 := by
    have h6 := e_mul_y_le_one hx hδ1
    rw [← hy, ← he] at h6
    have he0 : 0 ≤ e := by positivity
    nlinarith only [h6, hy1, he0]
  have hd0 := rtd_nonneg m
  have hT0 : 0 ≤ (1 + T) * rtd m := by
    have : 0 ≤ 1 + T := by linarith only [hT]
    positivity
  have hW1 : 1 ≤ W M K A ℓ := hy1.trans hWy
  refine ⟨hM, hK, hA, hℓ, ht, htT, hT, hκT, hκT', ha₁, ha₂, hao, ha'o, hc₀, hc₀1, hc₀2,
    h1.trans hWy, h2.trans hWy, hWD, ?_, ?_, hL₀, ?_⟩
  · rw [div_le_iff₀ hx0]
    have h6 := mul_le_mul_of_nonneg_left h3 hD0
    have e1 : D * (256 * Real.sqrt m * κT) = 4 * (64 * Real.sqrt m * κT * D) := by ring
    linarith only [h6, hDy, e1]
  · have h6 := mul_le_mul_of_nonneg_left h4 hD0
    have h7 : c₀ * (ℓ * e) ≤ c₀ * ℓ * W M K A ℓ := by
      have h8 : (ℓ : ℝ) * e ≤ ℓ * W M K A ℓ :=
        mul_le_mul_of_nonneg_left (he1.trans hW1) hx0.le
      have := mul_le_mul_of_nonneg_left h8 hc₀.le
      linarith only [this]
    have e1 : D * (c₀ * y) = c₀ * (D * y) := by ring
    rw [hDy] at e1
    have e2 : 2 * D * (rtd m + L₀ + 1) = D * (2 * (rtd m + L₀ + 1)) := by ring
    linarith only [h6, h7, e1, e2]
  · have h6 := y_sq_le hx hδ1
    rw [← hy] at h6
    nlinarith only [h5, h6, hy1]

/-- **The bound of the first change**: `5Γ + coneRadius ≤ D`, for `τ = 2x^{δ/100−1/4}`, `S ≤ C_S Λ`,
`Γ ≤ C_Γ x^{3/4} Λ`, from `C Λ² ≤ y`. -/
theorem coneRadius_le {δ C K₁ T S lg x Γ Cs CΓ Λ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 < C)
    (hK₁ : 0 ≤ K₁) (hT : 0 ≤ T) (hS : 1 ≤ S) (hx : 1 ≤ x) (hlg0 : 0 ≤ lg) (hlg : lg ≤ Λ)
    (hSΛ : S ≤ Cs * Λ) (hΛ : 1 ≤ Λ) (hΓ : Γ ≤ CΓ * x ^ ((3 : ℝ) / 4) * Λ) (hCΓ : 0 ≤ CΓ)
    (hCs : 0 ≤ Cs)
    (hy : (5 * CΓ + (1 + T) * (K₁ * Cs ^ 2) +
        slopeFactor T * C * (Cs * (2 * (1 + T)) + 4)) * Λ ^ 2 ≤ x ^ (δ / 200)) :
    5 * Γ + coneRadius δ C K₁ T S lg x (2 * x ^ (δ / 100 - 1 / 4)) ≤
      x ^ ((3 : ℝ) / 4 + δ / 200) := by
  have hx0 : 0 < x := by linarith only [hx]
  set X := x ^ ((3 : ℝ) / 4) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hx (by norm_num)
  have hΛ0 : 0 < Λ := by linarith only [hΛ]
  have hΛ2 : Λ ≤ Λ ^ 2 := by nlinarith only [hΛ]
  set E := x ^ (δ / 100 - 1 / 4) with hE
  have hE0 : 0 ≤ E := by positivity
  have hsf := slopeFactor_pos hT
  set sf := slopeFactor T with hsfdef
  -- the first term
  have t1 : 5 * Γ ≤ 5 * CΓ * Λ ^ 2 * X := by
    have h1 : CΓ * X * Λ ≤ CΓ * X * Λ ^ 2 := mul_le_mul_of_nonneg_left hΛ2 (by positivity)
    linarith only [h1, hΓ]
  -- the term near the endpoints
  have t2 : (1 + T) * (K₁ * S ^ 2) ≤ (1 + T) * (K₁ * Cs ^ 2) * Λ ^ 2 * X := by
    have hS2 : S ^ 2 ≤ Cs ^ 2 * Λ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith only [hS]) hSΛ 2
    have h1 : (1 + T) * (K₁ * S ^ 2) ≤ (1 + T) * (K₁ * (Cs ^ 2 * Λ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS2 hK₁) (by positivity)
    have h2 : (1 + T) * (K₁ * Cs ^ 2) * Λ ^ 2 ≤ (1 + T) * (K₁ * Cs ^ 2) * Λ ^ 2 * X :=
      le_mul_of_one_le_right (by positivity) hX1
    have e : (1 + T) * (K₁ * (Cs ^ 2 * Λ ^ 2)) = (1 + T) * (K₁ * Cs ^ 2) * Λ ^ 2 := by ring
    linarith only [h1, h2, e]
  -- `S^{1/2} (2(1 + T)x)^{3/4}`
  have t3 : S ^ ((1 : ℝ) / 2) * (2 * (1 + T) * x) ^ ((3 : ℝ) / 4) ≤
      Cs * (2 * (1 + T)) * Λ ^ 2 * X := by
    have h1 : S ^ ((1 : ℝ) / 2) ≤ S := by
      calc S ^ ((1 : ℝ) / 2) ≤ S ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hS (by norm_num)
        _ = S := Real.rpow_one S
    have h2 : (2 * (1 + T) * x) ^ ((3 : ℝ) / 4) = (2 * (1 + T)) ^ ((3 : ℝ) / 4) * X := by
      rw [Real.mul_rpow (by positivity) hx0.le]
    have h3 : (2 * (1 + T)) ^ ((3 : ℝ) / 4) ≤ 2 * (1 + T) := by
      calc (2 * (1 + T)) ^ ((3 : ℝ) / 4) ≤ (2 * (1 + T)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith only [hT]) (by norm_num)
        _ = 2 * (1 + T) := Real.rpow_one _
    rw [h2]
    calc S ^ ((1 : ℝ) / 2) * ((2 * (1 + T)) ^ ((3 : ℝ) / 4) * X)
        ≤ (Cs * Λ ^ 2) * ((2 * (1 + T)) * X) := by
          refine mul_le_mul ?_ (mul_le_mul_of_nonneg_right h3 (by positivity)) (by positivity)
            (by positivity)
          have := mul_le_mul_of_nonneg_left hΛ2 hCs
          linarith only [h1, hSΛ, this]
      _ = Cs * (2 * (1 + T)) * Λ ^ 2 * X := by ring
  -- `x τ^{1+δ/2} log N`
  have t4 : x * ((2 * E) ^ (1 + δ / 2) * lg) ≤ 4 * Λ ^ 2 * X := by
    have h1 : (2 * E) ^ (1 + δ / 2) = 2 ^ (1 + δ / 2) * E ^ (1 + δ / 2) := by
      rw [Real.mul_rpow (by norm_num) hE0]
    have h2 : (2 : ℝ) ^ (1 + δ / 2) ≤ 4 := by
      calc (2 : ℝ) ^ (1 + δ / 2) ≤ 2 ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hδ1])
        _ = 4 := by norm_num
    have h3 := mul_e_rpow_le hx hδ hδ1
    rw [← hE, ← hX] at h3
    have hE2 : 0 ≤ E ^ (1 + δ / 2) := by positivity
    have hxE : 0 ≤ x * E ^ (1 + δ / 2) := by positivity
    calc x * ((2 * E) ^ (1 + δ / 2) * lg)
        = 2 ^ (1 + δ / 2) * (x * E ^ (1 + δ / 2)) * lg := by rw [h1]; ring
      _ ≤ 4 * X * Λ ^ 2 := by
          refine mul_le_mul (mul_le_mul h2 h3 hxE (by norm_num)) (hlg.trans hΛ2) hlg0
            (by positivity)
      _ = 4 * Λ ^ 2 * X := by ring
  have t5 : sf * C * (S ^ ((1 : ℝ) / 2) * (2 * (1 + T) * x) ^ ((3 : ℝ) / 4) +
      x * ((2 * E) ^ (1 + δ / 2) * lg)) ≤ sf * C * (Cs * (2 * (1 + T)) + 4) * Λ ^ 2 * X := by
    have := mul_le_mul_of_nonneg_left (add_le_add t3 t4) (by positivity : 0 ≤ sf * C)
    linarith only [this]
  have hD : x ^ ((3 : ℝ) / 4 + δ / 200) = X * x ^ (δ / 200) := Real.rpow_add hx0 _ _
  have hfin := mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ X)
  rw [hD]
  unfold coneRadius
  linarith only [t1, t2, t5, hfin]

/-- **The base fact**: for `C, κ > 0`, `C log²(2 + N) ≤ (κ N)^{δ/200}` for `N` large. -/
theorem exists_base {C κ δ : ℝ} (hC : 0 < C) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C * Real.log (2 + N) ^ 2 ≤ (κ * N) ^ (δ / 200) := by
  have hc : 0 < Real.sqrt (κ ^ (δ / 200) / C) := by positivity
  have h := Moments.eventually_log_two_add_le_rpow (r := δ / 400) (by positivity) hc
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 h
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have h1 := hN₁ N (le_trans (le_max_left _ _) hN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) ≤ N := by linarith only [hN1]
  have hlog : 0 ≤ Real.log (2 + N) := Real.log_nonneg (by linarith only [hN1])
  have h2 : Real.log (2 + N) ^ 2 ≤ (Real.sqrt (κ ^ (δ / 200) / C) * (N : ℝ) ^ (δ / 400)) ^ 2 :=
    pow_le_pow_left₀ hlog h1 2
  rw [mul_pow, Real.sq_sqrt (by positivity)] at h2
  have h3 : ((N : ℝ) ^ (δ / 400)) ^ 2 = (N : ℝ) ^ (δ / 200) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    congr 1
    push_cast
    ring
  rw [h3] at h2
  rw [Real.mul_rpow hκ.le hN0]
  calc C * Real.log (2 + N) ^ 2 ≤ C * (κ ^ (δ / 200) / C * (N : ℝ) ^ (δ / 200)) :=
        mul_le_mul_of_nonneg_left h2 hC.le
    _ = κ ^ (δ / 200) * (N : ℝ) ^ (δ / 200) := by field_simp

/-- **The third change, for `N` large**: `K₀ N^q e^{−(log N/C)²} ≤ 1`. -/
theorem exists_holder {K₀ q C : ℝ} (hK₀ : 0 < K₀) (hq : 0 ≤ q) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      K₀ * (N : ℝ) ^ q * Real.exp (-(Real.log N / C) ^ 2) ≤ 1 := by
  set Y := C ^ 2 * (q + |Real.log K₀| + 1) + 1 with hY
  refine ⟨⌈Real.exp Y⌉₊ + 1, fun N hN => ?_⟩
  have hexp : Real.exp Y ≤ N := by
    have h1 := Nat.le_ceil (Real.exp Y)
    have h2 : ((⌈Real.exp Y⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈Real.exp Y⌉₊ ≤ N)
    linarith only [h1, h2]
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hexp
  set y := Real.log N with hy
  have hyY : Y ≤ y := by
    rw [hy, Real.le_log_iff_exp_le hN0]
    exact hexp
  have hab := abs_nonneg (Real.log K₀)
  have hY1 : 1 ≤ Y := by
    have : 0 ≤ C ^ 2 * (q + |Real.log K₀| + 1) := by positivity
    linarith only [this, hY]
  have hy1 : 1 ≤ y := hY1.trans hyY
  have hkey : Real.log K₀ + q * y - (y / C) ^ 2 ≤ 0 := by
    have h1 : (y / C) ^ 2 = y * (y / C ^ 2) := by field_simp
    have h2 : q + |Real.log K₀| + 1 ≤ y / C ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith only [hyY, hY, mul_comm (q + |Real.log K₀| + 1) (C ^ 2)]
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith only [hy1] : 0 ≤ y)
    have h4 : Real.log K₀ ≤ |Real.log K₀| := le_abs_self _
    have h5 : |Real.log K₀| ≤ y * |Real.log K₀| := le_mul_of_one_le_left hab hy1
    rw [h1]
    nlinarith only [h3, h4, h5, hy1]
  have e : K₀ * (N : ℝ) ^ q * Real.exp (-(y / C) ^ 2) =
      Real.exp (Real.log K₀ + q * y - (y / C) ^ 2) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hK₀, Real.rpow_def_of_pos hN0,
      mul_comm (Real.log (N : ℝ)) q]
  rw [e]
  exact Real.exp_le_one_iff.2 hkey

end CurvatureVariance.Paper.Localization.Loc
