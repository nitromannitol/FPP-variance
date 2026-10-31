/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cone bounds at the scale `n` are small

The numerics of the proof of Lemma `lem:slabs` (2): "at distance at least `n` from its endpoints,
the right side of equation `eq:cone` is much smaller than `n^{δ/100−1/4}` for `N` large, since
`S^{1/2} n^{−δ/100}` and `n^{−(δ/2)(1/4−δ/100)} log N` tend to zero". With `ρ = n^{δ/100−1/4}`,
`n ≥ √N` and `log N ≤ S ≤ N^{δ/1000}`:

* `S^{1/2} r^{−1/4} ≤ N^{δ/2000} n^{−1/4} ≤ N^{−9δ/2000} ρ` for `r ≥ n`;
* for `x ≤ 3ρ`: `x^{1+δ/2} log N ≤ 9 ρ N^{−3δ/50} log N`, as `ρ^{δ/2} ≤ N^{−3δ/50}`;

so `C (S^{1/2} r^{−1/4} + x^{1+δ/2} log N) ≤ ε ρ` for `N ≥ N₀(δ, C, ε)` (`cone_rhs_le_of`,
`eventually_cone_small`). The same threshold gives `C S² ≤ n` (the cone bounds apply at distance
`n`), `ρ ≤ 1/3` and `N ≥ 6`.
-/

@[expose] public section

open Filter

namespace CurvatureVariance.Paper.Proofs.Geometry

/-- Eventually `B ≤ N^c`, for `c > 0`. -/
theorem eventually_le_rpow_natCast {c : ℝ} (hc : 0 < c) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, B ≤ (N : ℝ) ^ c :=
  ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B

/-- Eventually `log N ≤ κ N^c`, for `c, κ > 0`. -/
theorem eventually_log_le_mul_rpow {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop, Real.log N ≤ κ * (N : ℝ) ^ c := by
  have h := tendsto_natCast_atTop_atTop.eventually ((isLittleO_log_rpow_atTop hc).bound hκ)
  filter_upwards [h] with N hN
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0] at hN
  exact (le_abs_self _).trans hN

/-- `(√N)^c = N^{c/2}`. -/
theorem sqrt_rpow_eq {N c : ℝ} (hN : 0 ≤ N) : Real.sqrt N ^ c = N ^ (c / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN]
  ring_nf

/-- The first term of equation `eq:cone` at distance `r ≥ n`:
`C S^{1/2} r^{−1/4} ≤ (ε/2) n^{δ/100−1/4}`, if `2C/ε ≤ N^{9δ/2000}`, `n ≥ √N` and
`0 ≤ S ≤ N^{δ/1000}`. -/
theorem first_term_le {δ C ε : ℝ} (hδ : 0 < δ) (hC : 0 < C) (hε : 0 < ε) {N : ℕ}
    (hN1 : 1 ≤ (N : ℝ)) (h1 : 2 * C / ε ≤ (N : ℝ) ^ (9 * δ / 2000)) {n : ℕ}
    (hn : Real.sqrt N ≤ n) {S : ℝ} (hS0 : 0 ≤ S) (hSN : S ≤ (N : ℝ) ^ (δ / 1000)) {r : ℝ}
    (hr : (n : ℝ) ≤ r) :
    C * (S ^ ((1 : ℝ) / 2) * r ^ (-(1 : ℝ) / 4)) ≤ ε / 2 * (n : ℝ) ^ (δ / 100 - 1 / 4) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hn0 : (0 : ℝ) < n := hsN.trans_le hn
  have hS : S ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (δ / 2000) := by
    calc S ^ ((1 : ℝ) / 2) ≤ ((N : ℝ) ^ (δ / 1000)) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow hS0 hSN (by norm_num)
      _ = (N : ℝ) ^ (δ / 2000) := by rw [← Real.rpow_mul hN0.le]; ring_nf
  have hr4 : r ^ (-(1 : ℝ) / 4) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_nonpos hn0 hr (by norm_num)
  have hna : (n : ℝ) ^ (δ / 100 - 1 / 4) = (n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ (δ / 100) := by
    rw [← Real.rpow_add hn0]; ring_nf
  have hnδ : (N : ℝ) ^ (δ / 2000) * (N : ℝ) ^ (9 * δ / 2000) ≤ (n : ℝ) ^ (δ / 100) := by
    rw [← Real.rpow_add hN0]
    calc (N : ℝ) ^ (δ / 2000 + 9 * δ / 2000) = Real.sqrt N ^ (δ / 100) := by
          rw [sqrt_rpow_eq hN0.le]; ring_nf
      _ ≤ (n : ℝ) ^ (δ / 100) := Real.rpow_le_rpow hsN.le hn (by positivity)
  have hS0' : 0 ≤ S ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hS0 _
  have hP : 0 < (n : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos hn0 _
  have hA : 0 < (N : ℝ) ^ (δ / 2000) := Real.rpow_pos_of_pos hN0 _
  have hC' : C ≤ ε / 2 * (N : ℝ) ^ (9 * δ / 2000) := by
    rw [div_le_iff₀ hε] at h1
    linarith
  calc C * (S ^ ((1 : ℝ) / 2) * r ^ (-(1 : ℝ) / 4))
      ≤ C * ((N : ℝ) ^ (δ / 2000) * (n : ℝ) ^ (-(1 : ℝ) / 4)) := by
        gcongr
        exact Real.rpow_nonneg (by linarith) _
    _ ≤ ε / 2 * (N : ℝ) ^ (9 * δ / 2000) * ((N : ℝ) ^ (δ / 2000) * (n : ℝ) ^ (-(1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right hC' (by positivity)
    _ = ε / 2 * (n : ℝ) ^ (-(1 : ℝ) / 4) *
          ((N : ℝ) ^ (δ / 2000) * (N : ℝ) ^ (9 * δ / 2000)) := by ring
    _ ≤ ε / 2 * (n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ (δ / 100) :=
        mul_le_mul_of_nonneg_left hnδ (by positivity)
    _ = ε / 2 * (n : ℝ) ^ (δ / 100 - 1 / 4) := by rw [hna]; ring

/-- `ρ^{δ/2} ≤ N^{−3δ/50}` for `ρ = n^{δ/100−1/4}`, `n ≥ √N`, `0 < δ ≤ 1`. -/
theorem rpow_half_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN1 : 1 ≤ (N : ℝ)) {n : ℕ}
    (hn : Real.sqrt N ≤ n) :
    ((n : ℝ) ^ (δ / 100 - 1 / 4)) ^ (δ / 2) ≤ (N : ℝ) ^ (-(3 * δ / 50)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hn0 : (0 : ℝ) < n := hsN.trans_le hn
  have hneg : (δ / 100 - 1 / 4) * (δ / 2) ≤ 0 := by nlinarith
  rw [← Real.rpow_mul hn0.le]
  calc (n : ℝ) ^ ((δ / 100 - 1 / 4) * (δ / 2))
      ≤ Real.sqrt N ^ ((δ / 100 - 1 / 4) * (δ / 2)) :=
        Real.rpow_le_rpow_of_nonpos hsN hn hneg
    _ = (N : ℝ) ^ ((δ / 100 - 1 / 4) * (δ / 2) / 2) := sqrt_rpow_eq hN0.le
    _ ≤ (N : ℝ) ^ (-(3 * δ / 50)) := by
        refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
        nlinarith

/-- The second term of equation `eq:cone`: `C x^{1+δ/2} log N ≤ (ε/2) n^{δ/100−1/4}` for
`0 ≤ x ≤ 3 n^{δ/100−1/4}`, if `18 C log N ≤ ε N^{3δ/50}` and `n ≥ √N`. -/
theorem second_term_le {δ C ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 < C) {N : ℕ}
    (hN1 : 1 ≤ (N : ℝ)) (h2 : 18 * C * Real.log N ≤ ε * (N : ℝ) ^ (3 * δ / 50)) {n : ℕ}
    (hn : Real.sqrt N ≤ n) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3 * (n : ℝ) ^ (δ / 100 - 1 / 4)) :
    C * (x ^ (1 + δ / 2) * Real.log N) ≤ ε / 2 * (n : ℝ) ^ (δ / 100 - 1 / 4) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hn0 : (0 : ℝ) < n := hsN.trans_le hn
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  set ρ := (n : ℝ) ^ (δ / 100 - 1 / 4) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hn0 _
  set Q := (N : ℝ) ^ (-(3 * δ / 50)) with hQ
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hN0 _
  have hQQ : Q * (N : ℝ) ^ (3 * δ / 50) = 1 := by
    rw [hQ, Real.rpow_neg hN0.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hN0 _).ne']
  have h3 : (3 : ℝ) ^ (δ / 2) ≤ 3 := by
    calc (3 : ℝ) ^ (δ / 2) ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 3 := Real.rpow_one 3
  have hx' : x ^ (1 + δ / 2) ≤ 9 * ρ * Q := by
    calc x ^ (1 + δ / 2) ≤ (3 * ρ) ^ (1 + δ / 2) := Real.rpow_le_rpow hx0 hx (by positivity)
      _ = 3 * ρ * ((3 : ℝ) ^ (δ / 2) * ρ ^ (δ / 2)) := by
          rw [Real.rpow_add (by positivity), Real.rpow_one,
            Real.mul_rpow (by norm_num) hρ0.le]
      _ ≤ 3 * ρ * (3 * Q) := by
          gcongr
          exact rpow_half_le hδ hδ1 hN1 hn
      _ = 9 * ρ * Q := by ring
  have hlogQ : 18 * C * Real.log N * Q ≤ ε := by
    calc 18 * C * Real.log N * Q ≤ ε * (N : ℝ) ^ (3 * δ / 50) * Q :=
          mul_le_mul_of_nonneg_right h2 hQ0.le
      _ = ε := by rw [mul_assoc, mul_comm _ Q, hQQ, mul_one]
  calc C * (x ^ (1 + δ / 2) * Real.log N) ≤ C * (9 * ρ * Q * Real.log N) := by
        gcongr
    _ = ρ / 2 * (18 * C * Real.log N * Q) := by ring
    _ ≤ ρ / 2 * ε := mul_le_mul_of_nonneg_left hlogQ (by positivity)
    _ = ε / 2 * ρ := by ring

/-- **The cone bound `eq:cone` at the scale `n` is small**, for one `N`: under the two numerical
conditions on `N`, for `n ≥ √N`, `0 ≤ S ≤ N^{δ/1000}`, `r ≥ n` and `0 ≤ x ≤ 3 n^{δ/100−1/4}`,
`C (S^{1/2} r^{−1/4} + x^{1+δ/2} log N) ≤ ε n^{δ/100−1/4}`. -/
theorem cone_rhs_le_of {δ C ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 < C) (hε : 0 < ε) {N : ℕ}
    (hN1 : 1 ≤ (N : ℝ)) (h1 : 2 * C / ε ≤ (N : ℝ) ^ (9 * δ / 2000))
    (h2 : 18 * C * Real.log N ≤ ε * (N : ℝ) ^ (3 * δ / 50)) {n : ℕ} (hn : Real.sqrt N ≤ n)
    {S : ℝ} (hS0 : 0 ≤ S) (hSN : S ≤ (N : ℝ) ^ (δ / 1000)) {r : ℝ} (hr : (n : ℝ) ≤ r) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 3 * (n : ℝ) ^ (δ / 100 - 1 / 4)) :
    C * (S ^ ((1 : ℝ) / 2) * r ^ (-(1 : ℝ) / 4) + x ^ (1 + δ / 2) * Real.log N) ≤
      ε * (n : ℝ) ^ (δ / 100 - 1 / 4) := by
  have e1 := first_term_le hδ hC hε hN1 h1 hn hS0 hSN hr
  have e2 := second_term_le hδ hδ1 hC hN1 h2 hn hx0 hx
  linarith

/-- **The cone bounds at the scale `n` are small** (the proof of Lemma `lem:slabs` (2)). For
`0 < δ ≤ 1`, `C, ε > 0` and `N` large: `N ≥ 6`, and for `n ≥ √N`, `n^{δ/100−1/4} ≤ 1/3`; for
`log N ≤ S ≤ N^{δ/1000}` also `C S² ≤ n`, and
`C (S^{1/2} r^{−1/4} + x^{1+δ/2} log N) ≤ ε n^{δ/100−1/4}` for `r ≥ n` and
`0 ≤ x ≤ 3 n^{δ/100−1/4}`. -/
theorem eventually_cone_small {δ C ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (6 : ℝ) ≤ N ∧ ∀ n : ℕ, Real.sqrt N ≤ n →
      (n : ℝ) ^ (δ / 100 - 1 / 4) ≤ 1 / 3 ∧
      ∀ S : ℝ, Real.log N ≤ S → S ≤ (N : ℝ) ^ (δ / 1000) → C * S ^ 2 ≤ n ∧
        ∀ r : ℝ, (n : ℝ) ≤ r → ∀ x : ℝ, 0 ≤ x → x ≤ 3 * (n : ℝ) ^ (δ / 100 - 1 / 4) →
          C * (S ^ ((1 : ℝ) / 2) * r ^ (-(1 : ℝ) / 4) + x ^ (1 + δ / 2) * Real.log N) ≤
            ε * (n : ℝ) ^ (δ / 100 - 1 / 4) := by
  have E0 : ∀ᶠ N : ℕ in atTop, (6 : ℝ) ≤ N := by
    filter_upwards [eventually_ge_atTop 6] with N hN
    exact_mod_cast hN
  have E1 := eventually_le_rpow_natCast (c := 9 * δ / 2000) (by positivity) (2 * C / ε)
  have E2 := eventually_log_le_mul_rpow (c := 3 * δ / 50) (κ := ε / (18 * C)) (by positivity)
    (by positivity)
  have E3 := eventually_le_rpow_natCast (c := (1 / 4 - δ / 100) / 2) (by linarith) 3
  have E4 := eventually_le_rpow_natCast (c := 1 / 2 - δ / 500) (by linarith) C
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (E0.and (E1.and (E2.and (E3.and E4))))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h0, h1, h2, h3, h4⟩ := hN₀ N hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have h2' : 18 * C * Real.log N ≤ ε * (N : ℝ) ^ (3 * δ / 50) := by
    have e : 18 * C * (ε / (18 * C)) = ε := by field_simp
    calc 18 * C * Real.log N ≤ 18 * C * (ε / (18 * C) * (N : ℝ) ^ (3 * δ / 50)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ε * (N : ℝ) ^ (3 * δ / 50) := by rw [← mul_assoc, e]
  refine ⟨h0, fun n hn => ⟨?_, fun S hS hSN => ⟨?_, fun r hr x hx0 hx =>
    cone_rhs_le_of hδ hδ1 hC hε hN1 h1 h2' hn ((Real.log_nonneg hN1).trans hS) hSN hr hx0 hx⟩⟩⟩
  · -- `n^{δ/100−1/4} ≤ (√N)^{δ/100−1/4} = 1 / N^{(1/4−δ/100)/2} ≤ 1/3`
    have hn0 : (0 : ℝ) < n := hsN.trans_le hn
    calc (n : ℝ) ^ (δ / 100 - 1 / 4) ≤ Real.sqrt N ^ (δ / 100 - 1 / 4) :=
          Real.rpow_le_rpow_of_nonpos hsN hn (by linarith)
      _ = ((N : ℝ) ^ ((1 / 4 - δ / 100) / 2))⁻¹ := by
          rw [sqrt_rpow_eq hN0.le, ← Real.rpow_neg hN0.le]; ring_nf
      _ ≤ 1 / 3 := (inv_anti₀ (by norm_num) h3).trans_eq (one_div 3).symm
  · -- `C S² ≤ C N^{δ/500} ≤ N^{1/2} ≤ n`
    have hS0 : 0 ≤ S := (Real.log_nonneg hN1).trans hS
    have hS2 : S ^ 2 ≤ (N : ℝ) ^ (δ / 500) := by
      calc S ^ 2 ≤ ((N : ℝ) ^ (δ / 1000)) ^ 2 := pow_le_pow_left₀ hS0 hSN 2
        _ = (N : ℝ) ^ (δ / 500) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    have hsq : Real.sqrt N = (N : ℝ) ^ (1 / 2 - δ / 500) * (N : ℝ) ^ (δ / 500) := by
      rw [← Real.rpow_add hN0, Real.sqrt_eq_rpow]; ring_nf
    calc C * S ^ 2 ≤ C * (N : ℝ) ^ (δ / 500) := mul_le_mul_of_nonneg_left hS2 hC.le
      _ ≤ (N : ℝ) ^ (1 / 2 - δ / 500) * (N : ℝ) ^ (δ / 500) :=
          mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hN0.le _)
      _ = Real.sqrt N := hsq.symm
      _ ≤ n := hn

end CurvatureVariance.Paper.Proofs.Geometry
