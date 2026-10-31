/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.Scales
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The "if `N` is sufficiently large" thresholds of Section `sec:exponential`

Explicit thresholds `N₀`, uniform in `A` and `K`:

* equation `eq:regime` makes `W_s / s` small at lengths comparable to `N` (`exists_W_le`; this is
  what "if `N` is sufficiently large" in Section `sec:exponential` uses, uniformly in `A`);
* powers of logarithms are below `Q_s` at lengths comparable to `N` (`exists_log_le`).

Both come from the elementary bound `log x ≤ x^ε / ε` (`Real.log_le_rpow_div`).
-/

@[expose] public section

namespace IsotropicVariance.Paper.Proofs.Profiles

/-- `log (2 + N) ≤ δ N` once `N ≥ 2` and `N ≥ 8 / δ²`. -/
lemma log_two_add_le_mul {δ N : ℝ} (hδ : 0 < δ) (hN2 : 2 ≤ N) (hN : 8 / δ ^ 2 ≤ N) :
    Real.log (2 + N) ≤ δ * N := by
  have h1 : Real.log (2 + N) ≤ 2 * Real.sqrt (2 + N) := by
    have h := Real.log_le_rpow_div (x := 2 + N) (ε := 1 / 2) (by linarith) (by norm_num)
    have e : (2 + N) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (2 + N) ^ (1 / 2 : ℝ) := by ring
    rw [Real.sqrt_eq_rpow]
    linarith
  have h2 : Real.sqrt (2 + N) ≤ Real.sqrt (2 * N) := Real.sqrt_le_sqrt (by linarith)
  set t := Real.sqrt (2 * N) with ht_def
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 2 * N := Real.sq_sqrt (by linarith)
  have ht : 4 / δ ≤ t := by
    rw [ht_def, Real.le_sqrt (by positivity) (by linarith), div_pow]
    rw [div_le_iff₀ (by positivity)] at hN ⊢
    linarith
  have hδt : 4 ≤ δ * t := by
    rw [div_le_iff₀ hδ] at ht
    linarith
  have h3 : 2 * t ≤ δ * N := by nlinarith
  linarith

/-- `√(N log (2 + N)) ≤ δ N` once `N ≥ 2` and `N ≥ 8 / δ⁴`. -/
lemma sqrt_mul_log_le_mul {δ N : ℝ} (hδ : 0 < δ) (hN2 : 2 ≤ N) (hN : 8 / δ ^ 4 ≤ N) :
    Real.sqrt (N * Real.log (2 + N)) ≤ δ * N := by
  have e : (δ ^ 2) ^ 2 = δ ^ 4 := by ring
  have hlog := log_two_add_le_mul (δ := δ ^ 2) (by positivity) hN2 (by rwa [e])
  rw [show δ * N = Real.sqrt ((δ * N) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  calc N * Real.log (2 + N) ≤ N * (δ ^ 2 * N) :=
        mul_le_mul_of_nonneg_left hlog (by linarith)
    _ = (δ * N) ^ 2 := by ring

/-- Equation `eq:regime` makes `W_s / s` small at lengths comparable to `N`, uniformly in `A` and
`K`. -/
theorem exists_W_le (Cstar c₁ ε : ℝ) (hc₁ : 0 < c₁) (hε : 0 < ε) :
    ∃ N₀ : ℝ, ∀ K : ℕ, 10 ≤ K → ∀ A N : ℝ, 0 ≤ A → N₀ ≤ N → Regime Cstar K A N →
      ∀ s : ℝ, c₁ * N ≤ s → s ≤ N → W K A s ≤ ε * s := by
  set D := max Cstar 1
  have hD : 0 < D := lt_of_lt_of_le one_pos (le_max_right _ _)
  set δ := ε ^ 2 * c₁ / D
  have hδ : 0 < δ := by positivity
  refine ⟨max 2 (8 / δ ^ 4), fun K hK A N hA hN hreg s hs hsN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hN8 : 8 / δ ^ 4 ≤ N := le_trans (le_max_right _ _) hN
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  have hQ : Q K A N ≤ ε ^ 2 * c₁ * N := by
    calc Q K A N ≤ Cstar * Real.sqrt (N * Real.log (2 + N)) := hreg
      _ ≤ D * Real.sqrt (N * Real.log (2 + N)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      _ ≤ D * (δ * N) := mul_le_mul_of_nonneg_left (sqrt_mul_log_le_mul hδ hN2 hN8) hD.le
      _ = ε ^ 2 * c₁ * N := by
          simp only [δ]
          field_simp
  have hW2 : s * Q K A s ≤ (ε * s) ^ 2 := by
    have hcs : ε ^ 2 * (c₁ * N) ≤ ε ^ 2 * s := mul_le_mul_of_nonneg_left hs (sq_nonneg ε)
    calc s * Q K A s ≤ s * Q K A N := mul_le_mul_of_nonneg_left (Q_mono hK hA hs0 hsN) hs0
      _ ≤ s * (ε ^ 2 * c₁ * N) := mul_le_mul_of_nonneg_left hQ hs0
      _ ≤ s * (ε ^ 2 * s) := mul_le_mul_of_nonneg_left (by linarith) hs0
      _ = (ε * s) ^ 2 := by ring
  calc W K A s = Real.sqrt (s * Q K A s) := rfl
    _ ≤ Real.sqrt ((ε * s) ^ 2) := Real.sqrt_le_sqrt hW2
    _ = ε * s := Real.sqrt_sq (by positivity)

/-- Powers of logarithms are below `Q_s` at lengths comparable to `N`, uniformly in `A ≥ 1` and
`K ≥ 10`. -/
theorem exists_log_le (C c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ N₀ : ℝ, ∀ K : ℕ, 10 ≤ K → ∀ A N : ℝ, 1 ≤ A → N₀ ≤ N →
      ∀ s : ℝ, c₁ * N ≤ s → C * Real.log (2 + N) ^ 2 ≤ Q K A s := by
  set D := max C 1
  have hD : 0 < D := lt_of_lt_of_le one_pos (le_max_right _ _)
  set κ := (c₁ / 2) ^ (2 / 5 : ℝ)
  have hκ : 0 < κ := Real.rpow_pos_of_pos (by positivity) _
  set B := 100 * D / κ
  have hB0 : 0 ≤ B := by positivity
  refine ⟨max (max 2 (1 / c₁)) (B ^ 5), fun K hK A N hA hN s hs => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNc : 1 / c₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNB : B ^ 5 ≤ N := le_trans (le_max_right _ _) hN
  have hc₁N : 1 ≤ c₁ * N := by
    rw [div_le_iff₀ hc₁] at hNc
    linarith
  have hs1 : 1 ≤ s := hc₁N.trans hs
  have hx : 0 < 2 + N := by linarith
  -- `Q_s ≥ (c₁ N)^{2/5} ≥ κ (2 + N)^{2/5}`.
  have hQ : κ * ((2 + N) ^ (1 / 5 : ℝ)) ^ 2 ≤ Q K A s := by
    have hv2 : ((2 + N) ^ (1 / 5 : ℝ)) ^ 2 = (2 + N) ^ (2 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      norm_num
    calc κ * ((2 + N) ^ (1 / 5 : ℝ)) ^ 2 = (c₁ / 2 * (2 + N)) ^ (2 / 5 : ℝ) := by
          rw [hv2, Real.mul_rpow (by positivity) hx.le]
      _ ≤ (c₁ * N) ^ (2 / 5 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
      _ ≤ s ^ (2 / 5 : ℝ) := Real.rpow_le_rpow (by positivity) hs (by norm_num)
      _ ≤ s ^ qExp K := Real.rpow_le_rpow_of_exponent_le hs1 (qExp_ge hK)
      _ ≤ A * s ^ qExp K := le_mul_of_one_le_left (by positivity) hA
      _ = Q K A s := (Q_eq K A s).symm
  -- `log (2 + N)² ≤ 100 (2 + N)^{1/5}`.
  have hlog : Real.log (2 + N) ^ 2 ≤ 100 * (2 + N) ^ (1 / 5 : ℝ) := by
    have h := Real.log_le_rpow_div (x := 2 + N) (ε := 1 / 10) hx.le (by norm_num)
    have hl0 : 0 ≤ Real.log (2 + N) := Real.log_nonneg (by linarith)
    have hu2 : ((2 + N) ^ (1 / 10 : ℝ)) ^ 2 = (2 + N) ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      norm_num
    have e : (2 + N) ^ (1 / 10 : ℝ) / (1 / 10) = 10 * (2 + N) ^ (1 / 10 : ℝ) := by ring
    have h' : Real.log (2 + N) ≤ 10 * (2 + N) ^ (1 / 10 : ℝ) := by linarith
    calc Real.log (2 + N) ^ 2 ≤ (10 * (2 + N) ^ (1 / 10 : ℝ)) ^ 2 := pow_le_pow_left₀ hl0 h' 2
      _ = 100 * (2 + N) ^ (1 / 5 : ℝ) := by rw [mul_pow, hu2]; norm_num
  -- `(2 + N)^{1/5} ≥ B`.
  have hvB : B ≤ (2 + N) ^ (1 / 5 : ℝ) := by
    have hB5 : (B ^ 5) ^ (1 / 5 : ℝ) = B := by
      rw [show (1 / 5 : ℝ) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast hB0 (by norm_num)
    calc B = (B ^ 5) ^ (1 / 5 : ℝ) := hB5.symm
      _ ≤ (2 + N) ^ (1 / 5 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hv0 : 0 ≤ (2 + N) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hx.le _
  have h100 : 100 * D ≤ κ * (2 + N) ^ (1 / 5 : ℝ) := by
    have h := hvB
    simp only [B] at h
    rw [div_le_iff₀ hκ] at h
    linarith
  calc C * Real.log (2 + N) ^ 2 ≤ D * Real.log (2 + N) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ D * (100 * (2 + N) ^ (1 / 5 : ℝ)) := mul_le_mul_of_nonneg_left hlog hD.le
    _ = 100 * D * (2 + N) ^ (1 / 5 : ℝ) := by ring
    _ ≤ κ * (2 + N) ^ (1 / 5 : ℝ) * (2 + N) ^ (1 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right h100 hv0
    _ = κ * ((2 + N) ^ (1 / 5 : ℝ)) ^ 2 := by ring
    _ ≤ Q K A s := hQ

end IsotropicVariance.Paper.Proofs.Profiles
