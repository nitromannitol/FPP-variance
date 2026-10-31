/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Proofs.Responses.RadiusMoments
import CurvatureVariance.Paper.Proofs.Responses.LocalizationMoment
import CurvatureVariance.Paper.Proofs.Responses.WidthBridge
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform raw-radius moments on retained pairs

The localization contract applies to the actual center slope of each pair of row cubes. Its
high moment controls the moment required for the array of squared radii. Constants precede
`K` and thresholds follow `K`; both precede every model fitting the common bounds `bd`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper.Responses

/-- Uniform `8d` moments of the raw radius on every retained pair of a target's rows, from Lemma
`lem:localization` and equation `eq:scales`. -/
theorem raw_radius_moments {m : ℕ} (hscales : ScalesStatement m)
    (hrad : LocalizationStatement m) :
    ∀ bd : Bounds m, bd.Valid → ∀ Cstar Cd : ℝ, 0 ≤ Cd → ∃ D : ℝ, 0 < D ∧
    ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
    ∀ M : Model m, M.Standing → M.Fits bd → ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
    Premise M K A N → RangeA M K A N Cstar →
    ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
    ∀ (i : ℕ) (j k : Fin m → ℤ),
      8 * (wInt M K A n : ℝ) * ‖transversePoint (k - j)‖ ≤
        (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) →
      (∫⁻ ω, slabRadius M K A Cd ω n (targetSlope ℓ y) i j k ^ (8 * (m + 1)) ∂M.P) ≤
        ENNReal.ofReal D := by
  intro bd hbd Cstar Cd hCd
  obtain ⟨Cb, hCb, hloc⟩ := exists_radius_moments_of hrad bd hbd Cstar
  let p := 128 * (m + 1) ^ 2
  let q := 8 * (m + 1)
  refine ⟨(2 * Cd + 1) ^ q * Cb ^ p, by positivity, ?_⟩
  intro K hK
  have hKpos : (0 : ℝ) < K := by
    have hK1 : 1 ≤ K := by omega
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK1)
  obtain ⟨Nr, hNr⟩ := hloc (1 / (9 * K)) (by positivity) K hK
  obtain ⟨Nw, hNw⟩ := eventually_row_width_small hscales bd hbd Cstar K hK
  refine ⟨max ((9 * K) ^ 2) (max Nr Nw), ?_⟩
  intro M hM hfit N hN A hA hprem hrange n ℓ y htar i j k hjk
  obtain ⟨hn, hsqrt, -, -⟩ := target_size_bounds (by omega : 1 ≤ K)
    ((le_max_left _ _).trans hN) htar
  have hwidth := hNw M hM hfit N ((le_max_right Nr Nw).trans ((le_max_right _ _).trans hN))
    A hA hrange n hsqrt
  have hround : 16 * Real.sqrt m ≤ (n : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) := by
    rw [show 1 + (M.δ / 100 - 1 / 4) = (3 : ℝ) / 4 + M.δ / 100 by ring]
    nlinarith only [hwidth, Real.sqrt_nonneg (m : ℝ), Nat.cast_nonneg (α := ℝ) (wInt M K A n)]
  have hjk' : (wInt M K A n : ℝ) * ‖transversePoint (k - j)‖ ≤
      (n : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) / 8 := by
    rw [show 1 + (M.δ / 100 - 1 / 4) = (3 : ℝ) / 4 + M.δ / 100 by ring]
    linarith only [hjk]
  have hslope := rowPairSlope_norm_le (by omega : 1 ≤ n) (targetSlope ℓ y) ((i : ℤ) - 1) j k
    (targetSlope_norm_le_half hM hK (by omega) htar.1 htar.2.2.2) hjk' hround
  have hwpos := one_le_wInt (M := M) (K := K) hA (by omega : 1 ≤ n)
  have hpair := isCubePair_rows (M := M) (K := K) (A := A) (b := 1) (by omega : 1 ≤ n)
    hwpos (by simpa only [one_mul] using wInt_sub_one_le_W M K A n)
    (targetSlope ℓ y) ((i : ℤ) - 1) j k
  simp only [sub_add_cancel] at hpair
  have hnlo : 1 / (9 * (K : ℝ)) * N ≤ n := by
    have h := htar.2.1
    rw [htar.1, Nat.cast_mul] at h
    apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 9 * K by positivity)).mp
    field_simp
    nlinarith only [h]
  have hnN : n ≤ N := by
    have hnℓ : n ≤ ℓ := by rw [htar.1]; exact Nat.le_mul_of_pos_left n (by omega)
    exact hnℓ.trans htar.2.2.1
  have hl := hNr M hM hfit N ((le_max_left Nr Nw).trans ((le_max_right _ _).trans hN)) A hA hprem
    hrange n hnlo hnN _ _ _ hpair hslope
  have hR := hl.2 (((i : ℤ) - 1) * n) (fun u hu => hu.1)
  have hface : ((i : ℤ) - 1) * n + n = (i : ℤ) * n := by ring
  rw [hface] at hR
  have hR1 : ∀ ω : Config m, 1 ≤ locRadiusSlab ω (((i : ℤ) - 1) * n) ((i : ℤ) * n)
      (rowCube n (wInt M K A n) (targetSlope ℓ y) ((i : ℤ) - 1) j)
      (rowCube n (wInt M K A n) (targetSlope ℓ y) i k) (W M K A n) :=
    fun ω => by
      change (1 : ℝ≥0∞) ≤ 1 + _
      exact le_add_of_nonneg_right bot_le
  have hqp : q ≤ p := by
    dsimp only [p, q]
    have hsq : m + 1 ≤ (m + 1) ^ 2 := by nlinarith
    exact (Nat.mul_le_mul_right (m + 1) (by norm_num : 8 ≤ 128)).trans
      (Nat.mul_le_mul_left 128 hsq)
  change (∫⁻ ω, (ENNReal.ofReal Cd * (1 + locRadiusSlab ω (((i : ℤ) - 1) * n) ((i : ℤ) * n)
    (rowCube n (wInt M K A n) (targetSlope ℓ y) ((i : ℤ) - 1) j)
    (rowCube n (wInt M K A n) (targetSlope ℓ y) i k) (W M K A n))) ^ q ∂M.P) ≤ _
  exact lintegral_scaled_radius_pow_le (p := p) (q := q) hqp hR1 hCd hR

end CurvatureVariance.Paper.Contracts
