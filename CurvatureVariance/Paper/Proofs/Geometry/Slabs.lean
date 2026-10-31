/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.SlabsTwo
public import CurvatureVariance.Paper.Proofs.Geometry.HitsMain

/-!
# Lemma `lem:slabs` (Restriction to slabs): two facts

`coneBound_mono`: the cone bound is monotone in its constant, and `exists_nat_goodEvent_small`: the
good events `𝒢_N(S) = GoodEvent μ A a (2N²) (max S 1)` can be taken with failure probability small
once `N` is large.
-/

@[expose] public section

open MeasureTheory InnerProductGeometry
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### Monotonicity in the constants -/

theorem coneBound_mono {M : Model m} {C C' S : ℝ} {N : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    {a : Pt m} (hS : 0 ≤ S) (hN : 1 ≤ N) (hCC' : C ≤ C')
    (h : ConeBound M C S N t a) : ConeBound M C' S N t a := by
  intro ha
  have ha' : C * S ^ 2 ≤ ‖a‖ := (mul_le_mul_of_nonneg_right hCC' (sq_nonneg S)).trans ha
  refine (h ha').trans (mul_le_mul_of_nonneg_right hCC' ?_)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  positivity

/-! ### The size of the failure probability -/

/-- For `N` large and `S ≥ log N`: `S ≥ 1`, the box condition of the union bound holds, and
`K |B|² e^{-cS²} ≤ e^{-cS²/2}` for the box `B = [−2N², 2N²]^d`. -/
theorem exists_nat_goodEvent_small {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : ℝ, Real.log N ≤ S →
      1 ≤ S ∧ Real.log (2 + 2 * ((m : ℝ) + 1) * ((2 * N ^ 2 : ℕ) : ℝ)) ≤ 3 * S ^ 2 ∧
        K * ((boxFinset (m := m) (2 * N ^ 2)).card : ℝ) ^ 2 * Real.exp (-(c * S ^ 2)) ≤
          Real.exp (-(c / 2 * S ^ 2)) := by
  set S₀ := 2 / c * (Real.log (K + 1) + 6 * ((m : ℝ) + 1)) with hS₀
  refine ⟨max (max 5 (4 * (m + 1) + 2)) ⌈Real.exp S₀⌉₊, fun N hN S hS => ?_⟩
  have hN5 : (5 : ℝ) ≤ N := by
    exact_mod_cast le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNm : (4 * ((m : ℝ) + 1) + 2) ≤ N := by
    exact_mod_cast le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNe' : ⌈Real.exp S₀⌉₊ ≤ N := le_trans (le_max_right _ _) hN
  have hNe : Real.exp S₀ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNe')
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : 1 ≤ Real.log N := one_le_log_of_three_le (by linarith)
  have hS1 : 1 ≤ S := hlogN.trans hS
  have hlogK : 0 ≤ Real.log (K + 1) := Real.log_nonneg (by linarith)
  have hS₀0 : 0 ≤ S₀ := by positivity
  have hSS₀ : S₀ ≤ S := by
    have : S₀ ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le hNpos]; exact hNe
    linarith
  refine ⟨hS1, ?_, ?_⟩
  · have hN3 : 2 + 2 * ((m : ℝ) + 1) * ((2 * N ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 3 := by
      push_cast
      have h1 : (4 * ((m : ℝ) + 1) + 2) * (N : ℝ) ^ 2 ≤ (N : ℝ) * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hNm (sq_nonneg _)
      have h2 : (2 : ℝ) ≤ 2 * (N : ℝ) ^ 2 := by nlinarith only [hN5]
      nlinarith only [h1, h2]
    calc Real.log (2 + 2 * ((m : ℝ) + 1) * ((2 * N ^ 2 : ℕ) : ℝ))
        ≤ Real.log ((N : ℝ) ^ 3) := Real.log_le_log (by positivity) hN3
      _ = 3 * Real.log N := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 3 * S ^ 2 := by nlinarith only [hS, hS1, hlogN]
  · -- `|B| = (4N² + 1)^d ≤ N^{3d}`
    have hcard : ((boxFinset (m := m) (2 * N ^ 2)).card : ℝ) ≤ ((N : ℝ) ^ 3) ^ (m + 1) := by
      rw [card_boxFinset]
      push_cast
      refine pow_le_pow_left₀ (by positivity) ?_ _
      nlinarith only [hN5]
    have hcard2 : ((boxFinset (m := m) (2 * N ^ 2)).card : ℝ) ^ 2 ≤
        Real.exp (6 * ((m : ℝ) + 1) * Real.log N) := by
      calc ((boxFinset (m := m) (2 * N ^ 2)).card : ℝ) ^ 2 ≤ (((N : ℝ) ^ 3) ^ (m + 1)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
        _ = Real.exp (6 * ((m : ℝ) + 1) * Real.log N) := by
            rw [← pow_mul, ← pow_mul, ← Real.exp_log hNpos, ← Real.exp_nat_mul,
              Real.exp_log hNpos]
            push_cast
            ring_nf
    have hkey : Real.log (K + 1) + 6 * ((m : ℝ) + 1) * Real.log N ≤ c / 2 * S ^ 2 := by
      have h1 : c / 2 * S ^ 2 ≥ (Real.log (K + 1) + 6 * ((m : ℝ) + 1)) * S := by
        have hEq : c / 2 * S₀ = Real.log (K + 1) + 6 * ((m : ℝ) + 1) := by
          rw [hS₀]; field_simp
        have hle := mul_le_mul_of_nonneg_left hSS₀
          (mul_nonneg (by positivity : (0 : ℝ) ≤ c / 2) (by linarith : (0 : ℝ) ≤ S))
        calc (Real.log (K + 1) + 6 * ((m : ℝ) + 1)) * S = c / 2 * S₀ * S := by rw [hEq]
          _ = c / 2 * S * S₀ := by ring
          _ ≤ c / 2 * S * S := hle
          _ = c / 2 * S ^ 2 := by ring
      have h2 : 6 * ((m : ℝ) + 1) * Real.log N ≤ 6 * ((m : ℝ) + 1) * S :=
        mul_le_mul_of_nonneg_left hS (by positivity)
      nlinarith only [h1, h2, hS1, hlogK]
    calc K * ((boxFinset (m := m) (2 * N ^ 2)).card : ℝ) ^ 2 * Real.exp (-(c * S ^ 2))
        ≤ (K + 1) * Real.exp (6 * ((m : ℝ) + 1) * Real.log N) * Real.exp (-(c * S ^ 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul (by linarith) hcard2 (by positivity) (by linarith)
      _ = Real.exp (Real.log (K + 1) + 6 * ((m : ℝ) + 1) * Real.log N - c * S ^ 2) := by
          rw [Real.exp_sub, Real.exp_add, Real.exp_log (by linarith), Real.exp_neg]
          ring
      _ ≤ Real.exp (-(c / 2 * S ^ 2)) := Real.exp_le_exp.2 (by linarith)

end CurvatureVariance.Paper.Proofs.Geometry
