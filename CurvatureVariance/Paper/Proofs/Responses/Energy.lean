/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Infra.Os.Moments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The first occupation bound

Taking expectations in equation `eq:rowenergy` gives `E Σ_i |J_i − J_{i−1}|² ≤ C K`, which the
proof of Lemma `lem:fewtranslates` uses. The
bound holds for the supremum over every minimizing tuple, with no measurable choice of a minimizer.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

/-- Integration of an exponential error bounds a supremum of nonnegative energies. -/
theorem lintegral_iSup_energy_le {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Ω → ι → ℝ} {Admissible : Ω → ι → Prop}
    {X : Ω → ℝ} {c C Q : ℝ} {K : ℕ} (hc : 0 < c) (hC : 0 < C) (hQ : 0 < Q)
    (hK : 1 ≤ K) (hX : CurvatureVariance.IsOs P 1 (C * Q) X)
    (hb : ∀ᵐ ω ∂P, ∀ i, Admissible ω i → c * Q * E ω i ≤ C * K * Q + X ω) :
    (∫⁻ ω, ⨆ (i : ι) (_ : Admissible ω i), ENNReal.ofReal (E ω i) ∂P) ≤
      ENNReal.ofReal ((5 * C / c) * K) := by
  have hCX : 0 < C * Q := mul_pos hC hQ
  have hmax := hX.lintegral_pos_rpow_le (by norm_num : (0 : ℝ) < 1) hCX
    (by norm_num : (0 : ℝ) ≤ 1)
  norm_num only [Real.rpow_one, div_one, Nat.ceil_one, Nat.factorial_one] at hmax
  have hdom : (∫⁻ ω, ⨆ (i : ι) (_ : Admissible ω i), ENNReal.ofReal (E ω i) ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal ((C / c) * K) +
        (ENNReal.ofReal (c * Q))⁻¹ * ENNReal.ofReal (max (X ω) 0) ∂P := by
    apply lintegral_mono_ae
    filter_upwards [hb] with ω hω
    refine iSup_le fun i => iSup_le fun hi => ?_
    have hE : E ω i ≤ (C / c) * K + (c * Q)⁻¹ * max (X ω) 0 := by
      have h := hω i hi
      have hx := le_max_left (X ω) 0
      have heq : c * Q * ((C / c) * K + (c * Q)⁻¹ * max (X ω) 0) =
          C * K * Q + max (X ω) 0 := by field_simp [hc.ne', hQ.ne']
      have hl : c * Q * E ω i ≤ c * Q * ((C / c) * K + (c * Q)⁻¹ * max (X ω) 0) := by
        rw [heq]
        linarith only [h, hx]
      exact (mul_le_mul_iff_right₀ (mul_pos hc hQ)).mp (by simpa only [mul_comm] using hl)
    have h1 := ENNReal.ofReal_le_ofReal hE
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (c * Q)⁻¹),
      ENNReal.ofReal_inv_of_pos (mul_pos hc hQ)] at h1
    exact h1
  calc
    _ ≤ _ := hdom
    _ = ENNReal.ofReal ((C / c) * K) +
        (ENNReal.ofReal (c * Q))⁻¹ * (∫⁻ ω, ENNReal.ofReal (max (X ω) 0) ∂P) := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul'' _
        ((hX.1.max aemeasurable_const).ennreal_ofReal), lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal ((C / c) * K) + (ENNReal.ofReal (c * Q))⁻¹ *
        ENNReal.ofReal (4 * (C * Q)) :=
      add_le_add le_rfl (mul_le_mul' le_rfl hmax)
    _ ≤ _ := by
      rw [← ENNReal.ofReal_inv_of_pos (mul_pos hc hQ),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (c * Q)⁻¹),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have heq : (C / c) * K + (c * Q)⁻¹ * (4 * (C * Q)) =
          (C / c) * ((K : ℝ) + 4) := by field_simp [hc.ne', hQ.ne']
      rw [heq]
      have hratio : 0 ≤ C / c := (div_pos hC hc).le
      calc
        _ ≤ (C / c) * (5 * K) := mul_le_mul_of_nonneg_left (by linarith only [hK']) hratio
        _ = _ := by ring

end CurvatureVariance.Paper.Responses

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper.Responses

/-- `E Σ_i |J_i − J_{i−1}|² ≤ C K` follows directly from equation `eq:rowenergy`. -/
theorem response_energy_of {m : ℕ} (h : ExpArrayStatement m) :
    ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
    ∀ M : Model m, M.Standing → M.Fits bd → ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
    Premise M K A N → RangeA M K A N Cstar →
    ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
      (∫⁻ ω, ⨆ (Y : Fin (K + 1) → Fin m → ℤ)
        (_ : IsMinTuple M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y),
        ENNReal.ofReal (∑ i : Fin K, indexJumpSq n (wInt M K A n) (targetSlope ℓ y) Y i) ∂M.P ≤
        ENNReal.ofReal (C * K)) := by
  intro bd hbd Cstar
  obtain ⟨c, C, hc, hC, harray⟩ := h bd hbd Cstar
  refine ⟨5 * C / c, by positivity, ?_⟩
  intro K hK
  obtain ⟨Nbase, hbase⟩ := harray K hK
  refine ⟨max Nbase ((9 * K) ^ 2), ?_⟩
  intro M hM hfit N hN A hA hprem hrange n ℓ y htar
  let : IsProbabilityMeasure M.P := hM.probP
  obtain ⟨hn, hsqrt, -, -⟩ := target_size_bounds (by omega : 1 ≤ K)
    ((le_max_right _ _).trans hN) htar
  have hℓ3 : ((K * n : ℕ) : ℝ) ≤ 3 * N := by
    have hℓN : (ℓ : ℝ) ≤ N := by exact_mod_cast htar.2.2.1
    rw [← htar.1]
    linarith only [hℓN, Nat.cast_nonneg (α := ℝ) N]
  have hy : ‖transversePoint y - ((K * n : ℕ) : ℝ) • M.t₀‖ ≤ 2 * ((K * n : ℕ) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) := by
    rw [← htar.1, show 1 + (M.δ / 100 - 1 / 4) = (3 : ℝ) / 4 + M.δ / 100 by ring]
    exact htar.2.2.2.trans (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg ℓ) _) (by norm_num))
  obtain ⟨X, hX, hbound⟩ := hbase M hM hfit N ((le_max_left _ _).trans hN) A hA hprem hrange
    K n (by omega) hsqrt hℓ3 y hy
  rw [← htar.1] at hbound
  have hQ : 0 < Q M K A n := mul_pos (lt_of_lt_of_le zero_lt_one hA)
    (Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)) _)
  apply lintegral_iSup_energy_le hc hC hQ (by omega : 1 ≤ K) hX
  filter_upwards [hbound] with ω hω
  intro Y hY
  have hb := hω Y hY
  linarith only [hb, abs_nonneg ((slabMin M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y)).toReal -
    M.μ.1 (point ((ℓ : ℤ), y)))]

end CurvatureVariance.Paper.Contracts
