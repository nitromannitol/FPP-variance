/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import Mathlib.Tactic.Positivity

/-!
# Equation `eq:chainsum` applied to a multiple of an array, at a target

The use of equation `eq:chainsum` (as [AB26, (4.7)]) in the proofs of equations `eq:radiusenergy`
and `eq:rewardmoment` (the proof of Lemma `lem:blocks`): at a target
`(ℓ, y)`, `ℓ = Kn`, for arrays `T_i` in `[0, ∞]`, independent over the slabs, on a probability
space with a measure-preserving map `π` to the weights, and with
`E[(T_i(j,k) − λ|j−k|²)₊^{4d}] ≤ λ^{4d}` for all `i, j, k`,
`E sup_Y ∑_i T_i(J_{i−1}, J_i) ≤ λ C K`, the supremum over the minimizing tuples `Y` of `π ω`.
The arrays of equation `eq:chainsum` are `T_i/λ`. This is the continuum's
`IsotropicVariance.Paper.Proofs.Profiles.lintegral_sum_le_of_chainSum`, adapted: the set `D` of
pairs is all pairs, and the bound is the supremum over the minimizing tuples.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- **Equation `eq:chainsum` for the arrays `T_i/λ`, at a target.** -/
theorem lintegral_sup_sum_le_of_chainSum (hC : ChainSumStatement.{0} m) :
    ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
    ∀ M : Model m, M.Standing → M.Fits bd → ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
    Premise M K A N → RangeA M K A N Cstar →
    ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
    ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
      (π : Ω → Config m), MeasurePreserving π Pr M.P → ∀ lam : ℝ, 0 < lam →
    ∀ T : Fin K → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞,
      (∀ i j k, Measurable fun ω => T i ω j k) → iIndepFun T Pr →
      (∀ i j k, ∫⁻ ω, (T i ω j k - ENNReal.ofReal (lam * ‖transversePoint (j - k)‖ ^ 2)) ^
        (4 * (m + 1)) ∂Pr ≤ ENNReal.ofReal (lam ^ (4 * (m + 1)))) →
      ∫⁻ ω, ⨆ (Y : Fin (K + 1) → Fin m → ℤ)
          (_ : IsMinTuple M (π ω) n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y),
          ∑ i : Fin K, T i ω (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.castSucc)
            (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.succ) ∂Pr ≤
        ENNReal.ofReal (lam * (C * K)) := by
  intro bd hbd Cstar
  obtain ⟨C, hCpos, H⟩ := hC bd hbd Cstar
  refine ⟨C, hCpos, fun K hK => ?_⟩
  obtain ⟨N₀, hN₀⟩ := H K hK
  refine ⟨max N₀ ((9 * K) ^ 2), fun M hM hfit N hN A hA hprem hrange n ℓ y htar Ω _ Pr _ π hπ
    lam hlam T hTm hind hmom => ?_⟩
  have hN₀' : N₀ ≤ N := (le_max_left _ _).trans hN
  obtain ⟨hn, hsqrt, hnℓ, hℓ1⟩ := target_size_bounds (by omega : 1 ≤ K)
    ((le_max_right _ _).trans hN) htar
  obtain ⟨hℓ, hlow, hup, hy⟩ := htar
  subst hℓ
  have hMsN : (((K * n : ℕ)) : ℝ) ≤ 3 * N := by
    have : (((K * n : ℕ)) : ℝ) ≤ N := by exact_mod_cast hup
    linarith only [this, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hz : ‖transversePoint y - (((K * n : ℕ)) : ℝ) • M.t₀‖ ≤
      2 * (((K * n : ℕ)) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) := by
    have e : (1 : ℝ) + (M.δ / 100 - 1 / 4) = 3 / 4 + M.δ / 100 := by ring
    rw [e]
    have h0 : 0 ≤ (((K * n : ℕ)) : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hy' : ‖transversePoint y - (((K * n : ℕ)) : ℝ) • M.t₀‖ ≤
        (((K * n : ℕ)) : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := hy
    linarith only [hy', h0]
  have hlam1 : ENNReal.ofReal lam⁻¹ * ENNReal.ofReal lam = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hlam.le), inv_mul_cancel₀ hlam.ne', ENNReal.ofReal_one]
  have hlam2 : ENNReal.ofReal lam * ENNReal.ofReal lam⁻¹ = 1 := by rw [mul_comm, hlam1]
  set p := 4 * (m + 1) with hp
  have hp0 : p ≠ 0 := by omega
  set Z : Fin K → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ := fun i ω j k =>
    ENNReal.ofReal lam⁻¹ * T i ω j k with hZ
  have hZm : ∀ i j k, Measurable fun ω => Z i ω j k := fun i j k =>
    (hTm i j k).const_mul (ENNReal.ofReal lam⁻¹)
  have hZind : iIndepFun Z Pr := by
    let g : Fin K → ((Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞) → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ :=
      fun _ f j k => ENNReal.ofReal lam⁻¹ * f j k
    have hg : ∀ i, Measurable (g i) := fun _ =>
      measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun k => by
        have hev : Measurable fun f : (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ => f j k :=
          (measurable_pi_apply k).comp (measurable_pi_apply j)
        exact hev.const_mul _
    exact hind.comp g hg
  have hZmom : ∀ i j k, ∫⁻ ω, (Z i ω j k - ENNReal.ofReal (‖transversePoint (j - k)‖ ^ 2)) ^ p
      ∂Pr ≤ 1 := by
    intro i j k
    have hpt : ∀ ω, (Z i ω j k - ENNReal.ofReal (‖transversePoint (j - k)‖ ^ 2)) ^ p =
        ENNReal.ofReal lam⁻¹ ^ p *
          (T i ω j k - ENNReal.ofReal (lam * ‖transversePoint (j - k)‖ ^ 2)) ^ p := fun ω => by
      have e : ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (lam * ‖transversePoint (j - k)‖ ^ 2) =
          ENNReal.ofReal (‖transversePoint (j - k)‖ ^ 2) := by
        rw [ENNReal.ofReal_mul hlam.le, ← mul_assoc, hlam1, one_mul]
      rw [← mul_pow, ENNReal.mul_sub fun _ _ => ENNReal.ofReal_ne_top, e]
    simp only [hpt]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    calc ENNReal.ofReal lam⁻¹ ^ p * ∫⁻ ω,
          (T i ω j k - ENNReal.ofReal (lam * ‖transversePoint (j - k)‖ ^ 2)) ^ p ∂Pr
        ≤ ENNReal.ofReal lam⁻¹ ^ p * ENNReal.ofReal (lam ^ p) := by gcongr; exact hmom i j k
      _ = 1 := by rw [ENNReal.ofReal_pow hlam.le, ← mul_pow, hlam1, one_pow]
  have H' := hN₀ M hM hfit N hN₀' A hA hprem hrange K n (by omega) hsqrt hMsN y hz Ω Pr π hπ Z hZm
    hZind hZmom
  have hsum : ∀ ω (Y : Fin (K + 1) → Fin m → ℤ),
      ∑ i : Fin K, T i ω (tupleIndex n (wInt M K A n) (targetSlope (K * n) y) Y i.castSucc)
        (tupleIndex n (wInt M K A n) (targetSlope (K * n) y) Y i.succ) =
      ENNReal.ofReal lam * ∑ i : Fin K,
        Z i ω (tupleIndex n (wInt M K A n) (targetSlope (K * n) y) Y i.castSucc)
          (tupleIndex n (wInt M K A n) (targetSlope (K * n) y) Y i.succ) := fun ω Y => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hZ]
    rw [← mul_assoc, hlam2, one_mul]
  have hsup : ∀ ω, (⨆ (Y : Fin (K + 1) → Fin m → ℤ)
        (_ : IsMinTuple M (π ω) n K (targetSlope (K * n) y) 0 (((K * n : ℕ) : ℤ), y) Y),
        ∑ i : Fin K, T i ω (tupleIndex n (wInt M K A n) (targetSlope (K * n) y) Y i.castSucc)
          (tupleIndex n (wInt M K A n) (targetSlope (K * n) y) Y i.succ)) =
      ENNReal.ofReal lam * ⨆ (Y : Fin (K + 1) → Fin m → ℤ)
        (_ : IsMinTuple M (π ω) n K (targetSlope (K * n) y) 0 (((K * n : ℕ) : ℤ), y) Y),
        ∑ i : Fin K, Z i ω (tupleIndex n (wInt M K A n) (targetSlope (K * n) y) Y i.castSucc)
          (tupleIndex n (wInt M K A n) (targetSlope (K * n) y) Y i.succ) := fun ω => by
    rw [ENNReal.mul_iSup]
    refine iSup_congr fun Y => ?_
    rw [ENNReal.mul_iSup]
    exact iSup_congr fun _ => hsum ω Y
  simp only [hsup]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hlam.le]
  gcongr

end CurvatureVariance.Paper.Contracts
