/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Contracts.Moments
import CurvatureVariance.Paper.Proofs.Responses.BlocksChain
import CurvatureVariance.Paper.Proofs.Responses.RadiusArrays
import CurvatureVariance.Paper.Proofs.Responses.RawRadii
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:blocks`, equation `eq:radiusenergy`

Lemma `lem:blocks` and its proof, which is that of [AB26, Lemma 6.1]. The moment
`E[R_i(j,k)^{128d²}] ≤ C` of Lemma `lem:localization` gives `E[R_i(j,k)^{8d}] ≤ D` on the retained
pairs (`raw_radius_moments`), and `R_i(j,k) = 0` off them. The arrays `R_i(j,k)²` are
independent over the slabs (`Responses.iIndepFun_radiusArrays`), and `E[(R²)^{4d}] ≤ D ≤ λ^{4d}`
for `λ = D + 1`. Equation `eq:chainsum` (`lintegral_sup_sum_le_of_chainSum`) applied to
`R_i(j,k)²` with `π = id` gives `E sup ∑ R_i(x_{i−1}, x_i)² ≤ λ C K`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper.Responses

/-- **Lemma `lem:blocks`, equation `eq:radiusenergy`**, from Lemma `lem:localization`, equation
`eq:chainsum` and equation `eq:scales`. -/
theorem radiusEnergy {m : ℕ} (hloc : LocalizationStatement m)
    (hchain : ChainSumStatement.{0} m) (hscales : ScalesStatement m) : RadiusEnergyStatement m := by
  intro bd hbd Cstar Cd hCd
  obtain ⟨D, hD, hRadius⟩ := raw_radius_moments hscales hloc bd hbd Cstar Cd hCd
  obtain ⟨C₀, hC₀, hCS⟩ := lintegral_sup_sum_le_of_chainSum hchain bd hbd Cstar
  refine ⟨(D + 1) * C₀, by positivity, fun K hK => ?_⟩
  obtain ⟨NR, hNR⟩ := hRadius K hK
  obtain ⟨NC, hNC⟩ := hCS K hK
  refine ⟨max NR NC, fun M hM hfit N hN A hA hprem hrange n ℓ y htar => ?_⟩
  let : IsProbabilityMeasure M.P := hM.probP
  have hNR' : NR ≤ N := (le_max_left _ _).trans hN
  have hNC' : NC ≤ N := (le_max_right _ _).trans hN
  set p : ℕ := 4 * (m + 1) with hp
  have hRm : ∀ (i : ℕ) (j k : Fin m → ℤ),
      (∫⁻ ω, radiusArray M K A Cd ω n (targetSlope ℓ y) (i + 1) j k ^ (2 * p) ∂M.P) ≤
        ENNReal.ofReal D := by
    intro i j k
    by_cases hret : IsRetainedPair M n (wInt M K A n) j k
    · simp only [radiusArray, hret, ite_true]
      simpa only [p, show 2 * (4 * (m + 1)) = 8 * (m + 1) by omega] using
        hNR M hM hfit N hNR' A hA hprem hrange n ℓ y htar (i + 1) j k hret
    · simp only [radiusArray, hret, ite_false, zero_pow (show 2 * p ≠ 0 by omega), lintegral_zero]
      exact bot_le
  have hlam : 0 < D + 1 := by positivity
  have hDle : D ≤ (D + 1) ^ p := (by linarith only : D ≤ D + 1).trans
    (le_self_pow₀ (by linarith only [hD]) (by omega))
  have hmom : ∀ (i : Fin K) (j k : Fin m → ℤ), ∫⁻ ω,
      (radiusArray M K A Cd ω n (targetSlope ℓ y) ((i : ℕ) + 1) j k ^ 2 -
        ENNReal.ofReal ((D + 1) * ‖transversePoint (j - k)‖ ^ 2)) ^ p ∂M.P ≤
      ENNReal.ofReal ((D + 1) ^ p) := by
    intro i j k
    calc _ ≤ ∫⁻ ω, (radiusArray M K A Cd ω n (targetSlope ℓ y) ((i : ℕ) + 1) j k ^ 2) ^ p ∂M.P :=
          lintegral_mono fun ω => pow_le_pow_left₀ bot_le tsub_le_self _
      _ = ∫⁻ ω, radiusArray M K A Cd ω n (targetSlope ℓ y) ((i : ℕ) + 1) j k ^ (2 * p) ∂M.P := by
          simp only [← pow_mul]
      _ ≤ ENNReal.ofReal D := hRm i j k
      _ ≤ _ := ENNReal.ofReal_le_ofReal hDle
  have hmain := hNC M hM hfit N hNC' A hA hprem hrange n ℓ y htar (Config m) M.P id
    (MeasurePreserving.id M.P) (D + 1) hlam
    (fun (i : Fin K) ω j k => radiusArray M K A Cd ω n (targetSlope ℓ y) ((i : ℕ) + 1) j k ^ 2)
    (fun i j k => (measurable_radiusArray M K A Cd n (targetSlope ℓ y) ((i : ℕ) + 1) j k).pow_const 2)
    (iIndepFun_radiusArrays hM K n A Cd (targetSlope ℓ y)) hmom
  refine hmain.trans (le_of_eq ?_)
  congr 1
  ring

end CurvatureVariance.Paper.Contracts
