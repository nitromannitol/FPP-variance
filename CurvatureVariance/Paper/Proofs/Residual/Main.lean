/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Residual.First
public import CurvatureVariance.Paper.Proofs.Residual.Second
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Paper.Proofs.Responses.WidthBridge

/-!
# Lemma `lem:residual`

`residualStatement_of`: both bounds of equation `eq:residual` of Lemma `lem:residual`, by the proof
of [AB26, Lemma 6.3] with the changes of the proof of Lemma `lem:residual`, from equations
`eq:rewardmoment`, `eq:blocksum` and `eq:chainsum`, Lemma `lem:localization` and the tube property.
The first bound is `Residual.First`, and the second is `Residual.Second`, with the first bound on
its right side. The model is the continuum's `IsotropicVariance.Paper.Proofs.Residual.Main`.

The premise `ScalesStatement` of the implication is not used: the slope of a retained pair, in
`Residual.Near`, needs only that `n` is large.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Proofs.Residual

open CurvatureVariance.Paper CurvatureVariance.Paper.Gain CurvatureVariance.Paper.Contracts

variable {m : ℕ}

/-- **Lemma `lem:residual`**, equation `eq:residual`. -/
theorem residualStatement_of (hRM : RewardMomentStatement.{0} m) (hS : BlockSumStatement.{0} m)
    (hC : ChainSumStatement.{0} m) (hloc : LocalizationStatement m)
    (_hscales : ScalesStatement m) (htube : TubeStatement m) : ResidualStatement m := by
  intro bd hbd Cstar α ε _ hε
  obtain ⟨ψ', hψ, h⟩ := exists_residual_modulus hRM hS hC hloc htube bd hbd Cstar α hε
  refine ⟨ψ', hψ, fun K hK L hL => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h L hL K hK
  refine ⟨max ((9 * K) ^ 2) N₀, ?_⟩
  intro M hM hfit N hN A hA hprem hrange n ℓ y htar P hP lam hlam
  have h₁ := hN₀ M hM hfit N ((le_max_right _ _).trans hN) A hA hprem hrange n ℓ y htar P hP lam
    hlam
  obtain ⟨hn, -, -, -⟩ := Responses.target_size_bounds (by omega : 1 ≤ K)
    ((le_max_left _ _).trans hN) htar
  have hw := Responses.one_le_wInt (M := M) (K := K) hA (by omega : 1 ≤ n)
  refine ⟨h₁, (offsetAverage_mono fun σ => ?_).trans h₁⟩
  exact (meanConditionalVariance_averagedMin_le hM (by omega) (by omega) hn hw hlam
    fun i k => offsetOf_mem (by omega) σ i k).trans
      (ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' one_le_two))

end CurvatureVariance.Paper.Proofs.Residual
