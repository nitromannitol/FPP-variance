/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Residual.First
public import IsotropicVariance.Paper.Proofs.Residual.Second
import IsotropicVariance.Paper.Proofs.Blocks.Scales

/-!
# Lemma `lem:residual`

`residualStatement_of`: equation `eq:residual` and the bound of the mean conditional variance of
`F̄` (Lemma `lem:residual` and its proof), from equation `eq:rewardmoment`, equation `eq:blocksum`,
equation `eq:chainsum` and Lemma `lem:localization`.
-/

@[expose] public section

universe u

namespace IsotropicVariance.Paper.Proofs.Residual

open Contracts

/-- **Lemma `lem:residual`**. -/
theorem residualStatement_of (hM : RewardMomentStatement.{u}) (hS : BlockSumStatement.{u})
    (hC : ChainSumStatement.{u}) (hL : LocalizationStatement.{u}) : ResidualStatement.{u} := by
  intro m hm X hX b hb Cstar hCstar
  obtain ⟨G, hG, H⟩ := exists_residual_modulus hS hM hC hL hm X hX hb hCstar
  refine ⟨G, hG, fun K hK L hL' ε hε => ?_⟩
  obtain ⟨N₀, hN₀⟩ := H ε hε L hL' K hK
  refine ⟨N₀, fun A N hN hS' ℓ hℓ₁ hℓ₂ Λ hdet hcov hprof => ?_⟩
  have h₁ := hN₀ A N hN hS' ℓ hℓ₁ hℓ₂ Λ hdet hprof
  obtain ⟨-, -, hn, -, hW⟩ := Blocks.scales_of_standing hS' hℓ₁ hℓ₂
  exact ⟨h₁, (mul_le_mul' le_rfl (Finset.sum_le_sum fun o _ =>
    (lintegral_sub_condExp_averagedMin_le hm X hb hn hW (by omega) (by omega) hdet hcov o).trans
      (mul_le_of_le_one_left bot_le (by norm_num)))).trans h₁⟩

end IsotropicVariance.Paper.Proofs.Residual
