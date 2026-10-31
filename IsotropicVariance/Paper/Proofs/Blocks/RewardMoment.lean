/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Blocks
public import IsotropicVariance.Paper.Contracts.Localization
public import IsotropicVariance.Paper.Contracts.Profiles
import IsotropicVariance.Paper.Proofs.Blocks.Localization
import IsotropicVariance.Paper.Proofs.Blocks.Scales
import IsotropicVariance.Paper.Proofs.Localization.Scales
import IsotropicVariance.Paper.Proofs.Resampling.Coupling
import IsotropicVariance.Paper.Proofs.Responses.RewardAtScale

/-!
# Lemma `lem:blocks`, the first bound of equation `eq:rewardmoment`

`Responses.lintegral_reward_pow_le_of_isBlockCoupling` is the argument of the second paragraph of
the proof of Lemma `lem:blocks`, at one length, in the same order:

* the cells `[(i−1)n, in] × W_n (z + [0, 1)^{d−1})` cover the slab, and the term of a block in
  `Y_i(j, k)` is at most the sum over its cells that meet the tube
  (`Responses.tsum_blocks_le_tsum_cells`, after the text before Lemma `lem:blocks`, by which the
  term of `G` vanishes unless `G` meets `U_i(j, k)`:
  `IsBlockCoupling.ae_exists_cell_of_blockGain_ne_zero`);
* since `ω^G` has the law of `ω`, every moment of `Q_n⁻¹ sup |T^{(i), G} − T^{(i)}|` is bounded by
  equation `eq:profiles`, uniformly in `G`, `L`, `σ_G` (`Responses.eLpNorm_blockGain_div_le`,
  which uses only the two marginals);
* the cell of `z` meets the tube only if `dist(z, [j, k])` is at most a constant plus the radius,
  so Hölder's inequality and the bound `O_2(C)` of the radius give the Gaussian factor
  (`Responses.eLpNorm_indicator_sq_le_gaussian`);
* the sum over `z` is by Minkowski's inequality (`Responses.eLpNorm_cell_sum_le`).

The radius in that argument is `1 + W_n⁻¹ sup dist(x, [u, v])`, the quantity of Lemma
`lem:localization`, in place of `R_i(j, k)`. The two differ by a bounded amount
(`Modulus.radius_le`), which is the constant `C` of the paper.
-/

@[expose] public section

universe u

namespace IsotropicVariance.Paper.Proofs.Blocks

open Contracts

/-- **Lemma `lem:blocks`, the first bound of equation `eq:rewardmoment`**, from Proposition
`prop:profiles` and Lemma `lem:localization`. -/
theorem rewardMomentStatement_of (hP : ProfilesStatement.{u}) (hL : LocalizationStatement.{u}) :
    RewardMomentStatement.{u} := by
  intro m hm X hX b hb Cstar hC
  obtain ⟨Cl, hCl, Hl⟩ := hL m hm X hX b hb Cstar hC
  obtain ⟨Cp, hCp, Hp⟩ := hP m hm X hX b hb Cstar hC
  have hq : 1 ≤ 16 * (m + 1) := by omega
  have hCl' : 0 < 2 + Cl := by positivity
  refine ⟨Responses.rewardMomentConst m (16 * (m + 1)) (2 + Cl) Cp,
    Responses.rewardMomentConst_pos m hq hCl' hCp, fun K => ?_⟩
  by_cases hK : 10 ≤ K
  swap
  · exact ⟨0, fun A N _ hS => absurd hS.1 hK⟩
  have hK8 : (1 : ℝ) ≤ 8 * K := by exact_mod_cast (by omega : 1 ≤ 8 * K)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hc₁ : (0 : ℝ) < 1 / (8 * K) := by positivity
  have hc₁' : 1 / (8 * (K : ℝ)) ≤ 1 := (div_le_one (by linarith only [hK8])).mpr hK8
  obtain ⟨Nl, HNl⟩ := Hl (1 / (8 * K)) hc₁ hc₁' K
  obtain ⟨Np, HNp⟩ := Hp (1 / (8 * K)) hc₁ K
  refine ⟨max Nl (max Np (8 * (K : ℝ))),
    fun A N hN hS ℓ hℓ₁ hℓ₂ L hL σ o i _ j k hjk => ?_⟩
  have hNl : Nl ≤ N := (le_max_left _ _).trans hN
  have hNp : Np ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNK : 8 * (K : ℝ) ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hn₁, hn₄, hn, hQ, hW⟩ := scales_of_standing hS hℓ₁ hℓ₂
  have hnN : ℓ / K ≤ N := hn₄.trans (by linarith only [hS.2.2.1])
  have hn1 : 1 ≤ ℓ / K := by
    rw [le_div_iff₀ hKpos]
    linarith only [hNK, hℓ₁]
  have hW1 : 1 ≤ W K A (ℓ / K) := Localization.one_le_W (by omega) hS.2.1 hn1
  exact Responses.lintegral_reward_pow_le_of_isBlockCoupling hb hn.le hW1 hQ hCl' hCp hq hL o i j k
    hjk (HNp A N hNp hS _ hn₁ hnN _ (Profiles.gridPair_isAdmissible hn hW.le hjk)).2
    (isOs_one_add_gridPair X hn hW hCl (HNl A N hNl hS _ hn₁ hnN) i hjk)
    (new := fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 (i, z))
    fun z _ => X.isBlockCoupling_blockResampling _ _ L i z (σ.2 (i, z))

end IsotropicVariance.Paper.Proofs.Blocks
