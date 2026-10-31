/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Blocks
import IsotropicVariance.Paper.Proofs.Blocks.Scales
import IsotropicVariance.Paper.Proofs.Profiles.Asymptotics
import IsotropicVariance.Paper.Proofs.Resampling.Coupling
import IsotropicVariance.Paper.Proofs.Responses.FamilyResponse

/-!
# Equation `eq:blocksum`

In the proof of Lemma `lem:blocks`, for `N` large, evaluating `F^G` at the points `x_i` gives
`Σ_G (F^G − F)₊² ≤ Q_n² Σ_i Y_i(x_{i−1}, x_i)`, and by exchangeability `(F − F^G)₊` has the law of
`(F^G − F)₊`, so `Σ_G E[(F^G − F)²] ≤ 2 Q_n² E[Σ_i Y_i(x_{i−1}, x_i)]`.

`Responses.ae_tsum_pos_F_sub_sq_le_reward_of_isBlockCoupling` is the first step on the blocks of one
slab: a resampling in the slab `i` changes no other slab
(`Responses.IsBlockCoupling.ae_other_slabTime_eq`), so `F^G − F` is at most the change of `T^{(i)}`
at the old points `x_{i−1}`, `x_i` (`Responses.pos_F_sub_le_blockGain`), which lie in the cubes of
the indices `J`, at a pair retained by `Y_i` (`Profiles.J_step`, the use of `N` large).
`Responses.tsum_lintegral_F_sub_sq_le_selected_reward_of_isBlockCoupling` adds exchangeability
(`NoiseModel.exchangeable_resamplingLaw`, through `Setting.isBlockCoupling_blockResampling`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Blocks

open Contracts

/-- The sum of the integrals is at most the integral of the sum, with no measurability. -/
theorem sum_lintegral_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (s : Finset ι)
    (f : ι → Ω → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ ω, f i ω ∂μ ≤ ∫⁻ ω, ∑ i ∈ s, f i ω ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- **Equation `eq:blocksum`** (proof of Lemma `lem:blocks`). -/
theorem blockSumStatement_holds : BlockSumStatement.{u} := by
  intro m hm X hX b hb Cstar hC K
  by_cases hK : 10 ≤ K
  swap
  · exact ⟨0, fun A N _ hS => absurd hS.1 hK⟩
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hc₁ : (0 : ℝ) < 1 / (8 * K) := by positivity
  have hε : (0 : ℝ) < 1 / (4 * (Real.sqrt m + 1)) := by positivity
  obtain ⟨NW, HNW⟩ := Profiles.exists_W_le Cstar (1 / (8 * K)) _ hc₁ hε
  refine ⟨NW, fun A N hN hS ℓ hℓ₁ hℓ₂ L hL σ o => ?_⟩
  obtain ⟨hn₁, hn₄, hn, hQ, hW⟩ := scales_of_standing hS hℓ₁ hℓ₂
  have hnN : ℓ / K ≤ N := hn₄.trans (by linarith only [hS.2.2.1])
  have hWm : 4 * Real.sqrt m * W K A (ℓ / K) ≤ ℓ / K := four_sqrt_mul_le hn
    (HNW K hK A N (by linarith only [hS.2.1]) hN hS.2.2.2.2 (ℓ / K) hn₁ hnN)
  have hslab : ∀ i : Fin K,
      ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
          ∫⁻ p, ENNReal.ofReal ((X.F b K (ℓ / K) 0 (p.2 ((i : ℕ), (z : Fin m → ℤ))) -
              X.F b K (ℓ / K) 0 p.1) ^ 2)
            ∂X.blockResampling (ℓ / K) (W K A (ℓ / K)) L σ.1 ≤
        (2 * ENNReal.ofReal (Q K A (ℓ / K) ^ 2)) *
          ∫⁻ p, X.Y b (ℓ / K) (W K A (ℓ / K)) (Q K A (ℓ / K)) i
              (X.J b K (ℓ / K) (W K A (ℓ / K)) 0 p.1 i.castSucc)
              (X.J b K (ℓ / K) (W K A (ℓ / K)) 0 p.1 i.succ)
              {z | IsBlockIndex L (o i) z} Prod.fst
              (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 ((i : ℕ), z)) p
            ∂X.blockResampling (ℓ / K) (W K A (ℓ / K)) L σ.1 := fun i =>
    Responses.tsum_lintegral_F_sub_sq_le_selected_reward_of_isBlockCoupling hb hn hW hQ hWm hL
      (o i) i (new := fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 ((i : ℕ), z))
      fun z _ => X.isBlockCoupling_blockResampling _ _ L i z (σ.2 ((i : ℕ), z))
  have h2 : ENNReal.ofReal (2 * Q K A (ℓ / K) ^ 2) = 2 * ENNReal.ofReal (Q K A (ℓ / K) ^ 2) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [h2]
  refine (Finset.sum_le_sum fun i _ => hslab i).trans ?_
  rw [← Finset.mul_sum]
  gcongr
  exact sum_lintegral_le _ _

end IsotropicVariance.Paper.Proofs.Blocks
