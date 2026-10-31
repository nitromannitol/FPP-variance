/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Resampling

/-!
# Statements of Section `sec:gain`, part 1: equation `eq:blocksum` and Lemma `lem:blocks`

The setting at the start of Section `sec:gain` (modules `IsotropicVariance.Paper.Defs.Blocks` and
`IsotropicVariance.Paper.Defs.Resampling`): `ℓ = Kn ∈ [N/8, N]`, the slab minimum with `K` slabs of
width `n` and its points `x_i`, the radii `R_i(j, k)`, the blocks of transverse side
`L(nQ_n)^{1/2}` with an offset `a_i` per slab, and, for a choice of the `σ_G` (`X.BlockInfo`), the
joint law `X.blockResampling` of the noise `ω` (`Prod.fst`) and of the resamplings `ω^G`
(`fun p => p.2 (i, z)`). A function `Z_i(j, k)` evaluated at `x_{i−1}`, `x_i` is `Z_i` at the
indices `J` of the cubes that contain them (the convention before Lemma `lem:rowenergy`; `X.J`, the
floor, is the lexicographically greatest index). Lean slabs are 0-based: the paper's
`Z_i(x_{i−1}, x_i)`, `i ∈ {1, …, K}`, is `Z (i) (J i.castSucc) (J i.succ)`, `i : Fin K`.

* `BlockSumStatement`: equation `eq:blocksum`.
* `RadiusEnergyStatement`: equation `eq:radiusenergy`.
* `RewardMomentStatement`: the first bound of equation `eq:rewardmoment`.
* `BlockReplacementStatement`: the second bound of equation `eq:rewardmoment`.

By the conventions of Section `ssec:notation`, the constants depend only on `d` and the law of the
density, so they are chosen before `K`, `L`, the offsets and the `σ_G`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Contracts

/-- **Equation `eq:blocksum`**: for `ℓ = Kn ∈ [N/8, N]` with `N` large
depending on `K`, every `L ≥ 1`, every choice of the `σ_G` and all offsets `a_i`,
`Σ_G E[(F^G − F)²] ≤ 2 Q_n² E[Σ_{i=1}^K Y_i(x_{i−1}, x_i)]`, the sum over the blocks of all `K`
slabs, both sides in `[0, ∞]`.

The display is in the proof of Lemma `lem:blocks`, under "for `N` large". That phrase, as in
Lemma `lem:rowenergy`, uses `Q_s/s → 0`, which comes from equation `eq:regime`, so the statement
assumes `Standing`, as Lemma `lem:blocks` does. -/
def BlockSumStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∀ K : ℕ, ∃ N₀ : ℝ,
      ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ ℓ : ℝ, N / 8 ≤ ℓ → ℓ ≤ N →
        ∀ (L : ℕ), 1 ≤ L → ∀ (σ : X.BlockInfo (ℓ / K) (W K A (ℓ / K)) L)
          (o : Fin K → Fin m → Fin L),
          ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
              ∫⁻ p, ENNReal.ofReal ((X.F b K (ℓ / K) 0 (p.2 ((i : ℕ), (z : Fin m → ℤ))) -
                  X.F b K (ℓ / K) 0 p.1) ^ 2)
                ∂X.blockResampling (ℓ / K) (W K A (ℓ / K)) L σ.1 ≤
            ENNReal.ofReal (2 * Q K A (ℓ / K) ^ 2) *
              ∫⁻ p, ∑ i : Fin K, X.Y b (ℓ / K) (W K A (ℓ / K)) (Q K A (ℓ / K)) i
                  (X.J b K (ℓ / K) (W K A (ℓ / K)) 0 p.1 i.castSucc)
                  (X.J b K (ℓ / K) (W K A (ℓ / K)) 0 p.1 i.succ)
                  {z | IsBlockIndex L (o i) z} Prod.fst
                  (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 ((i : ℕ), z)) p
                ∂X.blockResampling (ℓ / K) (W K A (ℓ / K)) L σ.1

/-- **Lemma `lem:blocks`, equation `eq:radiusenergy`**:
`E Σ_{i=1}^K R_i(x_{i−1}, x_i)² ≤ CK` for every `ℓ = Kn ∈ [N/8, N]`, if `N` is large depending on
`K`. -/
def RadiusEnergyStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, ∃ N₀ : ℝ,
      ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ ℓ : ℝ, N / 8 ≤ ℓ → ℓ ≤ N →
        ∫⁻ ω, ENNReal.ofReal (∑ i : Fin K,
            X.R b (ℓ / K) (W K A (ℓ / K)) ω i
              (X.J b K (ℓ / K) (W K A (ℓ / K)) 0 ω i.castSucc)
              (X.J b K (ℓ / K) (W K A (ℓ / K)) 0 ω i.succ) ^ 2) ∂X.P ≤
          ENNReal.ofReal (C * K)

/-- **Lemma `lem:blocks`, first bound of equation `eq:rewardmoment`**: if
`N` is large depending on `K`, then for every `L ≥ 1`, every choice of the `σ_G`, every offset of
the slab `i` and every pair `j, k` with `(nQ_n)^{1/2}|k − j| ≤ n/2`,
`E[Y_i(j, k)^{16d}]^{1/(16d)} ≤ C(1 + |j − k|)`, written here for the moment itself. Only the offset
of the slab `i` enters `Y_i`. -/
def RewardMomentStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, ∃ N₀ : ℝ,
      ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ ℓ : ℝ, N / 8 ≤ ℓ → ℓ ≤ N →
        ∀ (L : ℕ), 1 ≤ L → ∀ (σ : X.BlockInfo (ℓ / K) (W K A (ℓ / K)) L)
          (o : Fin m → Fin L) (i : ℕ), i < K →
          ∀ j k : Fin m → ℤ, W K A (ℓ / K) * zNorm (k - j) ≤ ℓ / K / 2 →
            ∫⁻ p, X.Y b (ℓ / K) (W K A (ℓ / K)) (Q K A (ℓ / K)) i j k
                {z | IsBlockIndex L o z} Prod.fst
                (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 (i, z)) p ^ (16 * (m + 1))
                ∂X.blockResampling (ℓ / K) (W K A (ℓ / K)) L σ.1 ≤
              ENNReal.ofReal ((C * (1 + zNorm (j - k))) ^ (16 * (m + 1)))

/-- **Lemma `lem:blocks`, second bound of equation `eq:rewardmoment`**: if
`N` is large depending on `K`, then for every `L ≥ 1`, every choice of the `σ_G` and all offsets
`a_i`, `Σ_G E[(F^G − F)²] ≤ C K Q_n²`, the sum over the blocks of all `K` slabs, in `[0, ∞]`. -/
def BlockReplacementStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, ∃ N₀ : ℝ,
      ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ ℓ : ℝ, N / 8 ≤ ℓ → ℓ ≤ N →
        ∀ (L : ℕ), 1 ≤ L → ∀ (σ : X.BlockInfo (ℓ / K) (W K A (ℓ / K)) L)
          (o : Fin K → Fin m → Fin L),
          ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
              ∫⁻ p, ENNReal.ofReal ((X.F b K (ℓ / K) 0 (p.2 ((i : ℕ), (z : Fin m → ℤ))) -
                  X.F b K (ℓ / K) 0 p.1) ^ 2)
                ∂X.blockResampling (ℓ / K) (W K A (ℓ / K)) L σ.1 ≤
            ENNReal.ofReal (C * K * Q K A (ℓ / K) ^ 2)

end IsotropicVariance.Paper.Contracts
