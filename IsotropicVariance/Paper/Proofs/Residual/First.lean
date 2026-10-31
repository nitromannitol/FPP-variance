/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Blocks
public import IsotropicVariance.Paper.Contracts.Gain
public import IsotropicVariance.Paper.Contracts.Localization
public import IsotropicVariance.Paper.Contracts.Profiles
public import IsotropicVariance.Paper.Proofs.Profiles.ChainSum
public import IsotropicVariance.Paper.Proofs.Residual.Family
import IsotropicVariance.Paper.Proofs.Blocks.BlockReplacement
import IsotropicVariance.Paper.Proofs.Blocks.Localization
import IsotropicVariance.Paper.Proofs.Blocks.Scales
import IsotropicVariance.Paper.Proofs.LabelResidual.Coarse
import IsotropicVariance.Paper.Proofs.LabelResidual.SelectedReward
import IsotropicVariance.Paper.Proofs.LabelResidual.UniformModulus
import IsotropicVariance.Paper.Proofs.Localization.Scales
import IsotropicVariance.Paper.Proofs.Profiles.Asymptotics
import IsotropicVariance.Paper.Proofs.Responses.SelectedMoments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Lemma `lem:residual`: equation `eq:residual`

The proof of the first bound of equation `eq:residual`, on the concrete resampling with `σ_G = X_G`,
the `X_G` of the paper. Let `Y_i(j, k)` be defined with this resampling, the offsets independent of
the rest and included in the expectations. For `η ∈ (0, 1]` and `L` large depending on `η`,
`E[(Y_i(j, k) − η|j − k|²)₊^{4d}]^{1/(4d)} ≤ η`, by equation `eq:rewardmoment` at large `|j − k|`,
and at bounded `|j − k|` by the event `E`, equation `eq:labelprofile` and Hölder's inequality. These
steps are `LabelResidual.exists_small_penalized_rewards`, whose arrays are the conditional arrays
`Y_i` given the noise in their slab, averaged over the offsets. Equation `eq:chainsum`, applied to
the arrays `Y_i/η`, then gives `E[Σ_i Y_i(x_{i−1}, x_i)] ≤ CηK`, and equation `eq:blocksum` gives
equation `eq:residual`.

* `residualEnergy`: `Σ_G E[(F^G − F)²]`, at given offsets.
* `ResidualBound`: equation `eq:residual` with a constant `c`, at a given `ε` and `L`.
* `exists_small_residualBound`: the bound with a small `c`, for `ε` small and `L` large.
* `exists_coarse_residualBound`: the bound with a constant `c`, for all `ε` and `L`, from the second
  bound of equation `eq:rewardmoment`. This one is not in the paper, which takes `L` large; the
  statement names a value of `G(ε, L)` for every `ε` and `L`.
* `exists_residual_modulus`: one `G(ε, L)`.

The hypotheses are `BlockSumStatement`, `RewardMomentStatement`, `ChainSumStatement` and
`LocalizationStatement`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Residual

open Contracts Gain

/-- The left side of equation `eq:residual` at the offsets `o`: `Σ_G E[(F^G − F)²]`, for the
resampling with `σ_G = X_G` (Lemma `lem:residual`). -/
noncomputable def residualEnergy {m : ℕ} (X : Setting.{u} m) (b : ℝ) (K : ℕ) (n W : ℝ) (L : ℕ)
    (Λ : X.LabelFamily) (o : Fin K → Fin m → Fin L) : ℝ≥0∞ :=
  ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
    ∫⁻ p, ENNReal.ofReal ((X.F b K n 0 (p.2 ((i : ℕ), (z : Fin m → ℤ))) - X.F b K n 0 p.1) ^ 2)
      ∂X.blockResampling n W L (fun p => Λ.sigma p.1 p.2)

/-- Equation `eq:residual` at the error `ε` of equation `eq:labelprofile`, on average over the
offsets, with the constant `c`. -/
def ResidualBound {m : ℕ} (X : Setting.{u} m) (b Cstar ε : ℝ) (L : ℕ) (c : ℝ) : Prop :=
  ∀ K : ℕ, 10 ≤ K → ∃ N₀ : ℝ, ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N →
    ∀ ℓ : ℝ, N / 8 ≤ ℓ → ℓ ≤ N → ∀ Λ : X.LabelFamily,
      Λ.IsDetermined (ℓ / K) (W K A (ℓ / K)) L → LabelProfileBound X b K A ℓ L Λ ε →
        ((L : ℝ≥0∞) ^ (m * K))⁻¹ * ∑ o : Fin K → Fin m → Fin L,
            residualEnergy X b K (ℓ / K) (W K A (ℓ / K)) L Λ o ≤
          ENNReal.ofReal (c * K * Q K A (ℓ / K) ^ 2)

/-- **Equation `eq:residual` at one length, from the small arrays.** -/
theorem average_residualEnergy_le {m K : ℕ} (X : Setting.{u} m) {b n Wn Qn lam C : ℝ}
    (hb : X.IsUpperBound b) (hn : 0 < n) (hW : 0 < Wn) (hWm : 4 * Real.sqrt m * Wn ≤ n)
    (hlam : 0 < lam) (L : ℕ+) (Λ : X.LabelFamily) (hdet : Λ.IsDetermined n Wn L)
    (hC : Profiles.ChainSumBound X b K n Wn C)
    (hBS : ∀ o : Fin K → Fin m → Fin (L : ℕ), ∑ i : Fin K,
      ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
        ∫⁻ p, ENNReal.ofReal ((X.F b K n 0 (p.2 ((i : ℕ), (z : Fin m → ℤ))) -
            X.F b K n 0 p.1) ^ 2) ∂X.blockResampling n Wn L (fun p => Λ.sigma p.1 p.2) ≤
        ENNReal.ofReal (2 * Qn ^ 2) * ∫⁻ p, ∑ i : Fin K, X.Y b n Wn Qn i
          (X.J b K n Wn 0 p.1 i.castSucc) (X.J b K n Wn 0 p.1 i.succ)
          {z | IsBlockIndex L (o i) z} Prod.fst
          (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 ((i : ℕ), z)) p
          ∂X.blockResampling n Wn L (fun p => Λ.sigma p.1 p.2))
    (y : Fin K → (Fin m → ℤ) → (Fin m → ℤ) → X.Ω → ℝ≥0∞) (hym : ∀ i j k, Measurable (y i j k))
    (hyind : iIndepFun (fun i ω => fun j k => y i j k ω) X.P)
    (hpen : ∀ i j k, Wn * zNorm (k - j) ≤ n / 2 →
      ∫⁻ ω, (y i j k ω - ENNReal.ofReal (lam * (Infra.Arrays.sqNorm (k - j) : ℝ))) ^ (4 * (m + 1))
        ∂X.P ≤ ENNReal.ofReal (lam ^ (4 * (m + 1))))
    (hysel : (Fintype.card (Fin K → Fin m → Fin (L : ℕ)) : ℝ≥0∞)⁻¹ *
      ∑ o : Fin K → Fin m → Fin (L : ℕ), ∑ i : Fin K, ∫⁻ t, X.Y b n Wn Qn i
        (X.J b K n Wn 0 ((resamplingFamily X (labelInfo X Λ hdet) i
          {z | IsBlockIndex L (o i) z}).old t) i.castSucc)
        (X.J b K n Wn 0 ((resamplingFamily X (labelInfo X Λ hdet) i
          {z | IsBlockIndex L (o i) z}).old t) i.succ) {z | IsBlockIndex L (o i) z}
        (resamplingFamily X (labelInfo X Λ hdet) i {z | IsBlockIndex L (o i) z}).old
        (resamplingFamily X (labelInfo X Λ hdet) i {z | IsBlockIndex L (o i) z}).new t
        ∂(resamplingFamily X (labelInfo X Λ hdet) i {z | IsBlockIndex L (o i) z}).P' ≤
      ∫⁻ ω, ∑ i : Fin K, y i (X.J b K n Wn 0 ω i.castSucc) (X.J b K n Wn 0 ω i.succ) ω ∂X.P) :
    ((L : ℝ≥0∞) ^ (m * K))⁻¹ * ∑ o : Fin K → Fin m → Fin (L : ℕ),
        residualEnergy X b K n Wn L Λ o ≤
      ENNReal.ofReal (2 * Qn ^ 2 * (lam * (C * K))) := by
  have hsel := hysel.trans (Profiles.lintegral_sum_le_of_chainSum hC (MeasurePreserving.id X.P) hlam
    (fun i ω j k => y i j k ω) (fun i j k => hym i j k) hyind
    {p | Wn * zNorm (p.2 - p.1) ≤ n / 2}
    (fun i j k hjk => by
      rw [Profiles.zNorm_sub_comm j k, ← Responses.sqNorm_cast_eq_zNorm_sq]
      exact hpen i j k hjk)
    (fun ω i => Profiles.J_step X hb hn hW hWm ω i))
  simp_rw [sum_lintegral_selected X hb hn hW Qn (labelInfo X Λ hdet)] at hsel
  have hcard : (Fintype.card (Fin K → Fin m → Fin (L : ℕ)) : ℝ≥0∞) = (L : ℝ≥0∞) ^ (m * K) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      ← pow_mul, Nat.cast_pow]
  rw [hcard] at hsel
  calc ((L : ℝ≥0∞) ^ (m * K))⁻¹ * ∑ o : Fin K → Fin m → Fin (L : ℕ),
        residualEnergy X b K n Wn L Λ o
      ≤ ((L : ℝ≥0∞) ^ (m * K))⁻¹ * ∑ o : Fin K → Fin m → Fin (L : ℕ),
          ENNReal.ofReal (2 * Qn ^ 2) * _ :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun o _ => hBS o)
    _ = ENNReal.ofReal (2 * Qn ^ 2) * (((L : ℝ≥0∞) ^ (m * K))⁻¹ *
          ∑ o : Fin K → Fin m → Fin (L : ℕ), _) := by
        rw [← Finset.mul_sum, mul_left_comm]
        rfl
    _ ≤ ENNReal.ofReal (2 * Qn ^ 2) * ENNReal.ofReal (lam * (C * K)) :=
        mul_le_mul' le_rfl hsel
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-- **Equation `eq:residual` with a small constant** (proof of Lemma `lem:residual`). -/
theorem exists_small_residualBound (hS : BlockSumStatement.{u}) (hM : RewardMomentStatement.{u})
    (hC : ChainSumStatement.{u}) (hL : LocalizationStatement.{u}) {m : ℕ} (hm : 1 ≤ m)
    (X : Setting.{u} m) (hX : X.IsNormalized) {b : ℝ} (hb : X.IsUpperBound b) {Cstar : ℝ}
    (hCstar : 0 < Cstar) {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ L₀ : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ L : ℕ, L₀ ≤ L → 16 ≤ L →
      ResidualBound X b Cstar ε L η := by
  obtain ⟨CY, hCY, HY⟩ := hM m hm X hX b hb Cstar hCstar
  obtain ⟨Cl, hCl, Hl⟩ := hL m hm X hX b hb Cstar hCstar
  obtain ⟨CC, hCC, HC⟩ := hC m hm X hX b hb Cstar hCstar
  have hlam : 0 < η / (2 * CC) := by positivity
  obtain ⟨lam, hlamdef⟩ : ∃ lam, lam = η / (2 * CC) := ⟨_, rfl⟩
  rw [← hlamdef] at hlam
  have hlam_eq : 2 * lam * CC = η := by rw [hlamdef]; field_simp
  obtain ⟨ε₀, hε₀, L₀, Hsmall⟩ := LabelResidual.exists_small_penalized_rewards m hCY
    (add_pos two_pos hCl) hlam
  refine ⟨ε₀, hε₀, L₀, fun ε hε hε' L hL' hL16 K hK => ?_⟩
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hK8 : (1 : ℝ) ≤ 8 * K := by linarith only [hK1]
  have hc₁ : (0 : ℝ) < 1 / (8 * K) := by positivity
  have hc₁' : 1 / (8 * (K : ℝ)) ≤ 1 := (div_le_one (by linarith only [hK8])).mpr hK8
  obtain ⟨NY, HNY⟩ := HY K
  obtain ⟨NC, HNC⟩ := HC (1 / (8 * K)) hc₁ K
  obtain ⟨Nl, HNl⟩ := Hl (1 / (8 * K)) hc₁ hc₁' K
  obtain ⟨NS, HNS⟩ := hS m hm X hX b hb Cstar hCstar K
  obtain ⟨NW, HNW⟩ := Profiles.exists_W_le Cstar (1 / (8 * K)) _ hc₁
    (by positivity : (0 : ℝ) < 1 / (4 * (Real.sqrt m + 1)))
  refine ⟨max (max NY NC) (max (max Nl NS) (max NW (8 * K))),
    fun A N hN hS' ℓ hℓ₁ hℓ₂ Λ hdet hprof => ?_⟩
  obtain ⟨hN1, hN2⟩ := max_le_iff.mp hN
  obtain ⟨hNY, hNC⟩ := max_le_iff.mp hN1
  obtain ⟨hN3, hN4⟩ := max_le_iff.mp hN2
  obtain ⟨hNl, hNS⟩ := max_le_iff.mp hN3
  obtain ⟨hNW, hNK⟩ := max_le_iff.mp hN4
  obtain ⟨hn₁, hn₄, hn, hQ, hW⟩ := Blocks.scales_of_standing hS' hℓ₁ hℓ₂
  have hnN : ℓ / K ≤ N := hn₄.trans (by linarith only [hS'.2.2.1])
  have hn1 : 1 ≤ ℓ / K := by
    rw [le_div_iff₀ (by linarith only [hK1] : (0 : ℝ) < K)]
    linarith only [hNK, hℓ₁]
  have hW1 : 1 ≤ W K A (ℓ / K) := Localization.one_le_W (by omega) hS'.2.1 hn1
  have hWm : 4 * Real.sqrt m * W K A (ℓ / K) ≤ ℓ / K := Blocks.four_sqrt_mul_le hn
    (HNW K hK A N (by linarith only [hS'.2.1]) hNW hS'.2.2.2.2 (ℓ / K) hn₁ hnN)
  have hL1 : 1 ≤ L := by omega
  let LP : ℕ+ := ⟨L, hL1⟩
  have hsum := fun o : Fin K → Fin m → Fin L =>
    HNS A N hNS hS' ℓ hℓ₁ hℓ₂ L hL1 (labelInfo X Λ hdet) o
  have hloc (i : Fin K) (j k : Fin m → ℤ) (hjk : W K A (ℓ / K) * zNorm (k - j) ≤ ℓ / K / 2) :
      Cited.IsOs X.P 2 (2 + Cl)
        (Responses.pairLocalizationRadius X b (ℓ / K) (W K A (ℓ / K)) i j k) :=
    Blocks.isOs_one_add_gridPair X hn hW hCl (HNl A N hNl hS' _ hn₁ hnN) i hjk
  have hhigh (i : Fin K) (q : Fin m → Fin L) (j k : Fin m → ℤ)
      (hjk : W K A (ℓ / K) * zNorm (k - j) ≤ ℓ / K / 2) :
      ∫⁻ t, X.Y b (ℓ / K) (W K A (ℓ / K)) (Q K A (ℓ / K)) i j k {z | IsBlockIndex L q z}
          (resamplingFamily X (labelInfo X Λ hdet) i {z | IsBlockIndex L q z}).old
          (resamplingFamily X (labelInfo X Λ hdet) i {z | IsBlockIndex L q z}).new t ^ (16 * (m + 1))
          ∂(resamplingFamily X (labelInfo X Λ hdet) i {z | IsBlockIndex L q z}).P' ≤
        ENNReal.ofReal ((CY * (1 + zNorm (k - j))) ^ (16 * (m + 1))) := by
    have h := HNY A N hNY hS' ℓ hℓ₁ hℓ₂ L hL1 (labelInfo X Λ hdet) q i i.2 j k hjk
    rw [Profiles.zNorm_sub_comm j k] at h
    exact (lintegral_realResampling X (labelInfo X Λ hdet) fun p =>
      X.Y b (ℓ / K) (W K A (ℓ / K)) (Q K A (ℓ / K)) i j k {z | IsBlockIndex L q z} Prod.fst
        (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 ((i : ℕ), z)) p ^ (16 * (m + 1))).trans_le h
  obtain ⟨y, hym, hyind, hpen, hysel⟩ := Hsmall X Λ b A ℓ ε K LP hε.le hε' hL' hprof hb hn hW1 hQ
    hloc (fun i q => resamplingFamily X (labelInfo X Λ hdet) i {z | IsBlockIndex L q z})
    (fun i q z => ae_label_eq X Λ hdet i _ z) hhigh
  have hmain := average_residualEnergy_le X hb hn hW hWm hlam LP Λ hdet
    (HNC A N hNC hS' K (ℓ / K) (by omega) hn₁ hn₄) hsum y hym hyind hpen hysel
  refine hmain.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [← hlam_eq]
  ring

/-- **Equation `eq:residual` with a constant**, for all `ε` and `L`: the second bound of equation
`eq:rewardmoment`, averaged over the offsets. -/
theorem exists_coarse_residualBound (hS : BlockSumStatement.{u}) (hM : RewardMomentStatement.{u})
    (hC : ChainSumStatement.{u}) {m : ℕ} (hm : 1 ≤ m) (X : Setting.{u} m) (hX : X.IsNormalized)
    {b : ℝ} (hb : X.IsUpperBound b) {Cstar : ℝ} (hCstar : 0 < Cstar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ L : ℕ, 16 ≤ L → ResidualBound X b Cstar ε L C := by
  obtain ⟨C, hC', H⟩ := Blocks.blockReplacementStatement_of hS hM hC m hm X hX b hb Cstar hCstar
  refine ⟨C, hC'.le, fun ε _ L hL16 K _ => ?_⟩
  obtain ⟨N₀, HN⟩ := H K
  have hL1 : 1 ≤ L := by omega
  exact ⟨N₀, fun A N hN hS' ℓ hℓ₁ hℓ₂ Λ hdet _ => LabelResidual.average_offsets_le hL1 _ fun o =>
    HN A N hN hS' ℓ hℓ₁ hℓ₂ L hL1 (labelInfo X Λ hdet) o⟩

/-- **Equation `eq:residual`, with one modulus `G(ε, L)`** (proof of Lemma `lem:residual`). -/
theorem exists_residual_modulus (hS : BlockSumStatement.{u}) (hM : RewardMomentStatement.{u})
    (hC : ChainSumStatement.{u}) (hL : LocalizationStatement.{u}) {m : ℕ} (hm : 1 ≤ m)
    (X : Setting.{u} m) (hX : X.IsNormalized) {b : ℝ} (hb : X.IsUpperBound b) {Cstar : ℝ}
    (hCstar : 0 < Cstar) :
    ∃ G : ℝ → ℕ → ℝ,
      (∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ L₀ : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ L : ℕ, L₀ ≤ L → G ε L ≤ η) ∧
      ∀ ε : ℝ, 0 < ε → ∀ L : ℕ, 16 ≤ L → ResidualBound X b Cstar ε L (G ε L) := by
  refine LabelResidual.exists_uniform_small_majorant (fun ε L c => ResidualBound X b Cstar ε L c)
    (fun ε L c c' hcc' H K hK => ?_) (exists_coarse_residualBound hS hM hC hm X hX hb hCstar)
    fun η hη => exists_small_residualBound hS hM hC hL hm X hX hb hCstar hη
  obtain ⟨N₀, hN₀⟩ := H K hK
  exact ⟨N₀, fun A N hN hS' ℓ hℓ₁ hℓ₂ Λ hdet hprof =>
    (hN₀ A N hN hS' ℓ hℓ₁ hℓ₂ Λ hdet hprof).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc' (Nat.cast_nonneg K))
        (sq_nonneg _)))⟩

end IsotropicVariance.Paper.Proofs.Residual
