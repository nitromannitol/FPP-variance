/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Blocks
public import IsotropicVariance.Paper.Contracts.Gain
public import IsotropicVariance.Paper.Contracts.Profiles
public import IsotropicVariance.Paper.Proofs.Gain.FewTranslatesShift
public import IsotropicVariance.Paper.Proofs.Gain.Influence
import IsotropicVariance.Paper.Proofs.Profiles.RowEnergyIndex
import IsotropicVariance.Paper.Proofs.Blocks.Scales
import IsotropicVariance.Paper.Proofs.Profiles.Asymptotics
import IsotropicVariance.Paper.Proofs.Gain.GainAssembly
import IsotropicVariance.Paper.Proofs.Gain.PoincareJensen
import IsotropicVariance.Paper.Proofs.Resampling.Coupling

/-!
# Lemma `lem:fewtranslates`

The lemma and its proof: for `L ≥ 16` and `N` large depending on `K` and `L`, for every choice of
the `a_i`, `Σ_G E[(f − E_G[f])²] ≤ C K Q_n²` and `Σ_G E[|f − E_G[f]|]² ≤ C K^{−1/6} K Q_n²`, for
`f = E[F̄ | (X_G)_G]` on the noise and `ω^G` the resampling with `σ_G` constant.

The steps of the paper's proof, in order.

* `f − E_G[f] = ⌈K^{2/3}⌉⁻¹ Σ_m E[F_m − F_m^G | (X_H)_H]`: `condExp_sub_resampled_ae_eq`.
* `F_m^G = F_m` unless `G` meets the tube of one of the two noises:
  `F_le_of_disjoint_tube`, inside `sq_lintegral_abs_averagedMin_sub_le_of_isBlockCoupling`.
* The tube meets at most `C(1 + |x_i − x_{i−1} − ne₁|/(nQ_n)^{1/2} + R_i(x_{i−1}, x_i))` translates
  of `G`, and this number has mean at most `C K^{1/2}`: `card_hit_le`, `sum_measure_hit_le`.
* For an independent `m`, `G` meets either tube of `F_m` with probability at most
  `2 C K^{1/2}/⌈K^{2/3}⌉ ≤ C K^{−1/6}`: the factor of the second display, with
  `sqrt_div_colCount_le`.
* Jensen's inequality and the Cauchy–Schwarz inequality for the joint law of `m` and the noise:
  `sq_eLpNorm_two_labelMean_sub_le`, `sq_eLpNorm_one_labelMean_sub_le`.
* Equation `eq:rewardmoment` for `F_m` by stationarity, and the sum over `G`:
  `tsum_lintegral_F_shift_bot`, `sum_tsum_eLpNorm_two_le`, `sum_tsum_eLpNorm_one_le`.

As in `Paper.Proofs.Gain.Influence`, the tube is that of `F`, and the block moves: the translation
of `F_j` to `F` maps `G` to `block(i, z − j L e₀)`. The number of translates is counted with the
cube indices, `2 R_i(J_i, J_{i+1}) + 2 |J_{i+1} − J_i| + 2`, so equation `eq:rowenergy` is used in
the indices (`Profiles.rowEnergyIndexStatement_of_rowEnergy`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper IsotropicVariance.Paper.Contracts

variable {m L K : ℕ} {X : Setting.{u} m}

/-- **Jensen over `m`**: the average over `j < M` of a family with sums over the blocks at most `a`
has sum over the blocks at most `a`. -/
theorem sum_tsum_average_le {K M : ℕ} (hM : 1 ≤ M) {Z : Fin K → Type*}
    (e : ℕ → (i : Fin K) → Z i → ℝ≥0∞) {a : ℝ≥0∞} (hS : ∀ j, ∑ i, ∑' z, e j i z ≤ a) :
    ∑ i, ∑' z, ((M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, e j i z) ≤ a := by
  have hM0 : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  calc ∑ i, ∑' z, ((M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, e j i z)
      = (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, ∑ i, ∑' z, e j i z := by
        simp_rw [ENNReal.tsum_mul_left]
        rw [← Finset.mul_sum]
        simp_rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        rw [Finset.sum_comm]
    _ ≤ (M : ℝ≥0∞)⁻¹ * ∑ _j ∈ Finset.range M, a := by
        gcongr with j hj
        exact hS j
    _ = a := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel hM0 (ENNReal.natCast_ne_top M), one_mul]

/-- The change of a function of the noise under the resampling is a random variable. -/
theorem aestronglyMeasurable_old_sub_new {n W : ℝ} {Z : X.Ω → ℝ}
    (hZ : AEStronglyMeasurable Z X.P) (c : BlockIdx m) :
    AEStronglyMeasurable (fun q : X.Ω × (BlockIdx m → X.Ω) => Z q.1 - Z (q.2 c))
      (X.botResampling n W L) :=
  (hZ.comp_measurePreserving (X.measurePreserving_old _ _)).sub
    (hZ.comp_measurePreserving (X.measurePreserving_new (σ := (X.botInfo n W L).1) bot_le))

/-- **Jensen's inequality** (first bound of the last display of the proof of Lemma
`lem:fewtranslates`):
`E[(f − E_G[f])²] ≤ ⌈K^{2/3}⌉⁻¹ Σ_m E[(F_m − F_m^G)²]`. -/
theorem sq_eLpNorm_two_labelMean_sub_le {b : ℝ} (hb : X.IsUpperBound b) (hM : 1 ≤ colCount K)
    (Λ : X.LabelFamily) {n W : ℝ} (hn : 0 < n) (hW : 0 < W) (hdet : Λ.IsDetermined n W L)
    (o : Fin K → Fin m → Fin L) {i : Fin K} {z : Fin m → ℤ} (hz : IsBlockIndex L (o i) z) :
    eLpNorm (X.labelMean b K n W Λ o -
        X.P[X.labelMean b K n W Λ o | Λ.otherSigma K o i z]) 2 X.P ^ 2 ≤
      (colCount K : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range (colCount K),
        ∫⁻ p, ENNReal.ofReal ((X.F b K n (((j : ℝ) * L * W) • e₂ m) (p.2 ((i : ℕ), z)) -
          X.F b K n (((j : ℝ) * L * W) • e₂ m) p.1) ^ 2) ∂X.botResampling n W L := by
  have hZ := (averagedMin_regular X hb K hn.le W L).1
  have hc := X.isBlockCoupling_blockResampling n W L (σ := (X.botInfo n W L).1) i z bot_le
  have hJ := eLpNorm_sub_condExp_le Λ hn hW hdet o hz (hZ.integrable one_le_two)
    (p := 2) one_le_two
  have hm := aestronglyMeasurable_old_sub_new (n := n) (W := W) (L := L) hZ.aestronglyMeasurable
    ((i : ℕ), z)
  have hFj : ∀ j : ℕ, AEMeasurable (fun p : X.Ω × (BlockIdx m → X.Ω) =>
      X.F b K n (((j : ℝ) * L * W) • e₂ m) (p.2 ((i : ℕ), z)) -
        X.F b K n (((j : ℝ) * L * W) • e₂ m) p.1) (X.botResampling n W L) := fun j =>
    aemeasurable_sub_of_isBlockCoupling hc (aemeasurable_F X hb K hn.le (lon_smul_e₂ _))
  calc eLpNorm (X.labelMean b K n W Λ o -
        X.P[X.labelMean b K n W Λ o | Λ.otherSigma K o i z]) 2 X.P ^ 2
      ≤ eLpNorm (fun q : X.Ω × (BlockIdx m → X.Ω) => averagedMin X b K n W L q.1 -
          averagedMin X b K n W L (q.2 ((i : ℕ), z))) 2 (X.botResampling n W L) ^ 2 :=
        pow_le_pow_left' hJ 2
    _ = ∫⁻ q, ENNReal.ofReal (((colCount K : ℝ)⁻¹ * ∑ j ∈ Finset.range (colCount K),
          (X.F b K n (((j : ℝ) * L * W) • e₂ m) (q.2 ((i : ℕ), z)) -
            X.F b K n (((j : ℝ) * L * W) • e₂ m) q.1)) ^ 2) ∂X.botResampling n W L := by
        rw [Poincare.eLpNorm_two_sq _ hm]
        refine lintegral_congr fun q => ?_
        rw [← averagedMin_sub, sub_sq_comm]
    _ ≤ _ := lintegral_sq_average_le hM _ hFj

/-- **The Cauchy–Schwarz inequality for the joint law of `m` and the noise**
(second bound of the last display of the proof of Lemma `lem:fewtranslates`):
`E[|f − E_G[f]|]² ≤ (⌈K^{2/3}⌉⁻¹ Σ_m E[(F_m − F_m^G)²])
(⌈K^{2/3}⌉⁻¹ Σ_m 2 P(G_m meets the tube))`. -/
theorem sq_eLpNorm_one_labelMean_sub_le (hm : 1 ≤ m) {b : ℝ} (hb : X.IsUpperBound b)
    (hM : 1 ≤ colCount K) (Λ : X.LabelFamily) {n W : ℝ} (hn : 0 < n) (hW : 1 ≤ W)
    (hWn : W * Real.sqrt m ≤ n / 4) (hdet : Λ.IsDetermined n W L) (o : Fin K → Fin m → Fin L)
    {i : Fin K} {z : Fin m → ℤ} (hz : IsBlockIndex L (o i) z) :
    eLpNorm (X.labelMean b K n W Λ o -
        X.P[X.labelMean b K n W Λ o | Λ.otherSigma K o i z]) 1 X.P ^ 2 ≤
      ((colCount K : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range (colCount K),
          ∫⁻ p, ENNReal.ofReal ((X.F b K n (((j : ℝ) * L * W) • e₂ m) (p.2 ((i : ℕ), z)) -
            X.F b K n (((j : ℝ) * L * W) • e₂ m) p.1) ^ 2) ∂X.botResampling n W L) *
        ((colCount K : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range (colCount K),
          2 * X.P {c | ¬ Disjoint (block n W L i (z - blockShift hm j L)) (tube X b K n W c i)}) := by
  have hZ := (averagedMin_regular X hb K hn.le W L).1
  have hW0 : 0 < W := by linarith only [hW]
  have hc := X.isBlockCoupling_blockResampling n W L (σ := (X.botInfo n W L).1) i z bot_le
  have hJ := eLpNorm_sub_condExp_le Λ hn hW0 hdet o hz (hZ.integrable one_le_two)
    (p := 1) le_rfl
  have hme := aestronglyMeasurable_old_sub_new (n := n) (W := W) (L := L) hZ.aestronglyMeasurable
    ((i : ℕ), z)
  calc eLpNorm (X.labelMean b K n W Λ o -
        X.P[X.labelMean b K n W Λ o | Λ.otherSigma K o i z]) 1 X.P ^ 2
      ≤ eLpNorm (fun q : X.Ω × (BlockIdx m → X.Ω) => averagedMin X b K n W L q.1 -
          averagedMin X b K n W L (q.2 ((i : ℕ), z))) 1 (X.botResampling n W L) ^ 2 :=
        pow_le_pow_left' hJ 2
    _ = (∫⁻ q, ENNReal.ofReal |averagedMin X b K n W L (q.2 ((i : ℕ), z)) -
          averagedMin X b K n W L q.1| ∂X.botResampling n W L) ^ 2 := by
        rw [Poincare.eLpNorm_one_eq _ hme]
        congr 1
        exact lintegral_congr fun q => by rw [abs_sub_comm]
    _ ≤ _ := sq_lintegral_abs_averagedMin_sub_le_of_isBlockCoupling X hm hb hM hn hW hWn i z hc

/-- **The first bound, summed over the blocks**: by Jensen's inequality and stationarity, it is at
most the bound `a` of equation `eq:rewardmoment` for `F`. -/
theorem sum_tsum_eLpNorm_two_le (hm : 1 ≤ m) {b : ℝ} (hb : X.IsUpperBound b) (hM : 1 ≤ colCount K)
    (Λ : X.LabelFamily) {n W : ℝ} (hn : 0 < n) (hW : 0 < W) (hdet : Λ.IsDetermined n W L)
    (o : Fin K → Fin m → Fin L) {a : ℝ≥0∞}
    (hS : ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
      ∫⁻ p, ENNReal.ofReal ((X.F b K n 0 (p.2 ((i : ℕ), (z : Fin m → ℤ))) -
        X.F b K n 0 p.1) ^ 2) ∂X.botResampling n W L ≤ a) :
    ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
        eLpNorm (X.labelMean b K n W Λ o -
          X.P[X.labelMean b K n W Λ o | Λ.otherSigma K o i z]) 2 X.P ^ 2 ≤ a := by
  refine le_trans (Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun z =>
    sq_eLpNorm_two_labelMean_sub_le hb hM Λ hn hW hdet o z.2) ?_
  refine sum_tsum_average_le hM _ fun j => ?_
  rw [tsum_lintegral_F_shift_bot X hm hb hn o j]
  exact hS

/-- **The second bound, summed over the blocks**: for every block, if the probabilities that its
translates meet the tube sum to at most `p`, then the sum is at most `a (2p/M)`. -/
theorem sum_tsum_eLpNorm_one_le (hm : 1 ≤ m) {b : ℝ} (hb : X.IsUpperBound b)
    (hM : 1 ≤ colCount K) (Λ : X.LabelFamily) {n W : ℝ} (hn : 0 < n) (hW : 1 ≤ W)
    (hWn : W * Real.sqrt m ≤ n / 4) (hdet : Λ.IsDetermined n W L) (o : Fin K → Fin m → Fin L)
    {a p : ℝ≥0∞}
    (hS : ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
      ∫⁻ p, ENNReal.ofReal ((X.F b K n 0 (p.2 ((i : ℕ), (z : Fin m → ℤ))) -
        X.F b K n 0 p.1) ^ 2) ∂X.botResampling n W L ≤ a)
    (hp : ∀ (i : Fin K) (z : Fin m → ℤ), ∑ j ∈ Finset.range (colCount K),
      X.P {c | ¬ Disjoint (block n W L i (z - blockShift hm j L)) (tube X b K n W c i)} ≤ p) :
    ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
        eLpNorm (X.labelMean b K n W Λ o -
          X.P[X.labelMean b K n W Λ o | Λ.otherSigma K o i z]) 1 X.P ^ 2 ≤
      a * ((colCount K : ℝ≥0∞)⁻¹ * (2 * p)) := by
  set q := (colCount K : ℝ≥0∞)⁻¹ * (2 * p) with hq
  have hblk : ∀ (i : Fin K) (z : {z : Fin m → ℤ | IsBlockIndex L (o i) z}),
      eLpNorm (X.labelMean b K n W Λ o -
        X.P[X.labelMean b K n W Λ o | Λ.otherSigma K o i z]) 1 X.P ^ 2 ≤
      ((colCount K : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range (colCount K),
          ∫⁻ p, ENNReal.ofReal ((X.F b K n (((j : ℝ) * L * W) • e₂ m)
              (p.2 ((i : ℕ), (z : Fin m → ℤ))) -
            X.F b K n (((j : ℝ) * L * W) • e₂ m) p.1) ^ 2) ∂X.botResampling n W L) * q := by
    intro i z
    refine (sq_eLpNorm_one_labelMean_sub_le hm hb hM Λ hn hW hWn hdet o z.2).trans ?_
    refine mul_le_mul' le_rfl ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (hp i z))
  refine le_trans (Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum (hblk i)) ?_
  simp_rw [ENNReal.tsum_mul_right]
  rw [← Finset.sum_mul]
  refine mul_le_mul' (sum_tsum_average_le hM _ fun j => ?_) le_rfl
  rw [tsum_lintegral_F_shift_bot X hm hb hn o j]
  exact hS

/-- The arithmetic of the second bound, `2 C √K / ⌈K^{2/3}⌉ ≤ C K^{−1/6}`. -/
theorem ofReal_mul_inv_colCount_le {CB Cp Q : ℝ} {K : ℕ} (hK : 1 ≤ K) (hCB : 0 < CB)
    (hCp : 0 < Cp) :
    ENNReal.ofReal (CB * K * Q ^ 2) *
        ((colCount K : ℝ≥0∞)⁻¹ * (2 * ENNReal.ofReal (Cp * Real.sqrt K))) ≤
      ENNReal.ofReal (CB * (1 + 2 * Cp) * (K : ℝ) ^ (-(1 : ℝ) / 6) * K * Q ^ 2) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hM0 : (0 : ℝ) < colCount K := by exact_mod_cast one_le_colCount hK
  have hCBKQ : 0 ≤ CB * K * Q ^ 2 := by positivity
  have hsd := sqrt_div_colCount_le hK
  have h1 : (colCount K : ℝ)⁻¹ * (2 * (Cp * Real.sqrt K)) ≤
      (1 + 2 * Cp) * (K : ℝ) ^ (-(1 : ℝ) / 6) := by
    calc (colCount K : ℝ)⁻¹ * (2 * (Cp * Real.sqrt K))
        = 2 * Cp * (Real.sqrt K / colCount K) := by ring
      _ ≤ 2 * Cp * (K : ℝ) ^ (-(1 : ℝ) / 6) := mul_le_mul_of_nonneg_left hsd (by positivity)
      _ ≤ (1 + 2 * Cp) * (K : ℝ) ^ (-(1 : ℝ) / 6) :=
          mul_le_mul_of_nonneg_right (by linarith only []) (Real.rpow_nonneg hK0.le _)
  have hreal : CB * K * Q ^ 2 * ((colCount K : ℝ)⁻¹ * (2 * (Cp * Real.sqrt K))) ≤
      CB * (1 + 2 * Cp) * (K : ℝ) ^ (-(1 : ℝ) / 6) * K * Q ^ 2 :=
    calc CB * K * Q ^ 2 * ((colCount K : ℝ)⁻¹ * (2 * (Cp * Real.sqrt K)))
        ≤ CB * K * Q ^ 2 * ((1 + 2 * Cp) * (K : ℝ) ^ (-(1 : ℝ) / 6)) :=
          mul_le_mul_of_nonneg_left h1 hCBKQ
      _ = CB * (1 + 2 * Cp) * (K : ℝ) ^ (-(1 : ℝ) / 6) * K * Q ^ 2 := by ring
  calc ENNReal.ofReal (CB * K * Q ^ 2) *
        ((colCount K : ℝ≥0∞)⁻¹ * (2 * ENNReal.ofReal (Cp * Real.sqrt K)))
      = ENNReal.ofReal (CB * K * Q ^ 2 * ((colCount K : ℝ)⁻¹ * (2 * (Cp * Real.sqrt K)))) := by
        rw [ENNReal.ofReal_mul hCBKQ, ENNReal.ofReal_mul (inv_nonneg.2 hM0.le),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_inv_of_pos hM0,
          ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- **The two bounds of Lemma `lem:fewtranslates` at one scale**, from equation `eq:rewardmoment`,
the row energy and the radius energy at that scale. -/
theorem fewTranslates_bounds (hm : 1 ≤ m) {b : ℝ} (hb : X.IsUpperBound b) (hK : 1 ≤ K)
    (hL : 1 ≤ L) {n W Qn CB Crow Crad : ℝ} (hn : 0 < n) (hW : 1 ≤ W)
    (hWn : W * Real.sqrt m ≤ n / 4) (hCB : 0 < CB) (hCrow : 0 < Crow) (hCrad : 0 < Crad)
    (Λ : X.LabelFamily) (hdet : Λ.IsDetermined n W L) (o : Fin K → Fin m → Fin L)
    (hS : ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
      ∫⁻ p, ENNReal.ofReal ((X.F b K n 0 (p.2 ((i : ℕ), (z : Fin m → ℤ))) -
        X.F b K n 0 p.1) ^ 2) ∂X.botResampling n W L ≤ ENNReal.ofReal (CB * K * Qn ^ 2))
    (hrow : ∫⁻ ω, ENNReal.ofReal (∑ i : Fin K,
      zNorm (X.J b K n W 0 ω i.succ - X.J b K n W 0 ω i.castSucc) ^ 2) ∂X.P ≤
        ENNReal.ofReal (5 * Crow * K))
    (hrad : ∫⁻ ω, ENNReal.ofReal (∑ i : Fin K, X.R b n W ω i (X.J b K n W 0 ω i.castSucc)
      (X.J b K n W 0 ω i.succ) ^ 2) ∂X.P ≤ ENNReal.ofReal (Crad * K)) :
    ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
        eLpNorm (X.labelMean b K n W Λ o -
          X.P[X.labelMean b K n W Λ o | Λ.otherSigma K o i z]) 2 X.P ^ 2 ≤
        ENNReal.ofReal (CB * (1 + 2 * (5 * Crow + Crad + 4)) * K * Qn ^ 2) ∧
      ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
        eLpNorm (X.labelMean b K n W Λ o -
          X.P[X.labelMean b K n W Λ o | Λ.otherSigma K o i z]) 1 X.P ^ 2 ≤
        ENNReal.ofReal (CB * (1 + 2 * (5 * Crow + Crad + 4)) * (K : ℝ) ^ (-(1 : ℝ) / 6) * K *
          Qn ^ 2) := by
  have hW0 : 0 < W := by linarith only [hW]
  have hM := one_le_colCount hK
  set Cp : ℝ := 5 * Crow + Crad + 4 with hCp
  have hCp0 : 0 < Cp := by positivity
  have hp : ∀ (i : Fin K) (z : Fin m → ℤ), ∑ j ∈ Finset.range (colCount K),
      X.P {c | ¬ Disjoint (block n W L i (z - blockShift hm j L)) (tube X b K n W c i)} ≤
        ENNReal.ofReal (Cp * Real.sqrt K) := fun i z =>
    sum_measure_hit_le X hm hb hK hn hW0 hL (colCount K) i z (by positivity) hCrad.le hrow hrad
  refine ⟨(sum_tsum_eLpNorm_two_le hm hb hM Λ hn hW0 hdet o hS).trans ?_,
    (sum_tsum_eLpNorm_one_le hm hb hM Λ hn hW hWn hdet o hS hp).trans
      (ofReal_mul_inv_colCount_le hK hCB hCp0)⟩
  refine ENNReal.ofReal_le_ofReal ?_
  have hq : 0 ≤ CB * K * Qn ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left (by linarith only [hCp0] : (1 : ℝ) ≤ 1 + 2 * Cp) hq
  linarith only [this]

/-- **Lemma `lem:fewtranslates`**, from equation `eq:rowenergy`,
equation `eq:radiusenergy` and the second bound of equation `eq:rewardmoment`. The constant is
`C = C_B (1 + 2 (5 C_row + C_rad + 4))`, the threshold makes `n = ℓ/K ≥ 1` and `W_n √m ≤ n/4`
(`Profiles.exists_W_le`). -/
theorem fewTranslatesStatement_of (hR : RowEnergyStatement.{u}) (hE : RadiusEnergyStatement.{u})
    (hB : BlockReplacementStatement.{u}) : FewTranslatesStatement.{u} := by
  intro m hm X hX b hb Cstar hC
  obtain ⟨CB, hCB, HB⟩ := hB m hm X hX b hb Cstar hC
  obtain ⟨Crow, hCrow, Hrow⟩ :=
    Profiles.rowEnergyIndexStatement_of_rowEnergy hR m hm X hX b hb Cstar hC
  obtain ⟨Crad, hCrad, Hrad⟩ := hE m hm X hX b hb Cstar hC
  refine ⟨CB * (1 + 2 * (5 * Crow + Crad + 4)), by positivity, fun K hK L hL => ?_⟩
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hc₁ : (0 : ℝ) < 1 / (8 * K) := by positivity
  obtain ⟨N₁, hN₁⟩ := HB K
  obtain ⟨N₂, hN₂⟩ := Hrow (1 / (8 * K)) hc₁ K
  obtain ⟨N₃, hN₃⟩ := Hrad K
  obtain ⟨N₄, hN₄⟩ := Profiles.exists_W_le Cstar (1 / (8 * K)) (1 / (4 * (Real.sqrt m + 1))) hc₁
    (by positivity)
  refine ⟨max (max N₁ N₂) (max N₃ (max N₄ (8 * K))), fun A N hN hS ℓ hℓ₁ hℓ₂ Λ hdet o => ?_⟩
  have hN₁' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₃' : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN₄' : N₄ ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hN₅ : 8 * (K : ℝ) ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  obtain ⟨hc₁N, hnN4, hn0, hQ0, -⟩ := Blocks.scales_of_standing hS hℓ₁ hℓ₂
  set n := ℓ / K with hn_def
  have hn1 : 1 ≤ n := by rw [hn_def, le_div_iff₀ hK0]; linarith only [hN₅, hℓ₁]
  have hQ1 : 1 ≤ Q K A n := Profiles.one_le_Q hK hS.2.1 hn1
  have hW1 : 1 ≤ W K A n := by
    unfold W
    rw [Real.one_le_sqrt]
    exact one_le_mul_of_one_le_of_one_le hn1 hQ1
  have hWn : W K A n * Real.sqrt m ≤ n / 4 := by
    have h := Blocks.four_sqrt_mul_le hn0 (hN₄ K hK A N (by linarith only [hS.2.1]) hN₄'
      hS.2.2.2.2 n hc₁N (by linarith only [hnN4, hN₅, hK0]))
    linarith only [h]
  have hE₀ := hN₁ A N hN₁' hS ℓ hℓ₁ hℓ₂ L (by omega) (X.botInfo n (W K A n) L) o
  have hrow := lintegral_sum_zNorm_sq_le X b hK1 hQ0 hCrow (hN₂ A N hN₂' hS K n hK1 hc₁N hnN4)
  exact fewTranslates_bounds hm hb hK1 (by omega) hn0 hW1 hWn hCB hCrow hCrad Λ hdet o hE₀ hrow
    (hN₃ A N hN₃' hS ℓ hℓ₁ hℓ₂)

end IsotropicVariance.Paper.Proofs.Gain
