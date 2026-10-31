/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.AveragedMin
public import IsotropicVariance.Paper.Proofs.Gain.Translation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Chebyshev

/-!
# The variance of the averaged minimum: the elementary steps

The analytic steps of the proof of Proposition `prop:gain` that do not involve the noise
interface:

* `evariance_le_two_mul`: `Var T ≤ 2 E (F̄ − T)² + 2 Var F̄`;
* `mul_Q_sq_le`: `K Q_n² ≤ 3 Q_ℓ²` for `n = ℓ/K` (`K Q_n² = K^{2/K} Q_ℓ²` and `K^{2/K} ≤ e`);
* `lintegral_sq_average_le`: Jensen's inequality over the translates;
* `labelCouplingEnergy_averagedMin_le`: the label energy of `F̄` is at most the average over the
  translates of the label energies of `F` for the translated resamplings ("by stationarity").
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper

/-! ### Variance -/

/-- **`Var T ≤ 2 E (Z − T)² + 2 Var Z`** for square-integrable `T`, `Z`. -/
theorem evariance_le_two_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T Z : Ω → ℝ} (hT : MemLp T 2 P) (hZ : MemLp Z 2 P) :
    evariance T P ≤ 2 * ∫⁻ ω, ENNReal.ofReal ((Z ω - T ω) ^ 2) ∂P + 2 * evariance Z P := by
  set c := ∫ ω, Z ω ∂P
  have hTm := hT.aestronglyMeasurable
  have hTZ : MemLp (fun ω => Z ω - T ω) 2 P := hZ.sub hT
  have hZc : MemLp (fun ω => Z ω - c) 2 P := hZ.sub (memLp_const c)
  have hint1 : Integrable (fun ω => (Z ω - T ω) ^ 2) P := hTZ.integrable_sq
  have hint2 : Integrable (fun ω => (Z ω - c) ^ 2) P := hZc.integrable_sq
  -- `Var T = Var (T − c) ≤ E (T − c)² ≤ 2 E (Z − T)² + 2 E (Z − c)²`
  have hvar : variance T P ≤ 2 * ∫ ω, (Z ω - T ω) ^ 2 ∂P + 2 * variance Z P := by
    have h1 : variance T P = variance (fun ω => T ω - c) P := (variance_sub_const hTm c).symm
    have h2 : variance (fun ω => T ω - c) P ≤ ∫ ω, (T ω - c) ^ 2 ∂P :=
      variance_le_expectation_sq (hTm.sub aestronglyMeasurable_const)
    have h3 : ∫ ω, (T ω - c) ^ 2 ∂P ≤ ∫ ω, (2 * (Z ω - T ω) ^ 2 + 2 * (Z ω - c) ^ 2) ∂P := by
      refine integral_mono ((hT.sub (memLp_const c)).integrable_sq)
        ((hint1.const_mul 2).add (hint2.const_mul 2)) fun ω => ?_
      nlinarith [sq_nonneg (Z ω - T ω + (Z ω - c)), sq_nonneg (Z ω - T ω - (Z ω - c))]
    have h4 : variance Z P = ∫ ω, (Z ω - c) ^ 2 ∂P := by
      rw [variance, evariance_eq_lintegral_ofReal, ← ofReal_integral_eq_lintegral_ofReal hint2
        (ae_of_all _ fun ω => sq_nonneg _), ENNReal.toReal_ofReal (integral_nonneg fun ω =>
          sq_nonneg _)]
    rw [h1]
    refine h2.trans (h3.trans (le_of_eq ?_))
    rw [integral_add (hint1.const_mul 2) (hint2.const_mul 2), integral_const_mul,
      integral_const_mul, h4]
  rw [← ofReal_variance hT, ← ofReal_variance hZ, ← ofReal_integral_eq_lintegral_ofReal hint1
    (ae_of_all _ fun ω => sq_nonneg _)]
  have h0 : 0 ≤ ∫ ω, (Z ω - T ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  calc ENNReal.ofReal (variance T P)
      ≤ ENNReal.ofReal (2 * ∫ ω, (Z ω - T ω) ^ 2 ∂P + 2 * variance Z P) :=
        ENNReal.ofReal_le_ofReal hvar
    _ = _ := by
        rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) h0)
          (mul_nonneg (by norm_num) (variance_nonneg _ _)), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-! ### Scales -/

/-- `K^{2/K} ≤ 3` for every `K ≥ 1`. -/
theorem rpow_two_div_le_three {K : ℝ} (hK : 1 ≤ K) : K ^ (2 / K) ≤ 3 := by
  have hK0 : 0 < K := by linarith
  -- `log K ≤ K / e ≤ K / 2`
  have hlog : Real.log K ≤ K / 2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < K / Real.exp 1 by positivity)
    rw [Real.log_div hK0.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have : K / Real.exp 1 ≤ K / 2 := div_le_div_of_nonneg_left hK0.le (by norm_num) he
    linarith
  rw [Real.rpow_def_of_pos hK0]
  calc Real.exp (Real.log K * (2 / K)) ≤ Real.exp 1 := by
        refine Real.exp_le_exp.2 ?_
        rw [mul_div_assoc', div_le_one hK0]
        linarith
    _ ≤ 3 := by linarith [Real.exp_one_lt_d9]

/-- **`K Q_n² ≤ 3 Q_ℓ²`** for `n = ℓ/K`: `K Q_n² = K^{2/K} Q_ℓ²`. -/
theorem mul_Q_sq_le {K : ℕ} (hK : 1 ≤ K) (A : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (K : ℝ) * Q K A (ℓ / K) ^ 2 ≤ 3 * Q K A ℓ ^ 2 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  set c : ℝ := 1 / 2 - 1 / (K : ℝ)
  have hsq : ∀ x : ℝ, 0 ≤ x → (x ^ c) ^ 2 = x ^ (2 * c) := fun x hx => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    ring_nf
  have hQn : Q K A (ℓ / K) ^ 2 = A ^ 2 * (ℓ ^ (2 * c) / (K : ℝ) ^ (2 * c)) := by
    rw [Q, mul_pow, hsq _ (div_nonneg hℓ hK0.le), Real.div_rpow hℓ hK0.le]
  have hQℓ : Q K A ℓ ^ 2 = A ^ 2 * ℓ ^ (2 * c) := by rw [Q, mul_pow, hsq _ hℓ]
  have hKc : (K : ℝ) / (K : ℝ) ^ (2 * c) = (K : ℝ) ^ (2 / (K : ℝ)) := by
    rw [div_eq_iff (Real.rpow_pos_of_pos hK0 _).ne', ← Real.rpow_add hK0]
    conv_lhs => rw [← Real.rpow_one (K : ℝ)]
    congr 1
    simp only [c]
    ring
  rw [hQn, hQℓ]
  have h3 := rpow_two_div_le_three (show (1 : ℝ) ≤ K by exact_mod_cast hK)
  have hA : 0 ≤ A ^ 2 * ℓ ^ (2 * c) := by positivity
  calc (K : ℝ) * (A ^ 2 * (ℓ ^ (2 * c) / (K : ℝ) ^ (2 * c)))
      = (K : ℝ) / (K : ℝ) ^ (2 * c) * (A ^ 2 * ℓ ^ (2 * c)) := by ring
    _ = (K : ℝ) ^ (2 / (K : ℝ)) * (A ^ 2 * ℓ ^ (2 * c)) := by rw [hKc]
    _ ≤ 3 * (A ^ 2 * ℓ ^ (2 * c)) := mul_le_mul_of_nonneg_right h3 hA

/-! ### Jensen's inequality over the translates -/

/-- **Jensen**: `E ((M⁻¹ Σ_j Δ_j)²) ≤ M⁻¹ Σ_j E Δ_j²` for `M ≥ 1` a.e.-measurable `Δ_j`. -/
theorem lintegral_sq_average_le {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {M : ℕ} (hM : 1 ≤ M) (Δ : ℕ → Ω' → ℝ) (hΔ : ∀ j, AEMeasurable (Δ j) P') :
    ∫⁻ ω, ENNReal.ofReal (((M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, Δ j ω) ^ 2) ∂P' ≤
      (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, ∫⁻ ω, ENNReal.ofReal (Δ j ω ^ 2) ∂P' := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hpt : ∀ ω, ENNReal.ofReal (((M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, Δ j ω) ^ 2) ≤
      (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, ENNReal.ofReal (Δ j ω ^ 2) := by
    intro ω
    have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.range M) (f := fun j => Δ j ω)
    rw [Finset.card_range] at hsq
    have h : ((M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, Δ j ω) ^ 2 ≤
        (M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, Δ j ω ^ 2 := by
      rw [mul_pow, inv_pow]
      calc ((M : ℝ) ^ 2)⁻¹ * (∑ j ∈ Finset.range M, Δ j ω) ^ 2
          ≤ ((M : ℝ) ^ 2)⁻¹ * ((M : ℝ) * ∑ j ∈ Finset.range M, Δ j ω ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, Δ j ω ^ 2 := by field_simp
    refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hM0,
      ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _]
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (by exact_mod_cast hM0.ne')),
    lintegral_finsetSum' _ fun j _ => ((hΔ j).pow_const 2).ennreal_ofReal]

/-! ### The label energy of the averaged minimum -/

section Energies

variable {m : ℕ} (X : Setting.{u} m)

/-- A slab minimum from a transverse point is almost everywhere measurable. -/
theorem aemeasurable_F {b : ℝ} (hb : X.IsUpperBound b) (M : ℕ) {s : ℝ} (hs : 0 ≤ s)
    {τ : Pt m} (hτ : Pt.lon τ = 0) : AEMeasurable (X.F b M s τ) X.P := by
  obtain ⟨G, hG, hae⟩ := exists_F_version X hb M hs hτ
  exact (hG.mono (X.info_le _) le_rfl).aemeasurable.congr hae.symm

/-- **The label energy of `F̄` is at most the average of the label energies of `F`** for the
translated resamplings (proof of Lemma `lem:residual`: Jensen's inequality over the translates and
"translations by multiples of `L(nQ_n)^{1/2}e₂` map blocks to blocks"). -/
theorem labelCouplingEnergy_averagedMin_le (hm : 1 ≤ m) {b : ℝ} (hb : X.IsUpperBound b)
    {K : ℕ} (hK : 1 ≤ colCount K) {n : ℝ} (hn : 0 ≤ n) (W : ℝ) (L : ℕ) {Λ : X.LabelFamily}
    (hΛ : IsCovariantAE Λ n W L) (o : Fin K → Fin m → Fin L)
    (rcpl : (i : ℕ) → (z : Fin m → ℤ) → X.LabelResamplingData Λ n W L i z) :
    labelCouplingEnergy X n W L K Λ o rcpl (averagedMin X b K n W L) ≤
      (colCount K : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range (colCount K),
        labelCouplingEnergy X n W L K Λ o (shiftResamplings X hΛ hm j rcpl) (X.F b K n 0) := by
  rw [← Finset.sum_congr rfl fun j _ => labelCouplingEnergy_F_shift X hm b L K j hΛ o rcpl]
  set M := colCount K
  set Fj : ℕ → X.Ω → ℝ := fun j => X.F b K n (((j : ℝ) * L * W) • e₂ m)
  have hFj : ∀ j, AEMeasurable (Fj j) X.P := fun j =>
    aemeasurable_F X hb K hn (by rw [Pt.lon_smul, lon_e₂, mul_zero])
  have hblock : ∀ (i : ℕ) (z : Fin m → ℤ),
      ∫⁻ ω, ENNReal.ofReal ((averagedMin X b K n W L ((rcpl i z).new ω) -
          averagedMin X b K n W L ((rcpl i z).old ω)) ^ 2) ∂(rcpl i z).P' ≤
        (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M,
          ∫⁻ ω, ENNReal.ofReal ((Fj j ((rcpl i z).new ω) - Fj j ((rcpl i z).old ω)) ^ 2)
            ∂(rcpl i z).P' := by
    intro i z
    have hc := (rcpl i z).isLabelResampling.isBlockCoupling
    have heq : ∀ ω, averagedMin X b K n W L ((rcpl i z).new ω) -
        averagedMin X b K n W L ((rcpl i z).old ω) =
          (M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, (Fj j ((rcpl i z).new ω) - Fj j ((rcpl i z).old ω)) :=
      fun ω => by simp only [averagedMin, Fj, M, ← mul_sub, ← Finset.sum_sub_distrib]
    simp_rw [heq]
    refine lintegral_sq_average_le hK _ fun j => ?_
    have hnew : AEMeasurable (Fj j) ((rcpl i z).P'.map (rcpl i z).new) := by
      rw [hc.measurePreserving_new.map_eq]; exact hFj j
    have hold : AEMeasurable (Fj j) ((rcpl i z).P'.map (rcpl i z).old) := by
      rw [hc.measurePreserving_old.map_eq]; exact hFj j
    exact (hnew.comp_measurable hc.measurePreserving_new.measurable).sub
      (hold.comp_measurable hc.measurePreserving_old.measurable)
  unfold labelCouplingEnergy
  calc (1 / 2 : ℝ≥0∞) * ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
        ∫⁻ ω, ENNReal.ofReal ((averagedMin X b K n W L ((rcpl i z).new ω) -
          averagedMin X b K n W L ((rcpl i z).old ω)) ^ 2) ∂(rcpl i z).P'
      ≤ (1 / 2 : ℝ≥0∞) * ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
        (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M,
          ∫⁻ ω, ENNReal.ofReal ((Fj j ((rcpl i z).new ω) - Fj j ((rcpl i z).old ω)) ^ 2)
            ∂(rcpl i z).P' := by
        gcongr with i z
        exact hblock i z
    _ = (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, (1 / 2 : ℝ≥0∞) * ∑ i : Fin K,
        ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
          ∫⁻ ω, ENNReal.ofReal ((Fj j ((rcpl i z).new ω) - Fj j ((rcpl i z).old ω)) ^ 2)
            ∂(rcpl i z).P' := by
        simp_rw [ENNReal.tsum_mul_left]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        simp_rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        rw [Finset.sum_comm, mul_left_comm]

end Energies

end IsotropicVariance.Paper.Proofs.Gain
