/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Contracts.Responses
public import CurvatureVariance.Paper.Proofs.Residual.Event
import CurvatureVariance.Paper.Proofs.LabelResidual.Small
import CurvatureVariance.Paper.Proofs.LabelResidual.SmallTail
import CurvatureVariance.Paper.Proofs.Responses.RowCubes
import CurvatureVariance.Paper.Proofs.Responses.RowGeometry
import CurvatureVariance.Paper.Proofs.Responses.SlabArrays
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Paper.Proofs.Responses.WidthBridge
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:residual`: the moments of `Y_i(j,k)`, from the contracts

The proof of Lemma `lem:residual`: "Lemma `lem:localization` and Markov's inequality give
`P[E] ≤ C(1 + |j − k| + L^{1/2})/L`". With `Residual.Event`, this bounds `E[Y_i(j,k)^{4d}]`, for
`|j − k|` fixed and `L` large (the second paragraph of the proof of [AB26, Lemma 6.3]).

* `exists_measure_slabRadius_gt_le`: `P[R_i(j,k) > r] ≤ C/r` on the retained pairs, for every
  `r > 0`, by Lemma `lem:localization` at `p = 1` and Markov's inequality.
* `tail_add_offsetFraction_le`: the arithmetic of `P[E]`.
* `exists_reward_moments`: `E[Y_i(j,k)^{16d}] ≤ (C(1 + |j − k|))^{16d}` (equation `eq:rewardmoment`)
  and
  `E[Y_i(j,k)^{4d}] ≤ 2^{8d+1} ε^{8d} + (C(1 + |j − k|))^{4d} (C(1 + |j − k| + L^{1/2})/L)^{3/4}`,
  the offsets being random.

Equation `eq:scales` is not needed: the slope of a retained pair needs only that `n` is large.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.Residual

open CurvatureVariance.Paper CurvatureVariance.Paper.Gain CurvatureVariance.Paper.Contracts
open CurvatureVariance.Paper.Gain.LabelResidual

variable {m : ℕ}

/-- `16 m^{1/2} ≤ n^{3/4+δ/100}` for `n ≥ 256m`. -/
theorem sixteen_sqrt_le_rpow {m n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hn : 256 * m ≤ n) (hn1 : 1 ≤ n) :
    16 * Real.sqrt m ≤ (n : ℝ) ^ ((3 : ℝ) / 4 + δ / 100) := by
  have hn' : (256 * m : ℝ) ≤ n := by exact_mod_cast hn
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsq : (16 * Real.sqrt m) ^ 2 ≤ n := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    linarith only [hn']
  refine (Real.le_sqrt_of_sq_le hsq).trans ?_
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hn1' (by linarith only [hδ])

/-- **The tail of `R_i(j,k)`** (the proof of Lemma `lem:residual`): Lemma `lem:localization` and
Markov's inequality. For every `C_d ≥ 0` there is `C > 0`, chosen before `K`, `N`, `A` and the
target, such that for `N` large, every slab, every retained pair and every `r > 0`,
`P[R_i(j,k) > r] ≤ C/r`. -/
theorem exists_measure_slabRadius_gt_le (hloc : LocalizationStatement m) (bd : Bounds m)
    (hbd : bd.Valid) (Cstar : ℝ) {Cd : ℝ} (hCd : 0 ≤ Cd) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd →
    ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A → Premise M K A N → RangeA M K A N Cstar →
    ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
    ∀ i : ℕ, 1 ≤ i → i ≤ K → ∀ j k : Fin m → ℤ, IsRetainedPair M n (wInt M K A n) j k →
    ∀ r : ℝ, 0 < r →
      M.P {ω | ENNReal.ofReal r < slabRadius M K A Cd ω n (targetSlope ℓ y) i j k} ≤
        ENNReal.ofReal (C / r) := by
  obtain ⟨Cr, hCr, hRd⟩ := hloc bd hbd Cstar 1 le_rfl 1 le_rfl
  refine ⟨(2 * Cd + 1) * max 1 Cr,
    mul_pos (by positivity) (lt_of_lt_of_le one_pos (le_max_left _ _)), fun K hK => ?_⟩
  have hK1 : 1 ≤ K := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  obtain ⟨NR, hNR⟩ := hRd (1 / (9 * K)) (by positivity) K hK
  refine ⟨max ((9 * K) ^ 2) (max NR ((256 * m) ^ 2)), ?_⟩
  intro M hM hfit N hN A hA hprem hrange n ℓ y htar i hi1 hiK j k hjk r hr
  have hN₁ : (9 * K) ^ 2 ≤ N := (le_max_left _ _).trans hN
  have hN₂ : NR ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₃ : (256 * m) ^ 2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hn, hsqrt, -, -⟩ := Responses.target_size_bounds hK1 hN₁ htar
  set t := targetSlope ℓ y with ht
  set w := wInt M K A n with hw
  have hδ := hM.delta_pos
  have hn256 : 256 * m ≤ n := by
    have h1 : ((256 * m : ℕ) : ℝ) ^ 2 ≤ N := by exact_mod_cast hN₃
    have h2 := (Real.le_sqrt_of_sq_le h1).trans hsqrt
    exact_mod_cast h2
  have hexp : 1 + (M.δ / 100 - 1 / 4) = (3 : ℝ) / 4 + M.δ / 100 := by ring
  have hround : 16 * Real.sqrt m ≤ (n : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) := by
    rw [hexp]
    exact sixteen_sqrt_le_rpow hδ.le hn256 (by omega)
  have hjk' : (w : ℝ) * ‖transversePoint (k - j)‖ ≤ (n : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) / 8 := by
    rw [hexp]
    have h := hjk
    unfold IsRetainedPair at h
    linarith only [h]
  have htn := Responses.targetSlope_norm_le_half hM hK (by omega) htar.1 htar.2.2.2
  have hslope := Responses.rowPairSlope_norm_le (by omega : 1 ≤ n) t ((i : ℤ) - 1) j k
    htn hjk' hround
  have hwpos : 1 ≤ w := Responses.one_le_wInt (M := M) (K := K) hA (by omega : 1 ≤ n)
  have hpair := Responses.isCubePair_rows (M := M) (K := K) (A := A) (b := 1) (by omega : 1 ≤ n)
    hwpos (by simpa only [one_mul] using Responses.wInt_sub_one_le_W M K A n) t ((i : ℤ) - 1) j k
  simp only [sub_add_cancel] at hpair
  have hnlo : 1 / (9 * (K : ℝ)) * N ≤ n := by
    have h := htar.2.1
    rw [htar.1, Nat.cast_mul] at h
    apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 9 * K by positivity)).mp
    field_simp
    nlinarith only [h]
  have hnN : n ≤ N := by
    have hnℓ : n ≤ ℓ := by rw [htar.1]; exact Nat.le_mul_of_pos_left n (by omega)
    exact hnℓ.trans htar.2.2.1
  -- Lemma `lem:localization` at `p = 1`
  have hRmom := (hNR M hM hfit N hN₂ A hA hprem hrange n hnlo hnN _ _ _ hpair hslope).2
    (((i : ℤ) - 1) * n) (fun u hu => hu.1)
  have hface : ((i : ℤ) - 1) * n + n = (i : ℤ) * n := by ring
  rw [hface] at hRmom
  simp only [ENNReal.rpow_one] at hRmom
  have := hM.probP
  have hmark := measure_ofReal_lt_radius_le (q := 1) (C₃ := Cr) hCd
    (Responses.measurable_locRadiusSlab (((i : ℤ) - 1) * n) ((i : ℤ) * n)
      (rowCube n w t ((i : ℤ) - 1) j) (rowCube n w t i k) (W M K A n))
    (by simpa only [pow_one] using hRmom) hr
  refine hmark.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [Nat.cast_one, pow_one, pow_one, Real.rpow_neg_one, div_eq_mul_inv]

/-- The arithmetic of `P[E] ≤ C(1 + |j − k| + L^{1/2})/L`. -/
theorem tail_add_offsetFraction_le {m L : ℕ} (hL : 1 ≤ L) {Cr a : ℝ} (hCr : 0 ≤ Cr) (ha : 0 ≤ a) :
    Cr / Real.sqrt L + offsetFraction m L ((Real.sqrt m + 1) * (1 + a + Real.sqrt L)) ≤
      (Cr + m * (2 * Real.sqrt m + 7)) * (1 + a + Real.sqrt L) / L := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt L := ⟨_, rfl⟩
  rw [← hs]
  have hs0 : 0 < s := hs ▸ Real.sqrt_pos.2 hL0
  have hss : s * s = L := hs ▸ Real.mul_self_sqrt hL0.le
  obtain ⟨u, hu⟩ : ∃ u, u = 1 + a + s := ⟨_, rfl⟩
  rw [← hu]
  have hu1 : s ≤ u := by linarith only [hu, ha]
  have hu2 : 1 ≤ u := by linarith only [hu, ha, hs0]
  have h1 : Cr / s ≤ Cr * u / L := by
    rw [div_le_div_iff₀ hs0 hL0, ← hss]
    have := mul_le_mul_of_nonneg_left hu1 (mul_nonneg hCr hs0.le)
    linarith only [this]
  have hc1 := (Int.ceil_lt_add_one (2 * ((Real.sqrt m + 1) * u))).le
  have hc2 : (⌈Real.sqrt L⌉₊ : ℝ) ≤ s + 1 := hs ▸ (Nat.ceil_lt_add_one hs0.le |>.le)
  have h2 : offsetFraction m L ((Real.sqrt m + 1) * u) ≤ m * (2 * Real.sqrt m + 7) * u / L := by
    unfold offsetFraction
    rw [mul_assoc]
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)) hL0.le
    linarith only [hc1, hc2, hu1, hu2, mul_comm (2 * Real.sqrt m + 7) u,
      mul_add (2 : ℝ) (Real.sqrt m) 1]
  have h3 : (Cr + m * (2 * Real.sqrt m + 7)) * u / L =
      Cr * u / L + m * (2 * Real.sqrt m + 7) * u / L := by ring
  rw [h3]
  linarith only [h1, h2]

/-- **The moments of `Y_i(j,k)`, from the contracts** (the second paragraph of the proof of
[AB26, Lemma 6.3], and the proof of Lemma `lem:residual`). There are `C` and `C'`, chosen before
`K`, `L`, `N`, `A` and the target, such that for `N` large depending only on `K`, every target,
every `L ≥ 1`, and all replacements at the offsets `σ` given a family of labels at the error `e`:

* `E[Y_i(j,k)^{16d}] ≤ (C(1 + |j − k|))^{16d}` (equation `eq:rewardmoment`), at each offset;
* `E[Y_i(j,k)^{4d}] ≤ 2^{8d+1} e^{8d} + (C(1 + |j − k|))^{4d} (C'(1 + |j − k| + L^{1/2})/L)^{3/4}`,
  the offsets being random. -/
theorem exists_reward_moments (hRM : RewardMomentStatement.{0} m)
    (hloc : LocalizationStatement m) (htube : TubeStatement m) (bd : Bounds m) (hbd : bd.Valid)
    (Cstar : ℝ) :
    ∃ C C' : ℝ, 0 < C ∧ 0 ≤ C' ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ, ∀ M : Model m, M.Standing →
    M.Fits bd → ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A → Premise M K A N → RangeA M K A N Cstar →
    ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y → ∀ L : ℕ, 1 ≤ L →
    ∀ (Pr : (Fin K → Fin m → Fin L) → Measure (Config m × Config m))
      (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ) (P : Pt m)
      (α e : ℝ),
      IsLabelPairFamily M n (wInt M K A n) L K (targetSlope ℓ y) lam Pr →
      Gain.IsLabelFamily M K A L n (targetSlope ℓ y) P α e lam →
      (∀ σ (i : Fin K) (j k : Fin m → ℤ), ∫⁻ x, reward M K A n (targetSlope ℓ y) Prod.fst
          (pairNew n (wInt M K A n) L (targetSlope ℓ y) (offsetOf σ)) ((i : ℕ) + 1) j k x ^
          (16 * (m + 1)) ∂Pr σ ≤
        ENNReal.ofReal ((C * (1 + ‖transversePoint (j - k)‖)) ^ (16 * (m + 1)))) ∧
      ∀ (i : Fin K) (j k : Fin m → ℤ), offsetAvg (fun σ => ∫⁻ x, reward M K A n (targetSlope ℓ y)
          Prod.fst (pairNew n (wInt M K A n) L (targetSlope ℓ y) (offsetOf σ)) ((i : ℕ) + 1) j k x ^
          (4 * (m + 1)) ∂Pr σ) ≤
        ENNReal.ofReal (2 ^ (8 * (m + 1) + 1) * e ^ (8 * (m + 1))) +
          ENNReal.ofReal ((C * (1 + ‖transversePoint (j - k)‖)) ^ (4 * (m + 1))) *
            ENNReal.ofReal (C' * (1 + ‖transversePoint (j - k)‖ + Real.sqrt L) / L) ^
              ((3 : ℝ) / 4) := by
  obtain ⟨Cd, hCd, hgeoall⟩ := ae_slabGeodesic_tube_of htube (bd.T + 1)
    (by linarith only [hbd.T_nonneg])
  obtain ⟨C, hC, hRMC⟩ := hRM bd hbd Cstar
  obtain ⟨Cr, hCr, htail⟩ := exists_measure_slabRadius_gt_le hloc bd hbd Cstar hCd
  have hC' : 0 ≤ Cr + m * (2 * Real.sqrt m + 7) := by positivity
  refine ⟨C, _, hC, hC', fun K hK => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hRMC K hK
  obtain ⟨N₂, hN₂⟩ := htail K hK
  refine ⟨max ((9 * K) ^ 2) (max N₁ N₂), ?_⟩
  intro M hM hfit N hN A hA hprem hrange n ℓ y htar L hL Pr lam P α e hfam hlam
  have hN₁' : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂' : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hmom : ∀ (σ : Fin K → Fin m → Fin L) (i : Fin K) (j k : Fin m → ℤ), ∫⁻ x,
      reward M K A n (targetSlope ℓ y) Prod.fst
      (pairNew n (wInt M K A n) L (targetSlope ℓ y) (offsetOf σ)) ((i : ℕ) + 1) j k x ^
      (16 * (m + 1)) ∂Pr σ ≤
      ENNReal.ofReal ((C * (1 + ‖transversePoint (j - k)‖)) ^ (16 * (m + 1))) :=
    fun σ i j k => hN₁ M hM hfit N hN₁' A hA hprem hrange n ℓ y htar L hL (offsetOf σ)
      (fun i k => offsetOf_mem hL σ i k) (Config m × Config m) (Pr σ) Prod.fst _ (hfam.repl σ)
      ((i : ℕ) + 1) (by omega) (by omega) j k
  refine ⟨hmom, fun i j k => ?_⟩
  by_cases hret : IsRetainedPair M n (wInt M K A n) j k
  swap
  · -- outside the retained pairs the reward vanishes
    have h0 : ∀ (σ : Fin K → Fin m → Fin L) x, reward M K A n (targetSlope ℓ y) Prod.fst
        (pairNew n (wInt M K A n) L (targetSlope ℓ y) (offsetOf σ)) ((i : ℕ) + 1) j k x = 0 :=
      fun σ x => by simp only [reward, hret, ite_false]
    simp only [h0, zero_pow (show 4 * (m + 1) ≠ 0 by omega), lintegral_zero, offsetAvg,
      Finset.sum_const_zero, mul_zero]
    exact bot_le
  obtain ⟨hn, -, -, -⟩ := Responses.target_size_bounds (by omega : 1 ≤ K)
    ((le_max_left _ _).trans hN) htar
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hQ : 0 < Q M K A n :=
    mul_pos (lt_of_lt_of_le zero_lt_one hA) (Real.rpow_pos_of_pos hnpos _)
  have hw : 0 < wInt M K A n := Responses.one_le_wInt (M := M) (K := K) hA (by omega : 1 ≤ n)
  have htn := Responses.targetSlope_norm_le_half hM hK (by omega) htar.1 htar.2.2.2
  have hepow : (n : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ n by omega))
    linarith only [hM.delta_le_one]
  have ht1 : ‖targetSlope ℓ y‖ ≤ bd.T + 1 := by
    have h1 := norm_add_le (targetSlope ℓ y - M.t₀) M.t₀
    rw [sub_add_cancel] at h1
    linarith only [htn, hepow, h1, hfit.t₀_le]
  obtain ⟨a, ha⟩ : ∃ a, a = ‖transversePoint (j - k)‖ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ norm_nonneg _
  have hsqm := Real.sqrt_nonneg (m : ℝ)
  have hsqL := Real.sqrt_nonneg (L : ℝ)
  obtain ⟨r, hr⟩ : ∃ r, r = (Real.sqrt m + 1) * (1 + a + Real.sqrt L) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := hr ▸ by positivity
  have hrL : ‖transversePoint (j - k)‖ + Real.sqrt L ≤ r := by
    rw [← ha, hr]
    nlinarith only [mul_nonneg hsqm ha0, mul_nonneg hsqm hsqL, hsqm]
  have hrm : ‖transversePoint (j - k)‖ + Real.sqrt m ≤ r := by
    rw [← ha, hr]
    nlinarith only [mul_nonneg hsqm ha0, mul_nonneg hsqm hsqL, hsqm, ha0, hsqL]
  have := hfam.prob
  have hmain := offsetAvg_reward_pow_le (t := targetSlope ℓ y) (Cd := Cd) hL hfam hQ hw
    (fun i hi hiK o g ho => hlam.isBlockLabel i hi hiK o g ho) i
    (hgeoall M hM K A hA n hn _ ht1 ((i : ℕ) + 1) (by omega) j k)
    (hmom · i j k) hrL hrm
  refine hmain.trans (add_le_add le_rfl
    (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num))))
  refine (measure_residualEvent_le hL (fun σ => (hfam.repl σ).law_old) i j k hr0).trans ?_
  have hLs : 0 < Real.sqrt L := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < L by omega))
  have hfrac0 : 0 ≤ offsetFraction m L r := by
    have h2r : (0 : ℤ) ≤ ⌈2 * r⌉ := Int.ceil_nonneg (by positivity)
    have h2r' : (0 : ℝ) ≤ ((⌈2 * r⌉ : ℤ) : ℝ) := by exact_mod_cast h2r
    unfold offsetFraction
    positivity
  refine (add_le_add (hN₂ M hM hfit N hN₂' A hA hprem hrange n ℓ y htar ((i : ℕ) + 1) (by omega)
    (by omega) j k hret (Real.sqrt L) hLs) le_rfl).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) hfrac0, ← ha]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hr]
  exact tail_add_offsetFraction_le hL hCr.le ha0

end CurvatureVariance.Paper.Proofs.Residual
