/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Contracts.Moments
import CurvatureVariance.Paper.Proofs.Responses.BlocksChain
import CurvatureVariance.Paper.Proofs.Responses.RadiusMoments
import CurvatureVariance.Paper.Proofs.ReplacementResponses.Arrays
import CurvatureVariance.Paper.Proofs.Gain.RRTuples
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:blocks`, the second bound of equation `eq:rewardmoment`

The proof of Lemma `lem:blocks`, which is the proof of [AB26, Lemma 6.1]. The arrays `Y_1, …, Y_K`
are independent (`ReplacementResponses.iIndepFun_rewardArrays`); the first bound of equation
`eq:rewardmoment` gives `E[(Y_i(j,k) − λ|j−k|²)₊^{4d}] ≤ λ^{4d}` for `λ = 1 + (2C)^{16d}`; equation
`eq:chainsum` (`lintegral_sup_sum_le_of_chainSum`, the arrays `Y_i/λ`, `π` the old weights) gives
`E sup ∑ᵢ Y_i(x_{i−1}, x_i) ≤ λ C K`; and equation `eq:blocksum` gives the bound.

The five moment lemmas `sub_sq_mul_le`, …, `lintegral_sub_sq_pow_le` are those of the continuum
library, in `IsotropicVariance.Paper.Proofs.Blocks` (they concern a random variable in `[0, ∞]` and
a real `r`), and `blockReplacement` is adapted from
`IsotropicVariance.Paper.Proofs.Blocks.blockReplacementStatement_of`. The versions
`exists_Y_versions` of the continuum are not needed: `Paper.reward` is already a function of the old
and the new weights on the replacement space, measurable and independent over the slabs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

namespace CurvatureVariance.Paper.Contracts

/-- `(t − r²) r⁶ ≤ t⁴` for `t ≥ 0`, `r ≥ 1`: on `t ≥ r²` the factor `t³` is at least `r⁶`. -/
lemma sub_sq_mul_le {t r : ℝ} (ht : 0 ≤ t) (hr : 1 ≤ r) : (t - r ^ 2) * r ^ 6 ≤ t ^ 4 := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  rcases le_total t (r ^ 2) with h | h
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith only [h]) (by positivity)).trans
      (by positivity)
  · have h6 : r ^ 6 ≤ t ^ 3 := by
      calc r ^ 6 = (r ^ 2) ^ 3 := by ring
        _ ≤ t ^ 3 := pow_le_pow_left₀ (sq_nonneg r) h 3
    calc (t - r ^ 2) * r ^ 6 ≤ t * t ^ 3 :=
          mul_le_mul (by linarith only [sq_nonneg r]) h6 (by positivity) ht
      _ = t ^ 4 := by ring

/-- `sub_sq_mul_le` in `[0, ∞]`, for the positive part. -/
lemma ennreal_sub_sq_mul_le (x : ℝ≥0∞) {r : ℝ} (hr : 1 ≤ r) :
    (x - ENNReal.ofReal (r ^ 2)) * ENNReal.ofReal (r ^ 6) ≤ x ^ 4 := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  · have ht : 0 ≤ x.toReal := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_sub _ (sq_nonneg r),
      ← ENNReal.ofReal_mul' (by positivity), ← ENNReal.ofReal_pow ht]
    exact ENNReal.ofReal_le_ofReal (sub_sq_mul_le ht hr)

/-- `x ≤ 1 + x⁴` in `[0, ∞]`. -/
lemma le_one_add_pow_four (x : ℝ≥0∞) : x ≤ 1 + x ^ 4 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · exact (le_self_pow₀ h (by norm_num)).trans le_add_self

/-- **The moment of `(T − r²)₊` at `r = 0`.** -/
lemma lintegral_sub_sq_pow_le_of_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C) (d : ℕ)
    (hmom : ∫⁻ ω, T ω ^ (16 * d) ∂P ≤ ENNReal.ofReal (C ^ (16 * d))) :
    ∫⁻ ω, (T ω - ENNReal.ofReal (0 ^ 2)) ^ (4 * d) ∂P ≤
      ENNReal.ofReal (1 + (2 * C) ^ (16 * d)) := by
  have hpt : ∀ ω, (T ω - ENNReal.ofReal (0 ^ 2)) ^ (4 * d) ≤ 1 + T ω ^ (16 * d) := fun ω => by
    have e : T ω ^ (16 * d) = (T ω ^ (4 * d)) ^ 4 := by
      rw [← pow_mul]
      congr 1
      ring
    rw [e]
    exact (pow_le_pow_left₀ bot_le tsub_le_self _).trans (le_one_add_pow_four _)
  have hmono : C ^ (16 * d) ≤ (2 * C) ^ (16 * d) :=
    pow_le_pow_left₀ hC (by linarith only [hC]) _
  calc ∫⁻ ω, (T ω - ENNReal.ofReal (0 ^ 2)) ^ (4 * d) ∂P
      ≤ ∫⁻ ω, (1 + T ω ^ (16 * d)) ∂P := lintegral_mono hpt
    _ = 1 + ∫⁻ ω, T ω ^ (16 * d) ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (C ^ (16 * d)) := by
        rw [ENNReal.ofReal_one]
        gcongr
    _ ≤ ENNReal.ofReal (1 + (2 * C) ^ (16 * d)) := by
        rw [← ENNReal.ofReal_add zero_le_one (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith only [hmono])

/-- **The moment of `(T − r²)₊` at `r ≥ 1`**: the display after [AB26, (6.3)], to the power `4d`,
with `|j − k|⁻⁸ᵈ ≤ 1`. -/
lemma lintegral_sub_sq_pow_le_of_one_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ≥0∞} {C r : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r) (d : ℕ)
    (hmom : ∫⁻ ω, T ω ^ (16 * d) ∂P ≤ ENNReal.ofReal ((C * (1 + r)) ^ (16 * d))) :
    ∫⁻ ω, (T ω - ENNReal.ofReal (r ^ 2)) ^ (4 * d) ∂P ≤
      ENNReal.ofReal (1 + (2 * C) ^ (16 * d)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hρ : 0 < (r ^ 6) ^ (4 * d) := by positivity
  set w : ℝ := ((r ^ 6) ^ (4 * d))⁻¹ with hw
  have hw0 : 0 ≤ w := (inv_pos.mpr hρ).le
  have hw1 : ENNReal.ofReal w * ENNReal.ofReal ((r ^ 6) ^ (4 * d)) = 1 := by
    rw [← ENNReal.ofReal_mul hw0, hw, inv_mul_cancel₀ hρ.ne', ENNReal.ofReal_one]
  have hpt : ∀ ω, (T ω - ENNReal.ofReal (r ^ 2)) ^ (4 * d) ≤ ENNReal.ofReal w * T ω ^ (16 * d) := by
    intro ω
    have h := pow_le_pow_left₀ bot_le (ennreal_sub_sq_mul_le (T ω) hr) (4 * d)
    have e : (T ω ^ 4) ^ (4 * d) = T ω ^ (16 * d) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [mul_pow, e, ← ENNReal.ofReal_pow (by positivity)] at h
    calc (T ω - ENNReal.ofReal (r ^ 2)) ^ (4 * d)
        = ENNReal.ofReal w * ((T ω - ENNReal.ofReal (r ^ 2)) ^ (4 * d) *
            ENNReal.ofReal ((r ^ 6) ^ (4 * d))) := by
          rw [mul_left_comm, hw1, mul_one]
      _ ≤ ENNReal.ofReal w * T ω ^ (16 * d) := by gcongr
  have hreal : w * (C * (1 + r)) ^ (16 * d) ≤ (2 * C) ^ (16 * d) := by
    have h₁ : (C * (1 + r)) ^ (16 * d) ≤ (2 * C) ^ (16 * d) * r ^ (16 * d) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have := mul_le_mul_of_nonneg_left hr hC
      linarith only [this]
    have h₂ : r ^ (16 * d) ≤ (r ^ 6) ^ (4 * d) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hr (by omega)
    calc w * (C * (1 + r)) ^ (16 * d)
        ≤ w * ((2 * C) ^ (16 * d) * (r ^ 6) ^ (4 * d)) := by
          refine mul_le_mul_of_nonneg_left (h₁.trans ?_) hw0
          exact mul_le_mul_of_nonneg_left h₂ (by positivity)
      _ = (2 * C) ^ (16 * d) := by
          rw [hw]
          field_simp
  calc ∫⁻ ω, (T ω - ENNReal.ofReal (r ^ 2)) ^ (4 * d) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal w * T ω ^ (16 * d) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal w * ∫⁻ ω, T ω ^ (16 * d) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal w * ENNReal.ofReal ((C * (1 + r)) ^ (16 * d)) := by gcongr
    _ = ENNReal.ofReal (w * (C * (1 + r)) ^ (16 * d)) := (ENNReal.ofReal_mul hw0).symm
    _ ≤ ENNReal.ofReal (1 + (2 * C) ^ (16 * d)) :=
        ENNReal.ofReal_le_ofReal (by linarith only [hreal])

/-- **The moment of `(T − r²)₊`**, for `r = 0` or `r ≥ 1`, from `E[T^{16d}] ≤ (C(1 + r))^{16d}`. -/
theorem lintegral_sub_sq_pow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ≥0∞} {C r : ℝ} (hC : 0 ≤ C) (hr : r = 0 ∨ 1 ≤ r) (d : ℕ)
    (hmom : ∫⁻ ω, T ω ^ (16 * d) ∂P ≤ ENNReal.ofReal ((C * (1 + r)) ^ (16 * d))) :
    ∫⁻ ω, (T ω - ENNReal.ofReal (r ^ 2)) ^ (4 * d) ∂P ≤
      ENNReal.ofReal (1 + (2 * C) ^ (16 * d)) := by
  rcases hr with rfl | hr
  · simp only [add_zero, mul_one] at hmom
    exact lintegral_sub_sq_pow_le_of_zero hC d hmom
  · exact lintegral_sub_sq_pow_le_of_one_le hC hr d hmom

/-- The constant `1 + (2C)^{16d}` of the moment bound, `d = m + 1`. -/
noncomputable def arrayConst (m : ℕ) (C : ℝ) : ℝ := 1 + (2 * C) ^ (16 * (m + 1))

lemma one_le_arrayConst (m : ℕ) {C : ℝ} (hC : 0 ≤ C) : 1 ≤ arrayConst m C := by
  have : 0 ≤ (2 * C) ^ (16 * (m + 1)) := by positivity
  unfold arrayConst
  linarith only [this]

/-- **Lemma `lem:blocks`, the second bound of equation `eq:rewardmoment`**, from the first bound,
equation `eq:blocksum` and equation `eq:chainsum`, as in the proof of Lemma `lem:blocks`. No
`ChainsExist` is used: if no tuple is admissible, `F ≡ 0`. -/
theorem blockReplacement {m : ℕ} (hM : RewardMomentStatement.{0} m)
    (hS : BlockSumStatement.{0} m) (hC : ChainSumStatement.{0} m) :
    BlockReplacementStatement.{0} m := by
  classical
  intro bd hbd Cstar
  obtain ⟨CY, hCY, HY⟩ := hM bd hbd Cstar
  obtain ⟨C₀, hC₀, HC⟩ := lintegral_sup_sum_le_of_chainSum hC bd hbd Cstar
  have hD1 : 1 ≤ arrayConst m CY := one_le_arrayConst m hCY.le
  have hD0 : 0 < arrayConst m CY := zero_lt_one.trans_le hD1
  refine ⟨2 * (arrayConst m CY * C₀), by positivity, fun K hK => ?_⟩
  obtain ⟨NY, hNY⟩ := HY K hK
  obtain ⟨NC, hNC⟩ := HC K hK
  obtain ⟨NS, hNS⟩ := hS bd hbd Cstar K hK
  refine ⟨max (max NY NC) NS, fun M hM' hfit N hN A hA hprem hrange n ℓ y htar L hL o ho Ω _ Pr
    old new hR => ?_⟩
  have hNY' : NY ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNC' : NC ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNS' : NS ≤ N := (le_max_right _ _).trans hN
  have : IsProbabilityMeasure Pr := hR.prob
  by_cases hadm : ∃ Y, IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y
  swap
  · -- no admissible tuple: `F ≡ 0`
    push Not at hadm
    have h0 : ∀ ω' : Config m, targetMin M ω' n K ℓ y = 0 := fun ω' => by
      have htop := Gain.slabMin_eq_top_of_forall_not hadm ω'
      rw [targetMin, htop, ENNReal.toReal_top]
    simp [h0]
  -- the selection of a minimizing chain
  let x : Ω → Fin (K + 1) → Fin m → ℤ := fun ω =>
    (Gain.exists_isMinTuple hadm (old ω)).choose
  have hx : ∀ ω, IsMinTuple M (old ω) n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) (x ω) := fun ω =>
    (Gain.exists_isMinTuple hadm (old ω)).choose_spec
  have hsum := hNS M hM' hfit N hNS' A hA hprem hrange n ℓ y htar L hL o ho Ω Pr old new hR x
    (ae_of_all _ hx)
  -- equation `eq:chainsum` for the arrays `Y_i / λ`
  set lam := arrayConst m CY with hlam
  have hmom : ∀ (i : Fin K) (j k : Fin m → ℤ), ∫⁻ ω,
      (reward M K A n (targetSlope ℓ y) old new ((i : ℕ) + 1) j k ω -
        ENNReal.ofReal (lam * ‖transversePoint (j - k)‖ ^ 2)) ^ (4 * (m + 1)) ∂Pr ≤
      ENNReal.ofReal (lam ^ (4 * (m + 1))) := fun i j k => by
    have h := lintegral_sub_sq_pow_le hCY.le
      (Responses.norm_transversePoint_zero_or_one_le (j - k)) (m + 1)
      (hNY M hM' hfit N hNY' A hA hprem hrange n ℓ y htar L hL o ho Ω Pr old new hR
        ((i : ℕ) + 1) (by omega) (by omega) j k)
    have hle : ENNReal.ofReal (‖transversePoint (j - k)‖ ^ 2) ≤
        ENNReal.ofReal (lam * ‖transversePoint (j - k)‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left (sq_nonneg _) hD1)
    exact (lintegral_mono fun ω => pow_le_pow_left₀ bot_le (tsub_le_tsub_left hle _) _).trans
      (h.trans (ENNReal.ofReal_le_ofReal (le_self_pow₀ hD1 (by omega))))
  have hchain := hNC M hM' hfit N hNC' A hA hprem hrange n ℓ y htar Ω Pr old
    ⟨hR.measurable_old, hR.law_old⟩ lam hD0
    (fun (i : Fin K) ω j k => reward M K A n (targetSlope ℓ y) old new ((i : ℕ) + 1) j k ω)
    (fun i j k => ReplacementResponses.measurable_reward M K A n (targetSlope ℓ y)
      hR.measurable_old hR.measurable_new ((i : ℕ) + 1) j k)
    (ReplacementResponses.iIndepFun_rewardArrays hR) hmom
  have hsel : ∫⁻ ω, ∑ i : Fin K, reward M K A n (targetSlope ℓ y) old new ((i : ℕ) + 1)
      (tupleIndex n (wInt M K A n) (targetSlope ℓ y) (x ω) i.castSucc)
      (tupleIndex n (wInt M K A n) (targetSlope ℓ y) (x ω) i.succ) ω ∂Pr ≤
      ENNReal.ofReal (lam * (C₀ * K)) :=
    (lintegral_mono fun ω => le_iSup₂_of_le (x ω) (hx ω) le_rfl).trans hchain
  refine hsum.trans ((mul_le_mul' le_rfl hsel).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end CurvatureVariance.Paper.Contracts
