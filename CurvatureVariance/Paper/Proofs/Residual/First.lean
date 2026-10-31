/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Residual.Near
import CurvatureVariance.Paper.Proofs.LabelResidual.Energy
import CurvatureVariance.Paper.Proofs.Gain.RRTuples
import CurvatureVariance.Paper.Proofs.Gain.Step2Tail
import CurvatureVariance.Paper.Proofs.LabelResidual.Small
import CurvatureVariance.Paper.Proofs.Responses.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:residual`: the first bound of equation `eq:residual`

The proof of Lemma `lem:residual` applies the first two paragraphs of the proof of
[AB26, Lemma 6.3], with equations `eq:rewardmoment` and `eq:blocksum` for [AB26, (6.2), (6.3)],
`ζ_t · (v − u)` for `n` and the event `E` of `Residual.Event`. The steps of the paper's proof, each
with the theorem that gives it:

* "We show that `E[(Y_i(j,k) − η|j − k|²)₊^{4d}]^{1/(4d)} ≤ η` for all `i, j, k` if `L` is large
  depending on `η`" is the hypothesis `hmom` of `exists_offsetAverage_blockEnergy_le`, proved in
  `exists_small_residualBound`, in two cases:
  - if `|j − k|` is large depending on `η`, by equation `eq:rewardmoment`
    (`lintegral_penalized_le_of_far`);
  - for `|j − k|` bounded, by `E[Y_i(j,k)^{4d}] → 0` as `L → ∞` (`Residual.Near`,
    `tendsto_nearBound`).
* "Then equation `eq:chainsum`, applied to the arrays `Y_i/η`, gives
  `E[Σ_i Y_i(x_{i−1}, x_i)] ≤ CηK`, and equation `eq:blocksum` gives the first bound":
  `exists_offsetAverage_blockEnergy_le`.

`ResidualBound`, `exists_coarse_residualBound`, `exists_small_majorant` and
`exists_residual_modulus` adapt the continuum's `IsotropicVariance.Paper.Proofs.Residual.First`
and `IsotropicVariance.Paper.Proofs.LabelResidual.UniformModulus`. As in the continuum, the paper
takes `L` large, the contract names a value `ψ'(L)` for every `L ≥ 16`, and a coarse bound fills
that gap. Here `ε` is one function of `L`, so the modulus has the one variable `L`. The continuum's
coarse bound is the second bound of equation `eq:rewardmoment`, which the implication here does not
have.
The coarse bound here is the same array step at a constant `θ`, from the first bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.Residual

open CurvatureVariance.Paper CurvatureVariance.Paper.Gain CurvatureVariance.Paper.Contracts
open CurvatureVariance.Paper.Gain.LabelResidual

variable {m : ℕ}

/-! ### Equations `eq:chainsum` and `eq:blocksum` -/

/-- **The first bound at one length** (the first paragraph of the proof of [AB26, Lemma 6.3]):
equation `eq:chainsum`, applied to the arrays `Y_i/θ`, and equation `eq:blocksum` give
`L^{−K(d−1)} Σ_a Σ_G E[(F^G − F)²] ≤ 2θCKQ_n²`, if
`E[(Y_i(j,k) − θ|j − k|²)₊^{4d}] ≤ θ^{4d}` for all `i, j, k`, the offsets being random. If no tuple
is admissible, `F` vanishes. -/
theorem exists_offsetAverage_blockEnergy_le (hS : BlockSumStatement.{0} m)
    (hC : ChainSumStatement.{0} m) (bd : Bounds m) (hbd : bd.Valid) (Cstar : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd →
    ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A → Premise M K A N → RangeA M K A N Cstar →
    ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y → ∀ L : ℕ, 1 ≤ L →
    ∀ (Pr : (Fin K → Fin m → Fin L) → Measure (Config m × Config m))
      (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ),
      IsLabelPairFamily M n (wInt M K A n) L K (targetSlope ℓ y) lam Pr →
    ∀ θ : ℝ, 0 < θ →
      (∀ (i : Fin K) (j k : Fin m → ℤ), offsetAvg (fun σ => ∫⁻ x,
          (reward M K A n (targetSlope ℓ y) Prod.fst
              (pairNew n (wInt M K A n) L (targetSlope ℓ y) (offsetOf σ)) ((i : ℕ) + 1) j k x -
            ENNReal.ofReal (θ * ‖transversePoint (j - k)‖ ^ 2)) ^ (4 * (m + 1)) ∂Pr σ) ≤
        ENNReal.ofReal (θ ^ (4 * (m + 1)))) →
      offsetAverage K L (blockEnergy M.P (fun ω => targetMin M ω n K ℓ y) n (wInt M K A n) L K
          (targetSlope ℓ y) lam) ≤
        ENNReal.ofReal (2 * θ * C * K * Q M K A n ^ 2) := by
  obtain ⟨C, hC0, hch⟩ := offsetAvg_iSup_reward_le hC bd hbd Cstar
  refine ⟨C, hC0, fun K hK => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hch K hK
  obtain ⟨N₂, hN₂⟩ := hS bd hbd Cstar K hK
  refine ⟨max N₁ N₂, ?_⟩
  intro M hM hfit N hN A hA hprem hrange n ℓ y htar L hL Pr lam hfam θ hθ hmom
  have hch' := hN₁ M hM hfit N ((le_max_left _ _).trans hN) A hA hprem hrange n ℓ y htar L hL Pr lam
    hfam θ hθ hmom
  have := hfam.prob
  have hFm : Measurable fun ω => targetMin M ω n K ℓ y := Responses.measurable_targetMin M n K ℓ y
  -- equation `eq:blocksum` at each offset
  have hσ : ∀ σ : Fin K → Fin m → Fin L,
      blockEnergy M.P (fun ω => targetMin M ω n K ℓ y) n (wInt M K A n) L K (targetSlope ℓ y) lam
        (offsetOf σ) ≤
      ENNReal.ofReal (2 * Q M K A n ^ 2) * ∫⁻ x, ⨆ (Y : Fin (K + 1) → Fin m → ℤ)
        (_ : IsMinTuple M x.1 n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y), ∑ i : Fin K,
          reward M K A n (targetSlope ℓ y) Prod.fst
            (pairNew n (wInt M K A n) L (targetSlope ℓ y) (offsetOf σ)) ((i : ℕ) + 1)
            (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.castSucc)
            (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.succ) x ∂Pr σ := by
    intro σ
    by_cases hadm : ∃ Y, IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y
    · choose x hx using fun z : Config m × Config m => exists_isMinTuple hadm z.1
      have h := hN₂ M hM hfit N ((le_max_right _ _).trans hN) A hA hprem hrange n ℓ y htar L hL
        (offsetOf σ) (fun i k => offsetOf_mem hL σ i k) (Config m × Config m) (Pr σ) Prod.fst _
        (hfam.repl σ) x (ae_of_all _ hx)
      refine le_trans (le_of_eq ?_) (h.trans (mul_le_mul' le_rfl
        (lintegral_mono fun z => le_iSup₂_of_le (x z) (hx z) le_rfl)))
      unfold blockEnergy
      refine Finset.sum_congr rfl fun i hi => tsum_congr fun g => ?_
      have hiK := Finset.mem_range.1 hi
      rw [hfam.es σ (i + 1) (by omega) (by omega) g _ hFm]
      refine lintegral_congr fun x => ?_
      rw [sub_sq_comm]
    · push Not at hadm
      have h0 : ∀ ω : Config m, targetMin M ω n K ℓ y = 0 := fun ω => by
        rw [targetMin, slabMin_eq_top_of_forall_not hadm ω, ENNReal.toReal_top]
      have h1 : blockEnergy M.P (fun ω => targetMin M ω n K ℓ y) n (wInt M K A n) L K
          (targetSlope ℓ y) lam (offsetOf σ) = 0 := by
        simp [blockEnergy, labelES, h0]
      rw [h1]
      exact bot_le
  rw [offsetAverage_eq_offsetAvg]
  have havg := mul_le_mul' (le_refl ((Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞))⁻¹)
    (Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hσ σ)
  rw [← Finset.mul_sum, mul_left_comm] at havg
  refine havg.trans ((mul_le_mul' le_rfl hch').trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-! ### The penalized moments -/

/-- **Far pairs** (the second paragraph of the proof of [AB26, Lemma 6.3]): equation
`eq:rewardmoment` gives
`E[(Y − θ a²)₊^p] ≤ (C θ^{−3} a^{−2})^p`, which is at most `θ^p` if `a` is large depending on
`θ`. -/
theorem lintegral_penalized_le_of_far {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ≥0∞} {C θ a : ℝ} (hC : 0 ≤ C) (hθ : 0 < θ) (ha : max 1 (4 * C ^ 2 / θ ^ 2) ≤ a)
    (p : ℕ) (hmom : ∫⁻ ω, Y ω ^ (4 * p) ∂μ ≤ ENNReal.ofReal ((C * (1 + a)) ^ (4 * p))) :
    ∫⁻ ω, (Y ω - ENNReal.ofReal (θ * a ^ 2)) ^ p ∂μ ≤ ENNReal.ofReal (θ ^ p) := by
  have ha1 : 1 ≤ a := (le_max_left _ _).trans ha
  have ha0 : 0 < a := by linarith only [ha1]
  refine (Gain.lintegral_tsub_pow_le hC ha1 hθ p hmom).trans (ENNReal.ofReal_le_ofReal ?_)
  refine pow_le_pow_left₀ (by positivity) ?_ p
  have h1 : 4 * C ^ 2 ≤ a * θ ^ 2 :=
    (div_le_iff₀ (by positivity)).1 ((le_max_right _ _).trans ha)
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [div_le_iff₀ (by positivity)]
  nlinarith only [h2]

/-- The value at `L` of the bound of `E[Y_i(j,k)^{4d}]` for `|j − k| ≤ D`. -/
noncomputable def nearBound (m : ℕ) (C C' D e : ℝ) (L : ℕ) : ℝ :=
  2 ^ (8 * (m + 1) + 1) * e ^ (8 * (m + 1)) + (C * (1 + D)) ^ (4 * (m + 1)) *
    (C' * (1 + D + Real.sqrt L) / L) ^ ((3 : ℝ) / 4)

/-- The bound of `Residual.Near` is at most `nearBound` for `|j − k| ≤ D`. -/
theorem ofReal_add_le_nearBound {C C' a D : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (ha : 0 ≤ a)
    (haD : a ≤ D) (e : ℝ) (L : ℕ) :
    ENNReal.ofReal (2 ^ (8 * (m + 1) + 1) * e ^ (8 * (m + 1))) +
        ENNReal.ofReal ((C * (1 + a)) ^ (4 * (m + 1))) *
          ENNReal.ofReal (C' * (1 + a + Real.sqrt L) / L) ^ ((3 : ℝ) / 4) ≤
      ENNReal.ofReal (nearBound m C C' D e L) := by
  have hsq : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hD : 0 ≤ D := ha.trans haD
  have hx : 0 ≤ C' * (1 + a + Real.sqrt L) / L := by positivity
  have hy : 0 ≤ C' * (1 + D + Real.sqrt L) / L := by positivity
  have he : 0 ≤ e ^ (8 * (m + 1)) := Even.pow_nonneg ⟨4 * (m + 1), by ring⟩ _
  rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (add_le_add le_rfl ?_)
  have h1 : (C * (1 + a)) ^ (4 * (m + 1)) ≤ (C * (1 + D)) ^ (4 * (m + 1)) :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith only [haD]) hC) _
  have h2 : (C' * (1 + a + Real.sqrt L) / L) ^ ((3 : ℝ) / 4) ≤
      (C' * (1 + D + Real.sqrt L) / L) ^ ((3 : ℝ) / 4) := by
    refine Real.rpow_le_rpow hx ?_ (by norm_num)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [haD]) hC')
      (Nat.cast_nonneg L)
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hx _) (by positivity)

/-- **`E[Y_i(j,k)^{4d}]` tends to zero as `L → ∞` for each fixed value of `|j − k|`**
(the second paragraph of the proof of [AB26, Lemma 6.3]). -/
theorem tendsto_nearBound (m : ℕ) (C : ℝ) {C' D : ℝ} (hC' : 0 ≤ C') (hD : 0 ≤ D) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun L => nearBound m C C' D (ε L) L) atTop (𝓝 0) := by
  have h1 : Tendsto (fun L => (2 : ℝ) ^ (8 * (m + 1) + 1) * ε L ^ (8 * (m + 1))) atTop (𝓝 0) := by
    have := (hε.pow (8 * (m + 1))).const_mul ((2 : ℝ) ^ (8 * (m + 1) + 1))
    rwa [zero_pow (by omega), mul_zero] at this
  have hlim : Tendsto (fun L : ℕ => C' * (2 + D) / Real.sqrt L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h2 : Tendsto (fun L : ℕ => C' * (1 + D + Real.sqrt L) / L) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun L => by positivity) ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt L := ⟨_, rfl⟩
    have hs1 : 1 ≤ s := hs ▸ Real.one_le_sqrt.mpr hL1
    have hss : s * s = L := hs ▸ Real.mul_self_sqrt (by linarith only [hL1])
    rw [← hs, ← hss, mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC'
    rw [div_le_div_iff₀ (by positivity) (by linarith only [hs1])]
    nlinarith only [mul_nonneg (show (0 : ℝ) ≤ 1 + D by linarith only [hD])
      (mul_nonneg (sub_nonneg.2 hs1) (by linarith only [hs1] : (0 : ℝ) ≤ s)), hs1,
      mul_self_nonneg s, mul_le_mul hs1 hs1 zero_le_one (by linarith only [hs1])]
  have h3 := ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 4)).tendsto 0).comp h2
  rw [Real.zero_rpow (by norm_num)] at h3
  have h4 := h3.const_mul ((C * (1 + D)) ^ (4 * (m + 1)))
  rw [mul_zero] at h4
  have := h1.add h4
  rw [add_zero] at this
  exact this

/-! ### The bound at one `L` -/

/-- The first bound of equation `eq:residual` at `L`, with the constant `c`, for the atom bound `α`
and the error `e` of the labels. -/
def ResidualBound (bd : Bounds m) (Cstar α e : ℝ) (L : ℕ) (c : ℝ) : Prop :=
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A → Premise M K A N → RangeA M K A N Cstar →
  ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
  ∀ P : Pt m, IsSubgradient M.μ (slopeVec (targetSlope ℓ y)) P →
  ∀ lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ,
    Gain.IsLabelFamily M K A L n (targetSlope ℓ y) P α e lam →
    offsetAverage K L (blockEnergy M.P (fun ω => targetMin M ω n K ℓ y) n (wInt M K A n) L K
        (targetSlope ℓ y) lam) ≤
      ENNReal.ofReal (c * K * Q M K A n ^ 2)

/-- The bound is monotone in the constant. -/
theorem ResidualBound.mono {bd : Bounds m} {Cstar α e : ℝ} {L : ℕ} {c c' : ℝ} (hc : c ≤ c')
    (h : ResidualBound bd Cstar α e L c) : ResidualBound bd Cstar α e L c' := by
  intro K hK
  obtain ⟨N₀, hN₀⟩ := h K hK
  exact ⟨N₀, fun M hM hfit N hN A hA hprem hrange n ℓ y htar P hP lam hlam =>
    (hN₀ M hM hfit N hN A hA hprem hrange n ℓ y htar P hP lam hlam).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg K)) (sq_nonneg _)))⟩

/-- A label-pair family for the labels of `Gain.IsLabelFamily`. -/
theorem exists_isLabelPairFamily {M : Model m} (hM : M.Standing) {n K L : ℕ} (hL : 1 ≤ L)
    {A : ℝ} {t : EuclideanSpace ℝ (Fin m)} {P : Pt m} {α e : ℝ}
    {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ}
    (hlam : Gain.IsLabelFamily M K A L n t P α e lam) :
    ∃ Pr, IsLabelPairFamily M n (wInt M K A n) L K t lam Pr :=
  labelPairFamiliesExist M hM n (wInt M K A n) L K hL t lam fun i hi hiK o g ho =>
    ⟨(hlam.isBlockLabel i hi hiK o g ho).dep, (hlam.isBlockLabel i hi hiK o g ho).finite,
      (hlam.isBlockLabel i hi hiK o g ho).measurableSet⟩

/-- **The first bound with a small constant** (the first two paragraphs of the proof of
[AB26, Lemma 6.3]): for `η > 0` and `L` large depending on `η`. -/
theorem exists_small_residualBound (hRM : RewardMomentStatement.{0} m)
    (hS : BlockSumStatement.{0} m) (hC : ChainSumStatement.{0} m)
    (hloc : LocalizationStatement m) (htube : TubeStatement m) (bd : Bounds m) (hbd : bd.Valid)
    (Cstar : ℝ) (α : ℕ → ℝ) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → 16 ≤ L → ResidualBound bd Cstar (α L) (ε L) L η := by
  obtain ⟨CC, hCC, hEn⟩ := exists_offsetAverage_blockEnergy_le hS hC bd hbd Cstar
  obtain ⟨CY, C', hCY, hC', hmoms⟩ := exists_reward_moments hRM hloc htube bd hbd Cstar
  -- the choices: `θ`, then the cutoff `D` of `|j − k|`, then `L`
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = min 1 (η / (2 * CC)) := ⟨_, rfl⟩
  have hθ : 0 < θ := hθdef ▸ lt_min one_pos (by positivity)
  have hθη : 2 * θ * CC ≤ η := by
    have h : θ ≤ η / (2 * CC) := hθdef ▸ min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    linarith only [h]
  obtain ⟨D, hDdef⟩ : ∃ D, D = max 1 (4 * CY ^ 2 / θ ^ 2) := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := hDdef ▸ le_max_left _ _
  have hnear := tendsto_nearBound m CY hC' (by linarith only [hD1] : 0 ≤ D) hε
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (hnear.eventually
    (ge_mem_nhds (show (0 : ℝ) < θ ^ (4 * (m + 1)) by positivity)))
  refine ⟨L₀, fun L hL hL16 K hK => ?_⟩
  have hL1 : 1 ≤ L := by omega
  obtain ⟨N₁, hN₁⟩ := hEn K hK
  obtain ⟨N₂, hN₂⟩ := hmoms K hK
  refine ⟨max N₁ N₂, ?_⟩
  intro M hM hfit N hN A hA hprem hrange n ℓ y htar P hP lam hlam
  have hN₁' : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂' : N₂ ≤ N := (le_max_right _ _).trans hN
  obtain ⟨Pr, hfam⟩ := exists_isLabelPairFamily hM hL1 hlam
  obtain ⟨h16, h4⟩ := hN₂ M hM hfit N hN₂' A hA hprem hrange n ℓ y htar L hL1 Pr lam P (α L) (ε L)
    hfam hlam
  refine (hN₁ M hM hfit N hN₁' A hA hprem hrange n ℓ y htar L hL1 Pr lam hfam θ hθ
    fun i j k => ?_).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (by simpa only [mul_right_comm] using mul_le_mul_of_nonneg_right hθη (Nat.cast_nonneg K))
      (sq_nonneg _)))
  obtain ⟨a, ha⟩ : ∃ a, a = ‖transversePoint (j - k)‖ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ norm_nonneg _
  by_cases hfar : D ≤ a
  · -- far pairs
    refine offsetAvg_le_const hL1 fun σ => ?_
    rw [← ha]
    refine lintegral_penalized_le_of_far hCY.le hθ (hDdef ▸ hfar) (4 * (m + 1)) ?_
    have e1 : 4 * (4 * (m + 1)) = 16 * (m + 1) := by ring
    rw [e1, ha]
    exact h16 σ i j k
  · -- pairs at bounded distance
    push Not at hfar
    calc offsetAvg (fun σ => ∫⁻ x, (reward M K A n (targetSlope ℓ y) Prod.fst
            (pairNew n (wInt M K A n) L (targetSlope ℓ y) (offsetOf σ)) ((i : ℕ) + 1) j k x -
          ENNReal.ofReal (θ * ‖transversePoint (j - k)‖ ^ 2)) ^ (4 * (m + 1)) ∂Pr σ)
        ≤ offsetAvg (fun σ => ∫⁻ x, reward M K A n (targetSlope ℓ y) Prod.fst
            (pairNew n (wInt M K A n) L (targetSlope ℓ y) (offsetOf σ)) ((i : ℕ) + 1) j k x ^
            (4 * (m + 1)) ∂Pr σ) := by
          refine mul_le_mul' le_rfl (Finset.sum_le_sum fun σ _ => lintegral_mono fun x => ?_)
          exact pow_le_pow_left' tsub_le_self _
      _ ≤ _ := h4 i j k
      _ ≤ ENNReal.ofReal (nearBound m CY C' D (ε L) L) :=
          ha ▸ ofReal_add_le_nearBound hCY.le hC' ha0 hfar.le (ε L) L
      _ ≤ ENNReal.ofReal (θ ^ (4 * (m + 1))) := ENNReal.ofReal_le_ofReal (hL₀ L hL)

/-- **The first bound with a constant**, for all `L`: the array step at a constant `θ`, from the
first bound of equation `eq:rewardmoment`. This one is not in the paper, which takes `L` large. The
statement names a value of `ψ'(L)` for every `L ≥ 16`. -/
theorem exists_coarse_residualBound (hRM : RewardMomentStatement.{0} m)
    (hS : BlockSumStatement.{0} m) (hC : ChainSumStatement.{0} m)
    (hloc : LocalizationStatement m) (htube : TubeStatement m) (bd : Bounds m) (hbd : bd.Valid)
    (Cstar : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ L : ℕ, 16 ≤ L → ∀ α e : ℝ, ResidualBound bd Cstar α e L c := by
  obtain ⟨CC, hCC, hEn⟩ := exists_offsetAverage_blockEnergy_le hS hC bd hbd Cstar
  obtain ⟨CY, C', hCY, hC', hmoms⟩ := exists_reward_moments hRM hloc htube bd hbd Cstar
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = max 1 (max (4 * CY ^ 2) (2 * CY)) := ⟨_, rfl⟩
  have hθ1 : 1 ≤ θ := hθdef ▸ le_max_left _ _
  have hθ0 : 0 < θ := by linarith only [hθ1]
  have hθ2 : 4 * CY ^ 2 ≤ θ := hθdef ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hθ3 : 2 * CY ≤ θ := hθdef ▸ (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨2 * θ * CC, by positivity, fun L hL16 α e K hK => ?_⟩
  have hL1 : 1 ≤ L := by omega
  obtain ⟨N₁, hN₁⟩ := hEn K hK
  obtain ⟨N₂, hN₂⟩ := hmoms K hK
  refine ⟨max N₁ N₂, ?_⟩
  intro M hM hfit N hN A hA hprem hrange n ℓ y htar P hP lam hlam
  have hN₁' : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂' : N₂ ≤ N := (le_max_right _ _).trans hN
  obtain ⟨Pr, hfam⟩ := exists_isLabelPairFamily hM hL1 hlam
  obtain ⟨h16, -⟩ := hN₂ M hM hfit N hN₂' A hA hprem hrange n ℓ y htar L hL1 Pr lam P α e hfam hlam
  refine hN₁ M hM hfit N hN₁' A hA hprem hrange n ℓ y htar L hL1 Pr lam hfam θ hθ0 fun i j k => ?_
  refine offsetAvg_le_const hL1 fun σ => ?_
  obtain ⟨a, ha⟩ : ∃ a, a = ‖transversePoint (j - k)‖ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ norm_nonneg _
  by_cases hfar : max 1 (4 * CY ^ 2 / θ ^ 2) ≤ a
  · rw [← ha]
    refine lintegral_penalized_le_of_far hCY.le hθ0 hfar (4 * (m + 1)) ?_
    have e1 : 4 * (4 * (m + 1)) = 16 * (m + 1) := by ring
    rw [e1, ha]
    exact h16 σ i j k
  · -- `a < 1`, since `4 C²/θ² ≤ 1`
    have hle : 4 * CY ^ 2 / θ ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith only [hθ1, hθ2]
    have ha1 : a ≤ 1 := by
      push Not at hfar
      exact hfar.le.trans (max_le le_rfl hle)
    refine (lintegral_mono fun x => pow_le_pow_left' tsub_le_self _).trans
      ((lintegral_reward_pow_le_of_moment (hfam.repl σ) (h16 σ i j k)).trans
        (ENNReal.ofReal_le_ofReal ?_))
    rw [← ha]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    nlinarith only [hθ3, ha1, hCY]

/-! ### The modulus -/

/-- **One modulus.** A coarse bound for every `L ≥ 16` and a bound with every positive constant for
`L` large give one `G → 0` with the bound `G(L)` at every `L ≥ 16`. Adapted from the continuum's
`IsotropicVariance.Paper.Proofs.LabelResidual.UniformModulus`, with one variable. -/
theorem exists_small_majorant (H : ℕ → ℝ → Prop) (hmono : ∀ L a b, a ≤ b → H L a → H L b)
    (hcoarse : ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 16 ≤ L → H L C)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → 16 ≤ L → H L η) :
    ∃ G : ℕ → ℝ, Tendsto G atTop (𝓝 0) ∧ ∀ L : ℕ, 16 ≤ L → H L (G L) := by
  obtain ⟨C, hC, hcoarse⟩ := hcoarse
  let S : ℕ → Set ℝ := fun L => {c | 0 ≤ c ∧ (16 ≤ L → H L c)}
  have hne (L : ℕ) : (S L).Nonempty := ⟨C, hC, hcoarse L⟩
  have hbelow (L : ℕ) : BddBelow (S L) := ⟨0, fun _ h => h.1⟩
  let G : ℕ → ℝ := fun L => sInf (S L) + 1 / ((L : ℝ) + 1)
  have hG0 (L : ℕ) : 0 ≤ G L :=
    add_nonneg (Real.sInf_nonneg fun _ h => h.1) (by positivity)
  refine ⟨G, Metric.tendsto_atTop.2 fun η hη => ?_, fun L hL => ?_⟩
  · obtain ⟨L₁, h₁⟩ := hsmall (η / 2) (by linarith only [hη])
    have hev := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (show (0 : ℝ) < η / 2 by linarith only [hη]))
    obtain ⟨L₂, h₂⟩ := eventually_atTop.1 hev
    refine ⟨max (max L₁ L₂) 16, fun L hL => ?_⟩
    have hL₁ : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
    have hL₂ : L₂ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
    have hL16 : 16 ≤ L := (le_max_right _ _).trans hL
    have hmem : η / 2 ∈ S L := ⟨by linarith only [hη], fun _ => h₁ L hL₁ hL16⟩
    have hi := csInf_le (hbelow L) hmem
    have hh := h₂ L hL₂
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hG0 L)]
    change sInf (S L) + 1 / ((L : ℝ) + 1) < η
    linarith only [hi, hh]
  · obtain ⟨c, hc, hc'⟩ := exists_lt_of_csInf_lt (hne L)
      (show sInf (S L) < G L from lt_add_of_pos_right _ (by positivity))
    exact hmono L c (G L) hc'.le (hc.2 hL)

/-- **The first bound of equation `eq:residual`, with one modulus `ψ'(L)`.** -/
theorem exists_residual_modulus (hRM : RewardMomentStatement.{0} m)
    (hS : BlockSumStatement.{0} m) (hC : ChainSumStatement.{0} m)
    (hloc : LocalizationStatement m) (htube : TubeStatement m) (bd : Bounds m) (hbd : bd.Valid)
    (Cstar : ℝ) (α : ℕ → ℝ) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ ψ' : ℕ → ℝ, Tendsto ψ' atTop (𝓝 0) ∧
      ∀ L : ℕ, 16 ≤ L → ResidualBound bd Cstar (α L) (ε L) L (ψ' L) := by
  refine exists_small_majorant (fun L c => ResidualBound bd Cstar (α L) (ε L) L c)
    (fun L a b hab h => h.mono hab) ?_
    fun η hη => exists_small_residualBound hRM hS hC hloc htube bd hbd Cstar α hε hη
  obtain ⟨c, hc, h⟩ := exists_coarse_residualBound hRM hS hC hloc htube bd hbd Cstar
  exact ⟨c, hc, fun L hL => h L hL (α L) (ε L)⟩

end CurvatureVariance.Paper.Proofs.Residual
