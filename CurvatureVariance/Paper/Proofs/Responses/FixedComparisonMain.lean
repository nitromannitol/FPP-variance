/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Contracts.Responses
import CurvatureVariance.Paper.Proofs.Responses.UniformFourth
import CurvatureVariance.Paper.Proofs.Responses.Exceptional
import CurvatureVariance.Paper.Proofs.Responses.ComparisonAsymptotics
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Paper.Proofs.Responses.FixedComparison
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Equation `eq:fixedcomparison`

Equation `eq:fixedcomparison`: `‖F − T(0,(ℓ,y))‖₂ ≤ C K log²N`. It follows from Lemma `lem:slabs`
(2) with `S = log N` on the good event `𝒢_N(log N)`, and from Hölder's inequality and the moments of
the bound `F ≤ ∑ T^{(i)}` off it. The tuple of the bound is the admissible tuple of the first clause
of `ChainsExistStatement` (the second clause, the rounded increments, is not used: the fourth moment
bound `target_difference_four_le` takes any admissible tuple). The good event has
`1_{𝒢ᶜ} ≤ O₂(C/log N)`, so its fourth norm is at most `(exp(log²N/C²) − 1)^{-1/4}`, which beats the
`O(N)` norm of `F − T`.

The fourth-moment estimate and Hölder step are `Responses.target_difference_four_le` and
`Responses.eLpNorm_two_le_good_add_four_mul`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Responses

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- An `O₂(θ)` indicator has fourth norm at most `(exp(θ⁻²) − 1)^{-1/4}`. -/
theorem indicator_eLpNorm_four_le_exp [IsProbabilityMeasure P] (G : Set Ω) (θ : ℝ) (hθ : 0 < θ)
    (hG : CurvatureVariance.IsOs P 2 θ (Gᶜ.indicator fun _ => (1 : ℝ))) :
    eLpNorm (Gᶜ.indicator fun _ => (1 : ℝ)) 4 P ≤
      ENNReal.ofReal ((Real.exp ((θ ^ 2)⁻¹) - 1)⁻¹ ^ (1 / 4 : ℝ)) := by
  set c : ℝ := Real.exp ((θ ^ 2)⁻¹) - 1 with hc
  have hc0 : 0 < c := by
    have : 0 < (θ ^ 2)⁻¹ := by positivity
    have := Real.add_one_lt_exp this.ne'
    rw [hc]; linarith
  have hpt : ∀ ω, ENNReal.ofReal c * ENNReal.ofReal ((Gᶜ.indicator fun _ => (1 : ℝ)) ω) + 1 ≤
      ENNReal.ofReal (Real.exp ((max ((Gᶜ.indicator fun _ => (1 : ℝ)) ω) 0 / θ) ^ (2 : ℝ))) := by
    intro ω
    by_cases hω : ω ∈ Gᶜ
    · simp only [Set.indicator_of_mem hω, ENNReal.ofReal_one, mul_one, max_eq_left zero_le_one]
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hc0.le zero_le_one]
      apply ENNReal.ofReal_le_ofReal
      have : (1 / θ) ^ (2 : ℝ) = (θ ^ 2)⁻¹ := by
        rw [Real.rpow_two]; field_simp
      rw [this, hc]; linarith
    · simp only [Set.indicator_of_notMem hω, ENNReal.ofReal_zero, mul_zero, zero_add, max_self,
        zero_div]
      rw [Real.zero_rpow (by norm_num), Real.exp_zero, ENNReal.ofReal_one]
  have hint : ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal ((Gᶜ.indicator fun _ => (1 : ℝ)) ω) ∂P + 1 ≤ 2 := by
    calc _ = ∫⁻ ω, (ENNReal.ofReal c * ENNReal.ofReal ((Gᶜ.indicator fun _ => (1 : ℝ)) ω) + 1) ∂P := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp ((max ((Gᶜ.indicator fun _ => (1 : ℝ)) ω) 0 / θ) ^ (2 : ℝ))) ∂P :=
          lintegral_mono hpt
      _ ≤ 2 := hG.2
  have hI : ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal ((Gᶜ.indicator fun _ => (1 : ℝ)) ω) ∂P ≤ 1 := by
    have h2 : (2 : ℝ≥0∞) = 1 + 1 := by norm_num
    rw [h2] at hint
    exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp hint
  have heq : (fun ω => ‖(Gᶜ.indicator fun _ => (1 : ℝ)) ω‖ₑ ^ (4 : ℝ)) =
      fun ω => ENNReal.ofReal ((Gᶜ.indicator fun _ => (1 : ℝ)) ω) := by
    funext ω
    by_cases hω : ω ∈ Gᶜ
    · simp only [Set.indicator_of_mem hω, enorm_one, ENNReal.one_rpow, ENNReal.ofReal_one]
    · simp only [Set.indicator_of_notMem hω, enorm_zero, ENNReal.ofReal_zero]
      norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hG.1.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  rw [heq]
  have hI' : ∫⁻ ω, ENNReal.ofReal ((Gᶜ.indicator fun _ => (1 : ℝ)) ω) ∂P ≤ ENNReal.ofReal c⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hc0]
    rw [ENNReal.le_inv_iff_mul_le, mul_comm]
    exact hI
  calc _ ≤ ENNReal.ofReal c⁻¹ ^ (1 / 4 : ℝ) := ENNReal.rpow_le_rpow hI' (by norm_num)
    _ = _ := ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hc0.le) (by norm_num)

end CurvatureVariance.Paper.Responses

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper.Responses

/-- **Equation `eq:fixedcomparison`**, from Lemmas `lem:good` and `lem:slabs` (2) at `S = log N`,
and the chain of the rounded points off the event. -/
theorem fixedComparison {m : ℕ} (hgood : GoodStatement m) (hslabs : SlabsStatement m)
    (hchains : ChainsExistStatement m) : FixedComparisonStatement m := by
  intro bd hbd
  let : IsProbabilityMeasure bd.law.P := hbd.law.probP
  obtain ⟨cg, Cg, hcg, hCg, Ng, hgd⟩ := hgood bd hbd
  obtain ⟨C, hC, Ns, hsl⟩ := hslabs bd hbd Cg cg hCg hcg
  have hδ : 0 < bd.law.δ := hbd.law.delta_pos
  let a : ℝ := bd.law.δ / 1000
  have ha : 0 < a := by dsimp only [a]; positivity
  refine ⟨C + 1, by positivity, ?_⟩
  intro K hK
  obtain ⟨B, hB, hmoment⟩ := target_difference_four_le bd hbd K
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop,
      Ng ≤ N ∧ Ns ≤ N ∧ (9 * K) ^ 2 ≤ N ∧ (64 * (m + 1)) ^ 2 ≤ N ∧ 3 ≤ N ∧
      Real.log N ≤ (N : ℝ) ^ a ∧ B + 1 ≤ N ∧ 8 * Cg ^ 2 ≤ Real.log N ∧ 1 ≤ Real.log N := by
    filter_upwards [eventually_ge_atTop Ng, eventually_ge_atTop Ns,
      eventually_ge_atTop ((9 * K) ^ 2), eventually_ge_atTop ((64 * (m + 1)) ^ 2),
      eventually_ge_atTop 3, eventually_log_le_rpow ha,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (B + 1),
      hlogtop.eventually_ge_atTop (8 * Cg ^ 2), hlogtop.eventually_ge_atTop 1]
      with N h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨N₀, ?_⟩
  intro M hM hfit N hN n ℓ y htar
  let : IsProbabilityMeasure M.P := hM.probP
  obtain ⟨hNg, hNs, hNK, hNm, hN3, hlog, hBle, h8, hlog1⟩ := hN₀ N hN
  obtain ⟨G, hGmono, hGos, hGgood⟩ := hgd M hM hfit N hNg
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN3)
  let S : ℝ := Real.log N
  have hS : 0 < S := lt_of_lt_of_le one_pos hlog1
  have hOs := hGos S le_rfl
  -- the fourth norm of the indicator of the exceptional event
  have hCgS : 0 < Cg / S := div_pos hCg hS
  have hbad := indicator_eLpNorm_four_le_exp (P := M.P) (G S) (Cg / S) hCgS hOs
  obtain ⟨hn, hsqrt, hnℓ, hℓ⟩ := target_size_bounds (by omega : 1 ≤ K) hNK htar
  have hNm' : ((64 * (m + 1) : ℕ) : ℝ) ≤ Real.sqrt N := by
    exact (le_abs_self _).trans (Real.abs_le_sqrt (by exact_mod_cast hNm))
  have hn64 : 64 * (m + 1) ≤ n := by
    have : ((64 * (m + 1) : ℕ) : ℝ) ≤ n := hNm'.trans hsqrt
    exact_mod_cast this
  have hbox : InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) ((ℓ : ℤ), y) :=
    target_inBox hM hℓ htar.2.2.1 htar.2.2.2
  have hbox0 : InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) (0 : Vertex m) := by
    constructor
    · simpa only [Prod.fst_zero, Int.cast_zero, abs_zero] using
        (show 0 ≤ 3 * (1 + ‖M.t₀‖) * (N : ℝ) by positivity)
    · intro j
      simpa only [Prod.snd_zero, Pi.zero_apply, Int.cast_zero, abs_zero] using
        (show 0 ≤ 3 * (1 + ‖M.t₀‖) * (N : ℝ) by positivity)
  have hℓ3 : (ℓ : ℝ) ≤ 3 * N := by
    have he : (ℓ : ℝ) ≤ N := by exact_mod_cast htar.2.2.1
    linarith only [he, hNpos.le]
  have ht := targetSlope_norm_le_rpow hM (by omega : 1 ≤ n) hnℓ htar.2.2.2
  have ht2 : ‖targetSlope ℓ y - M.t₀‖ ≤ 2 * (n : ℝ) ^ (M.δ / 100 - 1 / 4) :=
    ht.trans (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by norm_num))
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hslope : ‖targetSlope ℓ y - M.t₀‖ ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) := by
    have he : M.δ / 100 - 1 / 4 ≤ 0 := by linarith [hM.delta_le_one]
    have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
    have h1 : (n : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ Real.sqrt N ^ (M.δ / 100 - 1 / 4) :=
      Real.rpow_le_rpow_of_nonpos hsq hsqrt he
    have h2 : Real.sqrt N ^ (M.δ / 100 - 1 / 4) = (N : ℝ) ^ ((M.δ / 100 - 1 / 4) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]; ring_nf
    have h3 : (N : ℝ) ^ ((M.δ / 100 - 1 / 4) / 2) ≤ (N : ℝ) ^ (-(1 : ℝ) / 9) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith [hM.delta_le_one])
    have h4 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 9) := by positivity
    linarith only [ht, h1, h2, h3, h4]
  have hS' : S ≤ (N : ℝ) ^ (M.δ / 1000) := by
    change Real.log N ≤ (N : ℝ) ^ (M.δ / 1000)
    rw [hfit.δ_eq]; exact hlog
  have hsandwich : ∀ ω ∈ G S,
      (passageTime ω 0 ((ℓ : ℤ), y) : ℝ≥0∞) ≤ slabMin M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) ∧
      slabMin M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) ≤
        (passageTime ω 0 ((ℓ : ℤ), y) : ℝ≥0∞) + ENNReal.ofReal (C * K * S ^ 2) := by
    intro ω hω
    exact ((hsl M hM hfit N hNs S le_rfl ω (hGgood S le_rfl ω hω) ℓ (targetSlope ℓ y) 0
      ((ℓ : ℤ), y) (target_point_sub hℓ y) hℓ hℓ3 hslope).2 K n htar.1 (by omega) hsqrt ht2 hS'
      hbox0 hbox).2
  -- the chain of the rounded points supplies an admissible tuple
  have hYexists : ∃ Y, IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y := by
    obtain ⟨Y, hY, -⟩ := hchains M hM K n (by omega) hn64 (targetSlope ℓ y) 0 ((ℓ : ℤ), y)
      (by rw [← htar.1]; exact target_point_sub hℓ y)
    exact ⟨Y, hY⟩
  have hfour := hmoment M hM hfit N n ℓ y hn hnℓ htar.2.2.1 htar.2.2.2 hYexists
  have hX : AEStronglyMeasurable
      (fun ω => targetMin M ω n K ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)) M.P :=
    ((measurable_targetMin M n K ℓ y).sub
      (Infra.FPP.measurable_passageTime_real _ _)).aestronglyMeasurable
  have hKpos : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hCKS : 0 ≤ C * K * S ^ 2 := by positivity
  have htwo := eLpNorm_two_le_good_add_four_mul hX hOs.1.aestronglyMeasurable hCKS
    (fun ω hω => norm_target_difference_le_of_sandwich hCKS (hsandwich ω hω).1
      (hsandwich ω hω).2)
  -- the exceptional contribution is at most one
  have hBN : 0 < B * N := mul_pos hB hNpos
  have hexp : (B * N) ^ 4 ≤ Real.exp (((Cg / S) ^ 2)⁻¹) - 1 := by
    have hx : 8 * Real.log N ≤ ((Cg / S) ^ 2)⁻¹ := by
      rw [div_pow, inv_div]
      have : 8 * Cg ^ 2 ≤ S := h8
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [this, hS, sq_nonneg Cg]
    have h1 : (N : ℝ) ^ 8 ≤ Real.exp (((Cg / S) ^ 2)⁻¹) := by
      calc (N : ℝ) ^ 8 = Real.exp (8 * Real.log N) := by
            rw [show 8 * Real.log N = ((8 : ℕ) : ℝ) * Real.log N by norm_num,
              Real.exp_nat_mul, Real.exp_log hNpos]
        _ ≤ _ := Real.exp_le_exp.2 hx
    have h2 : (B * N) ^ 4 + 1 ≤ (N : ℝ) ^ 8 := by
      have h3 : (B * N) ^ 4 + N ^ 4 ≤ (B * N + N) ^ 4 :=
        pow_add_pow_le (by positivity) hNpos.le (by norm_num)
      have h4 : (B * N + N) ^ 4 ≤ ((N : ℝ) ^ 2) ^ 4 := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith only [mul_le_mul_of_nonneg_left hBle hNpos.le]
      have h5 : (1 : ℝ) ≤ N ^ 4 := one_le_pow₀ hN1'
      calc _ ≤ (B * N) ^ 4 + N ^ 4 := by linarith only [h5]
        _ ≤ _ := h3
        _ ≤ _ := h4
        _ = _ := by ring
    linarith only [h1, h2]
  have hbad' : eLpNorm ((G S)ᶜ.indicator fun _ => (1 : ℝ)) 4 M.P ≤ ENNReal.ofReal (B * N)⁻¹ := by
    refine hbad.trans (ENNReal.ofReal_le_ofReal ?_)
    have hc0 : 0 < Real.exp (((Cg / S) ^ 2)⁻¹) - 1 := lt_of_lt_of_le (by positivity) hexp
    have h4 : (Real.exp (((Cg / S) ^ 2)⁻¹) - 1)⁻¹ ≤ ((B * N) ^ 4)⁻¹ := inv_anti₀ (by positivity) hexp
    calc _ ≤ (((B * N) ^ 4)⁻¹) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (inv_nonneg.2 hc0.le) h4 (by norm_num)
      _ = _ := by
          rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hBN.le]
          norm_num
  have hone : eLpNorm (fun ω => targetMin M ω n K ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)) 4 M.P *
      eLpNorm ((G S)ᶜ.indicator fun _ => (1 : ℝ)) 4 M.P ≤ 1 := by
    calc _ ≤ ENNReal.ofReal (B * N) * ENNReal.ofReal (B * N)⁻¹ := mul_le_mul' hfour hbad'
      _ = 1 := by
        rw [← ENNReal.ofReal_mul hBN.le, mul_inv_cancel₀ hBN.ne', ENNReal.ofReal_one]
  have hS2 : 1 ≤ S ^ 2 := by nlinarith only [hlog1]
  have hKS : 1 ≤ (K : ℝ) * S ^ 2 := by nlinarith only [hKpos, hS2]
  calc _ ≤ ENNReal.ofReal (C * K * S ^ 2) + 1 := htwo.trans (add_le_add le_rfl hone)
    _ ≤ ENNReal.ofReal (C * K * S ^ 2) + ENNReal.ofReal (K * S ^ 2) := by
        gcongr
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hKS
    _ = ENNReal.ofReal ((C + 1) * K * Real.log N ^ 2) := by
        rw [← ENNReal.ofReal_add hCKS (by positivity)]
        congr 1; ring

end CurvatureVariance.Paper.Contracts
