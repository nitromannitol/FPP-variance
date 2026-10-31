/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Proofs.ShortLengths.ProfileLevel
public import CurvatureVariance.Paper.Proofs.ShortLengths.Translate
import CurvatureVariance.Statements.Inputs.IsOsMeasureGeLe
import CurvatureVariance.Paper.Proofs.Geometry.SlabsPair
import CurvatureVariance.Paper.Proofs.Geometry.SlabsAsymp
import CurvatureVariance.Paper.Proofs.Geometry.SlabsTwo
import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes
import CurvatureVariance.Paper.Proofs.Moments.Scales
import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Order.SetAccumulate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Equation `eq:profiledifference`

The paper, in the proof of Proposition `prop:profiles` for `s ≤ N/2`:

* "By stationarity, we may assume that `|ū| ≤ d^{1/2}`, so that `I` and `I'` lie in `[−N²,N²]^d`":
  the configuration is translated by `z = (p, ⌊c⌋)` (`translate`, `hmp`);
* "Let `S ≥ log N` be the least integer such that `𝒢_N(S)` occurs, so that
  `S ≤ log N + 1 + O₂(C)`": `exists_leastLevel`, from `GoodStatement`, through `failCount` of
  the module `ShortLengths.ProfileLevel`. The events of the contract are null-measurable, so the
  count runs over a measurable increasing family inside them;
* "If `s ≥ CS²`, Lemma `lem:slabs`(1) applies, since the slopes of the vectors `v − u` lie within
  `2s^{δ/100−1/4} ≤ 3N^{−1/9}` of `t₀`; otherwise Lemma `lem:good`(2) gives `T_P ≤ CS²`":
  `slabTime_le_of_isGood`;
* "Hence `0 ≤ sup (T_P − T) ≤ CS² ≤ C log²N + O₁(C)`": `S² ≤ 18 log²N + 2 count²`.

The slopes of the vectors `v − u` are within `2s^{δ/100−1/4}` of `t₀` by the width margin
(`exists_width_margin`, from equation `eq:scales`). Here `C` comes before `b`, as in the paper: the
side of the cubes enters only the threshold, through `b W_s ≤ s/4` and `√m b W_s ≤ s^{3/4+δ/100}/4`
for `N` large depending on `b`.

The proof consumes the contracts `GoodStatement`, `SlabsStatement` and `ScalesStatement`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.ShortLengths

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP
  CurvatureVariance.Infra.Os CurvatureVariance.Paper.Proofs.Geometry

variable {m : ℕ}

/-- **The bound of `T_P − T` at one configuration.** There are `C₃ > 0` and `N₀` such that, for
`N ≥ N₀`, `S ≥ log N` and `ω` with the properties of Lemma `lem:good` at the scale `S`, every pair
`u, v ∈ [−N², N²]^d` with `v₁ = u₁ + s`, `√N ≤ s ≤ 2N` and slope within `2 s^{δ/100−1/4}` of `t₀`
has `T ≤ T_P ≤ T + C₃ S²`: by Lemma `lem:slabs`(1) if `s ≥ CS²`, and by Lemma `lem:good`(2)
otherwise. The constants depend on the slope only through `T = bd.T ≥ |t₀|`. -/
theorem slabTime_le_of_isGood (hSlabs : SlabsStatement m) (bd : Bounds m) (hbd : bd.Valid)
    {Cg cg : ℝ} (hCg : 0 < Cg) (hcg : 0 < cg) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∃ N₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ S : ℝ, Real.log N ≤ S → ∀ ω : Config m, IsGood M Cg cg N S ω →
      ∀ s : ℕ, Real.sqrt N ≤ s → (s : ℝ) ≤ 2 * N →
      ∀ u v : Vertex m, InBox ((N : ℝ) ^ 2) u → InBox ((N : ℝ) ^ 2) v → v.1 = u.1 + s →
        ‖(s : ℝ)⁻¹ • transversePoint (v.2 - u.2) - M.t₀‖ ≤ 2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
        (passageTime ω u v : ℝ≥0∞) ≤ slabTime ω u.1 v.1 u v ∧
          slabTime ω u.1 v.1 u v ≤ (passageTime ω u v : ℝ≥0∞) + ENNReal.ofReal (C₃ * S ^ 2) := by
  obtain ⟨C₂, hC₂, N₂, hslab⟩ := hSlabs bd hbd Cg cg hCg hcg
  obtain ⟨N₃, hsmall⟩ := exists_slope_small (m := m) (by norm_num : (0 : ℝ) ≤ 2)
    hbd.law.delta_pos hbd.law.delta_le_one (ε := 1) one_pos
  -- the constant depends on the slope only through `T = bd.T ≥ |t₀|`
  set T := bd.T with hTdef
  have hT0 : 0 ≤ T := hbd.T_nonneg
  set C₃ := max C₂ (Cg * ((2 + T) * C₂ + 1)) with hC₃
  have hC₃2 : C₂ ≤ C₃ := le_max_left _ _
  refine ⟨C₃, lt_of_lt_of_le hC₂ hC₃2, max N₂ (max N₃ 4), fun M hM hfit N hN S hS ω hω s hs1 hs2
    u v hu hv huv ht => ?_⟩
  have hTM : ‖M.t₀‖ ≤ T := hfit.t₀_le
  have hδ1 := hM.delta_le_one
  have hN2 : N₂ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : N₃ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hN4 : (4 : ℝ) ≤ N := by
    exact_mod_cast le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hNpos : (0 : ℝ) < N := by linarith only [hN4]
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith only [hN4])
  have hS0 : 0 ≤ S := hlogN.trans hS
  have hsqrtN : (2 : ℝ) ≤ Real.sqrt N := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hN4
  have hs2' : (2 : ℝ) ≤ s := hsqrtN.trans hs1
  have hspos : 0 < s := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hs2' : (0 : ℝ) < s)
  set t := (s : ℝ)⁻¹ • transversePoint (v.2 - u.2) with htdef
  have hpt := point_sub_eq_smul_slopeVec hspos huv
  have ht1 : ‖t - M.t₀‖ ≤ 1 := by
    have ht' := ht
    rw [hfit.δ_eq] at ht'
    exact (hsmall N hN3 s hs1 (t - M.t₀) ht').1
  have htT : ‖t‖ ≤ T + 1 := by linarith only [norm_le_norm_sub_add t M.t₀, ht1, hTM]
  have hslope : ‖t - M.t₀‖ ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) := by
    have he : M.δ / 100 - 1 / 4 ≤ 0 := by linarith only [hδ1]
    have hsq : 0 < Real.sqrt N := by linarith only [hsqrtN]
    have h1 : (s : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ Real.sqrt N ^ (M.δ / 100 - 1 / 4) :=
      Real.rpow_le_rpow_of_nonpos hsq hs1 he
    have h2 : Real.sqrt N ^ (M.δ / 100 - 1 / 4) = (N : ℝ) ^ ((M.δ / 100 - 1 / 4) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]; ring_nf
    have h3 : (N : ℝ) ^ ((M.δ / 100 - 1 / 4) / 2) ≤ (N : ℝ) ^ (-(1 : ℝ) / 9) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [hN4]) (by linarith only [hδ1])
    have h4 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 9) := by positivity
    linarith only [ht, h1, h2, h3, h4]
  refine ⟨passageTime_le_slabTime ω _ _ u v, ?_⟩
  by_cases hlong : C₂ * S ^ 2 ≤ s
  · -- Lemma `lem:slabs`(1)
    have h := ((hslab M hM hfit N hN2 S hS ω hω s t u v hpt hspos (by linarith only [hs2])
      hslope).1 hu hv hlong).2
    exact h.trans (add_le_add_right (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hC₃2 (sq_nonneg S))) _)
  · -- Lemma `lem:good`(2)
    push Not at hlong
    have hbox : ∀ x : Vertex m, InBox ((N : ℝ) ^ 2) x → InBox (2 * (N : ℝ) ^ 2) x := by
      intro x hx
      refine inBox_mono ?_ hx
      have := sq_nonneg (N : ℝ)
      linarith only [this]
    have hs2z : (2 : ℤ) ≤ s := by exact_mod_cast hs2'
    have hD := hω.slabTime_le u v (hbox u hu) (hbox v hv) u.1 v.1 (by rw [huv]; omega) le_rfl
      (by rw [huv]; omega) (by rw [huv]; omega) le_rfl
    have hnorm : ‖point v - point u‖ ≤ (2 + T) * (C₂ * S ^ 2) := by
      rw [hpt, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have h1 := norm_slopeVec_le htT
      have h2 : (0 : ℝ) ≤ 2 + T := by linarith only [hT0]
      calc (s : ℝ) * ‖slopeVec t‖ ≤ (C₂ * S ^ 2) * (2 + T) :=
            mul_le_mul hlong.le (by linarith only [h1]) (norm_nonneg _) (by positivity)
        _ = (2 + T) * (C₂ * S ^ 2) := by ring
    have hle : Cg * (‖point v - point u‖ + S ^ 2) ≤ C₃ * S ^ 2 := by
      calc Cg * (‖point v - point u‖ + S ^ 2) ≤ Cg * ((2 + T) * (C₂ * S ^ 2) + S ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith only [hnorm]) hCg.le
        _ = Cg * ((2 + T) * C₂ + 1) * S ^ 2 := by ring
        _ ≤ C₃ * S ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg S)
    calc slabTime ω u.1 v.1 u v ≤ ENNReal.ofReal (Cg * (‖point v - point u‖ + S ^ 2)) := hD
      _ ≤ ENNReal.ofReal (C₃ * S ^ 2) := ENNReal.ofReal_le_ofReal hle
      _ ≤ (passageTime ω u v : ℝ≥0∞) + ENNReal.ofReal (C₃ * S ^ 2) := le_add_self

/-- The scale of the variable of `exists_leastLevel`. -/
noncomputable def leastLevelConst (Cg B : ℝ) : ℝ :=
  (1 + Real.log (Real.exp (1 / Cg ^ 2)) / (2 * Real.log 2)) * (2 * (4 * B / (2 / Cg ^ 2)))

theorem leastLevelConst_pos {Cg B : ℝ} (hCg : 0 < Cg) (hB : 0 < B) : 0 < leastLevelConst Cg B := by
  unfold leastLevelConst
  have h0 : 0 < Real.log (Real.exp (1 / Cg ^ 2)) := by rw [Real.log_exp]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  positivity

/-- `P(Gᶜ) ≤ 2 e^{−1/θ²}` from `1_{Gᶜ} ≤ O₂(θ)`. -/
theorem measure_compl_le_of_isOs_indicator {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {G : Set Ω} {θ : ℝ} (hθ : 0 < θ)
    (h : CurvatureVariance.IsOs P 2 θ (Gᶜ.indicator fun _ => (1 : ℝ))) :
    P Gᶜ ≤ ENNReal.ofReal (2 * Real.exp (-(1 / θ ^ 2))) := by
  have hm := h.measure_ge_le two_pos hθ (x := 1 / θ) (by positivity)
  have hsub : Gᶜ ⊆ {ω | θ * (1 / θ) ≤ Gᶜ.indicator (fun _ => (1 : ℝ)) ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq]
    rw [Set.indicator_of_mem hω, mul_one_div_cancel hθ.ne']
  have hexp : (1 / θ) ^ (2 : ℝ) = 1 / θ ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div_pow]
  rw [hexp] at hm
  exact (measure_mono hsub).trans hm

/-- **The least level** (the proof of Proposition `prop:profiles` for `s ≤ N/2`): let `G` be an
increasing family of events with `1_{G(S)ᶜ} ≤ O₂(Cg/S)` for `S ≥ L ≥ Cg > 0`. Then there is `f ≥ 0`
with `B f² ≤ O₁(C)`, and almost surely `G(⌈L⌉ + ⌈f⌉)` occurs. So the least integer `S ≥ L` at which
`G` occurs is at most `L + 2 + f`, the paper's `S ≤ log N + 1 + O₂(C)`. The events `G(S)` need only
be null-measurable, and `f` counts the failures of a measurable increasing family inside them. -/
theorem exists_leastLevel {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : ℝ → Set Ω} (hmono : Monotone G) {Cg L B : ℝ} (hCg : 0 < Cg) (hL : Cg ≤ L) (hB : 0 < B)
    (hG : ∀ S : ℝ, L ≤ S → CurvatureVariance.IsOs P 2 (Cg / S) ((G S)ᶜ.indicator fun _ => (1 : ℝ))) :
    ∃ f : Ω → ℝ, (∀ ω, 0 ≤ f ω) ∧ CurvatureVariance.IsOs P 1 (leastLevelConst Cg B) (fun ω => B * f ω ^ 2) ∧
      ∀ᵐ ω ∂P, ω ∈ G ((⌈L⌉₊ + ⌈f ω⌉₊ : ℕ) : ℝ) := by
  have hL0 : 0 < L := lt_of_lt_of_le hCg hL
  set k₀ := ⌈L⌉₊ with hk₀
  have hLk : L ≤ k₀ := Nat.le_ceil L
  have hSj : ∀ j : ℕ, L + j ≤ ((k₀ + j : ℕ) : ℝ) := fun j => by
    push_cast
    linarith only [hLk]
  have hLj : ∀ j : ℕ, L ≤ ((k₀ + j : ℕ) : ℝ) := fun j => by
    linarith only [hSj j, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hnull : ∀ j : ℕ, NullMeasurableSet (G ((k₀ + j : ℕ) : ℝ)) P := fun j =>
    NullMeasurableSet.of_compl ((aemeasurable_indicator_const_iff (1 : ℝ)).1 (hG _ (hLj j)).1)
  choose H hHsub hHmeas hHae using fun j => (hnull j).exists_measurable_subset_ae_eq
  -- a measurable increasing family inside `G`
  set G' : ℕ → Set Ω := Set.accumulate H with hG'
  have hG'mono : Monotone G' := Set.monotone_accumulate
  have hG'meas : ∀ j, MeasurableSet (G' j) := fun j => by
    rw [hG', Set.accumulate_def]
    exact MeasurableSet.biUnion (Set.to_countable _) fun i _ => hHmeas i
  have hG'sub : ∀ j, G' j ⊆ G ((k₀ + j : ℕ) : ℝ) := fun j ω hω => by
    obtain ⟨i, hij, hi⟩ := Set.mem_accumulate.1 hω
    exact hmono (by exact_mod_cast Nat.add_le_add_left hij k₀) (hHsub i hi)
  set c : ℝ := 2 / Cg ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hfail : ∀ j : ℕ, P (G' j)ᶜ ≤ ENNReal.ofReal (Real.exp (-(c / 2 * (j : ℝ) ^ 2))) := by
    intro j
    have hSpos : (0 : ℝ) < ((k₀ + j : ℕ) : ℝ) := lt_of_lt_of_le hL0 (hLj j)
    have h1 : P (G' j)ᶜ ≤ P (H j)ᶜ :=
      measure_mono (Set.compl_subset_compl.2 Set.subset_accumulate)
    have h2 : P (H j)ᶜ = P (G ((k₀ + j : ℕ) : ℝ))ᶜ :=
      measure_congr (ae_eq_set_compl_compl.2 (hHae j))
    have h3 := measure_compl_le_of_isOs_indicator (div_pos hCg hSpos) (hG _ (hLj j))
    rw [h2] at h1
    refine h1.trans (h3.trans (ENNReal.ofReal_le_ofReal ?_))
    -- `2 e^{−S²/Cg²} ≤ e^{−j²/Cg²}`, since `S ≥ Cg + j`
    set S : ℝ := ((k₀ + j : ℕ) : ℝ) with hS
    have hSge : Cg + j ≤ S := by linarith only [hSj j, hL]
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hsq : Cg ^ 2 + (j : ℝ) ^ 2 ≤ S ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hSge 2
      nlinarith only [this, hj0, hCg]
    have h4 : 1 + (j : ℝ) ^ 2 / Cg ^ 2 ≤ 1 / (Cg / S) ^ 2 := by
      rw [div_pow, one_div_div, le_div_iff₀ (by positivity)]
      have : (1 + (j : ℝ) ^ 2 / Cg ^ 2) * Cg ^ 2 = Cg ^ 2 + (j : ℝ) ^ 2 := by field_simp
      linarith only [this, hsq]
    have h5 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith only [this]
    have h6 : c / 2 * (j : ℝ) ^ 2 = (j : ℝ) ^ 2 / Cg ^ 2 := by rw [hc]; field_simp
    calc 2 * Real.exp (-(1 / (Cg / S) ^ 2))
        ≤ Real.exp 1 * Real.exp (-(1 + (j : ℝ) ^ 2 / Cg ^ 2)) :=
          mul_le_mul h5 (Real.exp_le_exp.2 (neg_le_neg h4)) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (-(c / 2 * (j : ℝ) ^ 2)) := by
          rw [← Real.exp_add, h6]
          congr 1
          ring
  have hlim : Tendsto (fun j => P (G' j)ᶜ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => Real.exp (-(c / 2 * (j : ℝ) ^ 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (((tendsto_pow_atTop two_ne_zero).comp
        tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity))
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => bot_le) hfail
  have hOs := isOs_failCount_sq hG'mono hG'meas hc0 hB hfail
  refine ⟨fun ω => (failCount G' ω).toReal, fun ω => ENNReal.toReal_nonneg, ?_, ?_⟩
  · have e : c / 2 = 1 / Cg ^ 2 := by rw [hc]; field_simp
    rw [e] at hOs
    exact hOs
  · filter_upwards [ae_failCount_ne_top hG'mono hlim] with ω hω
    exact hG'sub _ (mem_of_failCount_ne_top hG'mono hω)

/-- **Equation `eq:profiledifference`**, from Lemma `lem:good`, Lemma `lem:slabs`(1) and equation
`eq:scales`. -/
theorem profileDifferenceStatement (hGood : GoodStatement m) (hSlabs : SlabsStatement m)
    (hScales : ScalesStatement m) : ProfileDifferenceStatement m := by
  intro bd hbd Cstar
  obtain ⟨cg, Cg, hcg, hCg, Ng, hGoodK⟩ := hGood bd hbd
  obtain ⟨C₃, hC₃, N₃, hcore⟩ := slabTime_le_of_isGood hSlabs bd hbd hCg hcg
  set B := 2 * C₃ with hBdef
  have hB : 0 < B := by positivity
  have hCf := leastLevelConst_pos hCg hB
  set Cf := leastLevelConst Cg B with hCfdef
  refine ⟨18 * C₃ + Cf, by positivity, fun b hb K hK => ?_⟩
  set η := 1 / (4 * (Real.sqrt m + 1) * b) with hη
  have hη0 : 0 < η := by positivity
  have hbη : b * η ≤ 1 / 4 := by
    rw [hη, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [Real.sqrt_nonneg (m : ℝ), hb]
  have hmbη : Real.sqrt m * b * η ≤ 1 / 4 := by
    rw [hη, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [Real.sqrt_nonneg (m : ℝ), hb]
  obtain ⟨N₅, hN₅⟩ := Moments.exists_width_margin hScales bd hbd Cstar hη0
  set N₆ := ⌈(8 * Real.sqrt ((m : ℝ) + 1)) ^ 4⌉₊ with hN₆
  set N₇ := ⌈8 * (2 + bd.T)⌉₊ with hN₇
  set N₈ := ⌈Real.exp Cg⌉₊ with hN₈
  refine ⟨max (max N₃ Ng) (max N₅ (max N₆ (max 6 (max N₇ N₈)))),
    fun M hM hfit N hN A hA hR s hs1 hs2 t I I' hI ht => ?_⟩
  have := hM.probF
  have := hM.probP
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  have hN3 : N₃ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNg : Ng ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hN5 : N₅ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hN6' : N₆ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) hN))
  have hN678 : max 6 (max N₇ N₈) ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) hN))
  have hN6 : (6 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left _ _) hN678
  have hN78 : max N₇ N₈ ≤ N := le_trans (le_max_right _ _) hN678
  have hN7 : 8 * (2 + ‖M.t₀‖) ≤ (N : ℝ) := by
    have h := (Nat.le_ceil (8 * (2 + bd.T))).trans
      (by exact_mod_cast le_trans (le_max_left _ _) hN78 : ((N₇ : ℕ) : ℝ) ≤ N)
    linarith only [h, hfit.t₀_le]
  have hT0 : 0 ≤ ‖M.t₀‖ := norm_nonneg _
  have hNpos : (0 : ℝ) < N := by linarith only [hN6]
  have hlogN : 1 ≤ Real.log N := one_le_log_of_three_le (by linarith only [hN6])
  have hCglog : Cg ≤ Real.log N := by
    have h := (Nat.le_ceil (Real.exp Cg)).trans
      (by exact_mod_cast le_trans (le_max_right _ _) hN78 : ((N₈ : ℕ) : ℝ) ≤ N)
    exact (Real.le_log_iff_exp_le hNpos).2 h
  have hsqrtN : 1 ≤ Real.sqrt N :=
    (Real.one_le_sqrt).2 (by linarith only [hN6])
  have hs1' : (1 : ℝ) ≤ s := hsqrtN.trans hs1
  have hs0 : (0 : ℝ) < s := by linarith only [hs1']
  have hspos : 0 < s := by exact_mod_cast hs0
  -- the width margin, from equation `eq:scales`
  have hW := hN₅ K hK M hM hfit N hN5 A hA hR s (by linarith only [hs1, Real.sqrt_nonneg (N : ℝ)])
  set e := M.δ / 100 - 1 / 4 with he
  set Wd := W M K A s with hWd
  have hW0 : 0 ≤ Wd := Real.sqrt_nonneg _
  obtain ⟨p, c₀, c₀', a₁, a₁', rfl, rfl, ha0, haW, ha0', haW', hcc⟩ := hI
  have hbW : b * Wd ≤ s / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hW (by linarith only [hb] : (0 : ℝ) ≤ b)
    have h2 := rpow_le_self_of_one_le hs1' hδ1
    calc b * Wd ≤ b * (η * (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)) := h1
      _ = (b * η) * (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by ring
      _ ≤ (1 / 4) * s := mul_le_mul hbη h2 (Real.rpow_nonneg hs0.le _) (by norm_num)
      _ = s / 4 := by ring
  -- the slope of every pair is within `2 s^e` of `t₀`
  have hslope : ∀ u ∈ transverseCube p c₀ a₁, ∀ v ∈ transverseCube (p + s) c₀' a₁',
      ‖(s : ℝ)⁻¹ • transversePoint (v.2 - u.2) - M.t₀‖ ≤ 2 * (s : ℝ) ^ e := by
    intro u hu v hv
    have h1 := norm_transverse_sub_le_of_cubes ha0 ha0' haW haW' hcc hu hv
    have heq : (s : ℝ)⁻¹ • transversePoint (v.2 - u.2) - M.t₀ =
        (t - M.t₀) + (s : ℝ)⁻¹ • (transversePoint (v.2 - u.2) - (s : ℝ) • t) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hs0.ne', one_smul]; abel
    rw [heq]
    have h2 := norm_add_le (t - M.t₀)
      ((s : ℝ)⁻¹ • (transversePoint (v.2 - u.2) - (s : ℝ) • t))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs0)] at h2
    -- `s⁻¹ √m b W ≤ s^e / 4`
    have h3 : (s : ℝ)⁻¹ * (Real.sqrt m * (b * Wd)) ≤ (s : ℝ) ^ e / 4 := by
      have hw := mul_le_mul_of_nonneg_left hW
        (by positivity : (0 : ℝ) ≤ (s : ℝ)⁻¹ * (Real.sqrt m * b))
      calc (s : ℝ)⁻¹ * (Real.sqrt m * (b * Wd)) = (s : ℝ)⁻¹ * (Real.sqrt m * b) * Wd := by ring
        _ ≤ (s : ℝ)⁻¹ * (Real.sqrt m * b) * (η * (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)) := hw
        _ = Real.sqrt m * b * η * ((s : ℝ)⁻¹ * (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)) := by ring
        _ = Real.sqrt m * b * η * (s : ℝ) ^ e := by rw [inv_mul_rpow_eq hs0]
        _ ≤ 1 / 4 * (s : ℝ) ^ e :=
            mul_le_mul_of_nonneg_right hmbη (Real.rpow_nonneg hs0.le _)
        _ = (s : ℝ) ^ e / 4 := by ring
    -- `s⁻¹ 2√d ≤ s^e / 4`
    have h4 : (s : ℝ)⁻¹ * (2 * Real.sqrt ((m : ℝ) + 1)) ≤ (s : ℝ) ^ e / 4 := by
      have hs34 : 8 * Real.sqrt ((m : ℝ) + 1) ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
        have h6 : (8 * Real.sqrt ((m : ℝ) + 1)) ^ 4 ≤ N :=
          (Nat.le_ceil _).trans (Nat.cast_le.2 hN6')
        have h7 : 8 * Real.sqrt ((m : ℝ) + 1) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity)
            (by norm_num : (0 : ℝ) < 4), ← Real.rpow_mul hNpos.le]
          norm_num
          exact_mod_cast h6
        have h8 : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (s : ℝ) ^ ((1 : ℝ) / 2) := by
          calc (N : ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt N ^ ((1 : ℝ) / 2) := by
                rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]; norm_num
            _ ≤ (s : ℝ) ^ ((1 : ℝ) / 2) :=
                Real.rpow_le_rpow (Real.sqrt_nonneg _) hs1 (by norm_num)
        have h9 : (s : ℝ) ^ ((1 : ℝ) / 2) ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) :=
          Real.rpow_le_rpow_of_exponent_le hs1' (by linarith only [hδ])
        linarith only [h7, h8, h9]
      have := mul_le_mul_of_nonneg_left hs34 (inv_nonneg.2 hs0.le)
      rw [inv_mul_rpow_eq hs0] at this
      linarith only [this]
    have h5 : (s : ℝ)⁻¹ * ‖transversePoint (v.2 - u.2) - (s : ℝ) • t‖ ≤ (s : ℝ) ^ e / 2 := by
      calc (s : ℝ)⁻¹ * ‖transversePoint (v.2 - u.2) - (s : ℝ) • t‖
          ≤ (s : ℝ)⁻¹ * (Real.sqrt m * (b * Wd) + 2 * Real.sqrt ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (by linarith only [h1]) (inv_nonneg.2 hs0.le)
        _ ≤ (s : ℝ) ^ e / 2 := by rw [mul_add]; linarith only [h3, h4]
    have ht' : ‖t - M.t₀‖ ≤ 3 / 2 * (s : ℝ) ^ e := ht
    linarith only [h2, h5, ht']
  -- stationarity and the least level
  set z : Vertex m := (p, fun j => ⌊c₀ j⌋) with hz
  have hmp : MeasurePreserving (translate z) M.P M.P :=
    IsIIDWeights.measurePreserving_translate hM.iid z
  obtain ⟨G, hGmono, hGos, hGprop⟩ := hGoodK M hM hfit N hNg
  obtain ⟨f, hf0, hfOs, hfG⟩ := exists_leastLevel hGmono hCg hCglog hB hGos
  refine ⟨(fun ω => B * f ω ^ 2) ∘ translate z, ?_, ?_⟩
  · exact (IsOs.comp_measurePreserving hfOs hmp).mono_scale zero_le_one (by positivity)
      (by linarith only [hC₃])
  filter_upwards [hmp.quasiMeasurePreserving.ae hfG] with ω hmem
  intro u hu v hv
  set ω' := translate z ω with hω'
  set k₀ := ⌈Real.log N⌉₊ with hk₀
  set J := ⌈f ω'⌉₊ with hJ
  set S : ℝ := ((k₀ + J : ℕ) : ℝ) with hS
  have hSlog : Real.log N ≤ S := by
    rw [hS]
    push_cast
    have := Nat.le_ceil (Real.log N)
    linarith only [this, (Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  have hgood : IsGood M Cg cg N S ω' := hGprop S hSlog ω' hmem
  -- the translated pair
  set u' := u - z with hu'
  set v' := v - z with hv'
  have hu1 : u.1 = p := hu.1
  have hv1 : v.1 = p + s := hv.1
  have huv : v'.1 = u'.1 + s := by simp only [hu', hv', Prod.fst_sub, hu1, hv1]; ring
  have hdiff : v'.2 - u'.2 = v.2 - u.2 := by simp only [hu', hv', Prod.snd_sub]; abel
  have hfl : ∀ j, |(u.2 j : ℝ) - ⌊c₀ j⌋| ≤ s / 8 + 1 := by
    intro j
    have h1 := hu.2 j
    have h2 := Int.floor_le (c₀ j)
    have h3 := Int.lt_floor_add_one (c₀ j)
    have h4 : a₁ / 2 ≤ s / 8 := by linarith only [haW, hbW]
    rw [abs_le] at h1 ⊢
    constructor <;> linarith only [h1.1, h1.2, h2, h3, h4]
  have hboxu : InBox ((N : ℝ) ^ 2) u' := by
    refine ⟨?_, fun j => ?_⟩
    · simp only [hu', Prod.fst_sub, hu1, hz, sub_self, Int.cast_zero, abs_zero]; positivity
    · simp only [hu', hz, Prod.snd_sub, Pi.sub_apply, Int.cast_sub]
      have := hfl j
      nlinarith only [this, hs2, hN6]
  have hboxv : InBox ((N : ℝ) ^ 2) v' := by
    have hsl := hslope u hu v hv
    have hvu : ‖transversePoint (v.2 - u.2)‖ ≤ (2 + ‖M.t₀‖) * s := by
      have h1 : ‖transversePoint (v.2 - u.2)‖ = (s : ℝ) *
          ‖(s : ℝ)⁻¹ • transversePoint (v.2 - u.2)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs0), ← mul_assoc,
          mul_inv_cancel₀ hs0.ne', one_mul]
      have h2 := rpow_slope_le_one hs1' hδ1
      have h3 := norm_le_norm_sub_add ((s : ℝ)⁻¹ • transversePoint (v.2 - u.2)) M.t₀
      rw [h1]
      nlinarith only [hsl, h2, h3, hs0, norm_nonneg ((s : ℝ)⁻¹ • transversePoint (v.2 - u.2))]
    refine ⟨?_, fun j => ?_⟩
    · simp only [hv', Prod.fst_sub, hv1, hz, add_sub_cancel_left]
      rw [abs_of_nonneg (by positivity)]
      push_cast
      nlinarith only [hs2, hN6]
    · simp only [hv', hz, Prod.snd_sub, Pi.sub_apply, Int.cast_sub]
      have h1 : |((v.2 j - u.2 j : ℤ) : ℝ)| ≤ ‖transversePoint (v.2 - u.2)‖ := by
        have := PiLp.norm_apply_le (transversePoint (v.2 - u.2)) j
        simpa [transversePoint, Real.norm_eq_abs] using this
      push_cast at h1
      have h2 := hfl j
      have h3 : |(v.2 j : ℝ) - ⌊c₀ j⌋| ≤ |(v.2 j : ℝ) - u.2 j| + |(u.2 j : ℝ) - ⌊c₀ j⌋| := by
        have := abs_sub_le (v.2 j : ℝ) (u.2 j) (⌊c₀ j⌋ : ℝ)
        linarith only [this]
      have h4 : (2 + ‖M.t₀‖) * (2 * (N : ℝ)) + (2 * N / 8 + 1) ≤ (N : ℝ) ^ 2 := by
        nlinarith only [hN7, hN6, hT0]
      have h5 : (2 + ‖M.t₀‖) * (s : ℝ) ≤ (2 + ‖M.t₀‖) * (2 * N) :=
        mul_le_mul_of_nonneg_left hs2 (by linarith only [hT0])
      nlinarith only [h1, h2, h3, hvu, h4, h5, hs2]
  have hslope' : ‖(s : ℝ)⁻¹ • transversePoint (v'.2 - u'.2) - M.t₀‖ ≤ 2 * (s : ℝ) ^ e := by
    rw [hdiff]; exact hslope u hu v hv
  obtain ⟨hlow, hup⟩ := hcore M hM hfit N hN3 S hSlog ω' hgood s hs1 hs2 u' v' hboxu hboxv huv
    hslope'
  -- undo the translation
  have hT : passageTime ω' u' v' = passageTime ω u v := by
    rw [hω', passageTime_translate, hu', hv', sub_add_cancel, sub_add_cancel]
  have hD : slabTime ω' u'.1 v'.1 u' v' = slabTime ω u.1 v.1 u v := by
    rw [hω', slabTime_translate, hu', hv', sub_add_cancel, sub_add_cancel, Prod.fst_sub,
      Prod.fst_sub, sub_add_cancel, sub_add_cancel]
  rw [hT, hD] at hlow hup
  refine ⟨hlow, ?_⟩
  -- the real inequality
  have hT0' := NNReal.coe_nonneg (passageTime ω u v)
  have hC3S : 0 ≤ C₃ * S ^ 2 := mul_nonneg hC₃.le (sq_nonneg S)
  have hDreal : slabTimeReal ω u.1 v.1 u v ≤ passageTimeReal ω u v + C₃ * S ^ 2 := by
    unfold slabTimeReal passageTimeReal
    refine ENNReal.toReal_le_of_le_ofReal (add_nonneg hT0' hC3S) (hup.trans (le_of_eq ?_))
    rw [ENNReal.ofReal_add hT0' hC3S, ENNReal.ofReal_coe_nnreal]
  -- `C₃ S² ≤ 18 C₃ log² N + 2 C₃ f²`
  have hf0' : 0 ≤ f ω' := hf0 ω'
  have hk₀' : (k₀ : ℝ) ≤ Real.log N + 1 := (Nat.ceil_lt_add_one (by linarith only [hlogN])).le
  have hJf : (J : ℝ) ≤ f ω' + 1 := (Nat.ceil_lt_add_one hf0').le
  have hSle : S ≤ 3 * Real.log N + f ω' := by
    rw [hS]; push_cast; linarith only [hk₀', hJf, hlogN]
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hsq : S ^ 2 ≤ 18 * Real.log N ^ 2 + 2 * f ω' ^ 2 := by
    have h1 : S ^ 2 ≤ (3 * Real.log N + f ω') ^ 2 := pow_le_pow_left₀ hS0 hSle 2
    nlinarith only [h1, sq_nonneg (3 * Real.log N - f ω')]
  have hfinal : C₃ * S ^ 2 ≤ 18 * C₃ * Real.log N ^ 2 + B * f ω' ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq hC₃.le
    rw [hBdef]
    linarith only [this]
  have hlogsq : 0 ≤ Cf * Real.log N ^ 2 := by positivity
  show slabTimeReal ω u.1 v.1 u v - passageTimeReal ω u v ≤
    (18 * C₃ + Cf) * Real.log N ^ 2 + B * f (translate z ω) ^ 2
  have hexp : (18 * C₃ + Cf) * Real.log N ^ 2 =
      18 * C₃ * Real.log N ^ 2 + Cf * Real.log N ^ 2 := by ring
  rw [hexp]
  linarith only [hDreal, hfinal, hlogsq]

end CurvatureVariance.Paper.Proofs.ShortLengths
