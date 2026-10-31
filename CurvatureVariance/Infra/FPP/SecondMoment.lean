/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Notation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Second moments from tails, and one-sided bounds from second moments

Two abstract facts used to state the concentration of the passage time without a prefactor:

* **tail integration**: if `P(u < |X|) ≤ C (1 + u)^{-κ}` with `p < κ`, then
  `E|X|^p ≤ p (1/p + C/(κ - p))` (`lintegral_abs_rpow_le_of_polynomial_tail`); and an exponential
  tail `C e^{-cu}` is such a polynomial tail with `κ = 3` (`exp_tail_le_polynomial_tail`); in
  particular an exponential tail at the scale `r^{1/2}` gives `E X² ≤ V₀ r`
  (`integral_sq_le_of_exp_tail`);
* **a centred variable cannot sit below `-s` with probability close to one**: if `E W = 0` and
  `E W² ≤ V`, then `P(W ≤ -s) ≤ max(1/2, e^{-s²/(4V)})` (`measure_le_neg_le_of_integral_sq_le`).
  Indeed, if `p = P(W ≤ -s) > 1/2`, then `s p ≤ E W₋ = E W₊ ≤ (P(W > 0) E W²)^{1/2}
  ≤ ((1 - p) V)^{1/2}` (the middle step by `2ab ≤ L a² + b²/L`), so `1 - p ≥ s²/(4V)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace CurvatureVariance.Infra.FPP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-! ### Tail integration -/

/-- Tail integration for a nonnegative real random variable, valid also for infinite moments. -/
theorem lintegral_rpow_eq_tail (hX : AEMeasurable X μ) (hpos : 0 ≤ᵐ[μ] X)
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal (X ω ^ p) ∂μ) =
      ENNReal.ofReal p * ∫⁻ u in Ioi (0 : ℝ),
        μ {ω | u < X ω} * ENNReal.ofReal (u ^ (p - 1)) :=
  lintegral_rpow_eq_lintegral_meas_lt_mul μ hpos hX hp

/-- Tail integration for the absolute moment of a real random variable. -/
theorem lintegral_abs_rpow_eq_tail (hX : AEMeasurable X μ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ) =
      ENNReal.ofReal p * ∫⁻ u in Ioi (0 : ℝ),
        μ {ω | u < |X ω|} * ENNReal.ofReal (u ^ (p - 1)) :=
  lintegral_rpow_eq_tail (measurable_norm.comp_aemeasurable hX)
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) hp

private theorem lintegral_rpow_Ioc {p : ℝ} (hp : 0 < p) :
    (∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ (p - 1))) = ENNReal.ofReal (1 / p) := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
    (by linarith : -1 < p - 1)).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_rpow (Or.inl (by linarith : -1 < p - 1))]
    simp [Real.zero_rpow hp.ne', sub_add_cancel]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact Real.rpow_nonneg hu.1.le _

private theorem lintegral_rpow_Ioi {p κ : ℝ} (hpk : p < κ) :
    (∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (u ^ (p - κ - 1))) =
      ENNReal.ofReal (1 / (κ - p)) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : p - κ - 1 < -1)
    (by norm_num : (0 : ℝ) < 1)
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_Ioi_rpow_of_lt (by linarith : p - κ - 1 < -1) (by norm_num : (0 : ℝ) < 1)]
    congr 1
    simp only [Real.one_rpow]
    rw [show p - κ - 1 + 1 = -(κ - p) by ring, neg_div_neg_eq]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact Real.rpow_nonneg (by linarith [mem_Ioi.mp hu]) _

/-- An absolute-moment bound from a polynomial tail: splitting the tail integral at one gives
`E|X|^p ≤ p (1/p + C/(κ - p))`. -/
theorem lintegral_abs_rpow_le_of_polynomial_tail [IsProbabilityMeasure μ]
    (hX : AEMeasurable X μ) {C κ p : ℝ} (hC : 0 ≤ C) (hp : 0 < p) (hpk : p < κ)
    (htail : ∀ u : ℝ, 0 ≤ u → μ {ω | u < |X ω|} ≤ ENNReal.ofReal (C * (1 + u) ^ (-κ))) :
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ) ≤
      ENNReal.ofReal p * (ENNReal.ofReal (1 / p) +
        ENNReal.ofReal C * ENNReal.ofReal (1 / (κ - p))) := by
  rw [lintegral_abs_rpow_eq_tail hX hp]
  apply mul_le_mul' le_rfl
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext u
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hu
      rcases le_or_gt u 1 with h | h
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr h
    · rintro (h | h)
      · exact h.1
      · linarith
  rw [hsplit, lintegral_union measurableSet_Ioi (by
    rw [disjoint_left]; intro u hu hv; exact (not_lt_of_ge hu.2) hv)]
  apply add_le_add
  · calc
      _ ≤ ∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ (p - 1)) := by
        apply lintegral_mono
        intro u
        exact (mul_le_mul' (prob_le_one) le_rfl).trans_eq (one_mul _)
      _ = _ := lintegral_rpow_Ioc hp
  · calc
      _ ≤ ∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal C * ENNReal.ofReal (u ^ (p - κ - 1)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := lt_trans zero_lt_one hu
        have hk : (1 + u) ^ (-κ) ≤ u ^ (-κ) :=
          Real.rpow_le_rpow_of_nonpos hu0 (by linarith) (by linarith)
        calc
          _ ≤ ENNReal.ofReal (C * u ^ (-κ)) * ENNReal.ofReal (u ^ (p - 1)) :=
            mul_le_mul' ((htail u hu0.le).trans
              (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hk hC))) le_rfl
          _ = _ := by
            rw [ENNReal.ofReal_mul hC, mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hu0.le _),
              ← Real.rpow_add hu0]
            congr 3
            ring
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_rpow_Ioi hpk]

/-- An exponential tail `C e^{-cu}` is a polynomial tail of order three:
`C e^{-cu} ≤ (6 C e^c / c³) (1 + u)^{-3}` for `u ≥ 0`. -/
theorem exp_tail_le_polynomial_tail {C c u : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hu : 0 ≤ u) :
    C * Real.exp (-(c * u)) ≤ 6 * C * Real.exp c / c ^ 3 * (1 + u) ^ (-(3 : ℝ)) := by
  have h1u : 0 < 1 + u := by linarith
  have hpow : (1 + u) ^ (-(3 : ℝ)) = ((1 + u) ^ 3)⁻¹ := by
    rw [Real.rpow_neg h1u.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow]
  -- `e^{c(1+u)} ≥ (c(1+u))³/6`
  have h3 : (c * (1 + u)) ^ 3 / 6 ≤ Real.exp (c * (1 + u)) := by
    have := Real.pow_div_factorial_le_exp (x := c * (1 + u)) (by positivity) 3
    simpa [Nat.factorial] using this
  have hexp : Real.exp (-(c * u)) = Real.exp c * (Real.exp (c * (1 + u)))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  rw [hexp]
  have hE : 0 < Real.exp (c * (1 + u)) := Real.exp_pos _
  have key : (Real.exp (c * (1 + u)))⁻¹ ≤ 6 / (c ^ 3 * (1 + u) ^ 3) := by
    rw [inv_le_comm₀ hE (by positivity), inv_div]
    calc c ^ 3 * (1 + u) ^ 3 / 6 = (c * (1 + u)) ^ 3 / 6 := by ring
      _ ≤ _ := h3
  calc C * (Real.exp c * (Real.exp (c * (1 + u)))⁻¹)
      ≤ C * (Real.exp c * (6 / (c ^ 3 * (1 + u) ^ 3))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key (Real.exp_pos _).le) hC
    _ = 6 * C * Real.exp c / c ^ 3 * ((1 + u) ^ 3)⁻¹ := by field_simp

/-- **Second moment from an exponential tail at the scale `r^{1/2}`**: if
`P(|W| > s r^{1/2}) ≤ C e^{-cs}` for `s ≥ 0`, then `W²` is integrable and
`E W² ≤ (1 + 12 C e^c / c³) r`. -/
theorem integral_sq_le_of_exp_tail [IsProbabilityMeasure μ] {W : Ω → ℝ} (hW : AEMeasurable W μ)
    {C c r : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hr : 0 < r)
    (htail : ∀ s : ℝ, 0 ≤ s →
      μ {ω | s * √r < |W ω|} ≤ ENNReal.ofReal (C * Real.exp (-(c * s)))) :
    Integrable (fun ω => W ω ^ 2) μ ∧
      ∫ ω, W ω ^ 2 ∂μ ≤ (1 + 12 * C * Real.exp c / c ^ 3) * r := by
  have hq : 0 < √r := Real.sqrt_pos.2 hr
  have hX : AEMeasurable (fun ω => W ω / √r) μ := hW.div_const _
  set C' := 6 * C * Real.exp c / c ^ 3 with hC'def
  have hC' : 0 ≤ C' := by positivity
  have htailX : ∀ s : ℝ, 0 ≤ s →
      μ {ω | s < |W ω / √r|} ≤ ENNReal.ofReal (C' * (1 + s) ^ (-(3 : ℝ))) := by
    intro s hs
    have hset : {ω | s < |W ω / √r|} = {ω | s * √r < |W ω|} := by
      ext ω
      simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hq, lt_div_iff₀ hq]
    rw [hset]
    exact (htail s hs).trans (ENNReal.ofReal_le_ofReal (exp_tail_le_polynomial_tail hC hc hs))
  have hlin := lintegral_abs_rpow_le_of_polynomial_tail hX hC' two_pos
    (by norm_num : (2 : ℝ) < 3) htailX
  have hrhs : ENNReal.ofReal 2 * (ENNReal.ofReal (1 / 2) +
      ENNReal.ofReal C' * ENNReal.ofReal (1 / (3 - 2))) = ENNReal.ofReal (1 + 2 * C') := by
    rw [← ENNReal.ofReal_mul hC', ← ENNReal.ofReal_add (by norm_num) (by positivity),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [hrhs] at hlin
  have hfin : (∫⁻ ω, ENNReal.ofReal (|W ω / √r| ^ (2 : ℝ)) ∂μ) ≠ ∞ :=
    (hlin.trans_lt ENNReal.ofReal_lt_top).ne
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (|W ω / √r| ^ (2 : ℝ))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable hX).pow_const _)
  have heq : ∀ ω, (ENNReal.ofReal (|W ω / √r| ^ (2 : ℝ))).toReal = W ω ^ 2 / r := by
    intro ω
    rw [ENNReal.toReal_ofReal (by positivity), Real.rpow_two, sq_abs, div_pow,
      Real.sq_sqrt hr.le]
  have hint : Integrable (fun ω => W ω ^ 2 / r) μ := by
    have := integrable_toReal_of_lintegral_ne_top hmeas hfin
    simp_rw [heq] at this
    exact this
  refine ⟨(hint.const_mul r).congr (ae_of_all _ fun ω => by
    simp only
    field_simp), ?_⟩
  have hval : ∫ ω, W ω ^ 2 / r ∂μ ≤ 1 + 2 * C' := by
    have h1 := integral_toReal hmeas (ae_of_all _ fun ω => ENNReal.ofReal_lt_top)
    simp_rw [heq] at h1
    rw [h1]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
  rw [integral_div, div_le_iff₀ hr] at hval
  calc ∫ ω, W ω ^ 2 ∂μ ≤ (1 + 2 * C') * r := hval
    _ = _ := by rw [hC'def]; ring

/-! ### One-sided bounds from the second moment -/

/-- **A centred variable is not below `-s` with probability close to one**: if `E W = 0` and
`E W² ≤ V`, then `P(W ≤ -s) ≤ max(1/2, e^{-s²/(4V)})`. -/
theorem measure_le_neg_le_of_integral_sq_le [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hW : MemLp W 2 μ) (hmean : ∫ ω, W ω ∂μ = 0) {V : ℝ} (hV : 0 < V)
    (hsq : ∫ ω, W ω ^ 2 ∂μ ≤ V) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | W ω ≤ -s} ≤ max (1 / 2) (Real.exp (-(s ^ 2 / (4 * V)))) := by
  set p := μ.real {ω | W ω ≤ -s}
  rcases le_or_gt p (1 / 2) with hp | hp
  · exact hp.trans (le_max_left _ _)
  refine le_trans ?_ (le_max_right _ _)
  rcases hs.eq_or_lt with rfl | hs0
  · have h1 : p ≤ 1 := measureReal_le_one
    simpa using h1
  have hWi : Integrable W μ := hW.integrable one_le_two
  have hm : AEStronglyMeasurable W μ := hW.aestronglyMeasurable
  set A := {ω | W ω ≤ -s}
  set Bp := {ω | 0 < W ω}
  have hAm : NullMeasurableSet A μ := nullMeasurableSet_le hm.aemeasurable aemeasurable_const
  have hBm : NullMeasurableSet Bp μ := nullMeasurableSet_lt aemeasurable_const hm.aemeasurable
  -- `E W₊ = E W₋`
  have hpos : Integrable (fun ω => max (W ω) 0) μ := hWi.pos_part
  have hneg : Integrable (fun ω => max (-W ω) 0) μ := hWi.neg_part
  have hsplit : ∫ ω, max (W ω) 0 ∂μ = ∫ ω, max (-W ω) 0 ∂μ := by
    have : ∫ ω, (max (W ω) 0 - max (-W ω) 0) ∂μ = ∫ ω, W ω ∂μ :=
      integral_congr_ae (ae_of_all _ fun ω => by
        dsimp only
        rcases le_total (W ω) 0 with h | h
        · rw [max_eq_right h, max_eq_left (by linarith)]; ring
        · rw [max_eq_left h, max_eq_right (by linarith)]; ring)
    rw [integral_sub hpos hneg, hmean] at this
    linarith
  -- `s p ≤ E W₋ = E W₊`
  have hlow : s * p ≤ ∫ ω, max (W ω) 0 ∂μ := by
    rw [hsplit]
    have hind : ∀ ω, A.indicator (fun _ => s) ω ≤ max (-W ω) 0 := by
      intro ω
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]
        have : W ω ≤ -s := hω
        exact le_max_of_le_left (by linarith)
      · rw [Set.indicator_of_notMem hω]; exact le_max_right _ _
    have := integral_mono ((integrable_const s).indicator₀ hAm) hneg hind
    rwa [integral_indicator₀ hAm, setIntegral_const, smul_eq_mul, mul_comm] at this
  -- `P(W > 0) ≤ 1 - p`
  have hdisj : μ.real Bp ≤ 1 - p := by
    have hsub : Bp ⊆ Aᶜ := by
      intro ω hω hA
      have h1 : 0 < W ω := hω
      have h2 : W ω ≤ -s := hA
      linarith
    have := measureReal_mono hsub (μ := μ)
    rw [measureReal_compl₀ hAm, probReal_univ] at this
    exact this
  -- `E W₊ ≤ (L P(W > 0) + E W²/L)/2` for `L > 0`, applied with `L = V/(s p)`
  have hp0 : 0 < p := by linarith
  have hsp : 0 < s * p := mul_pos hs0 hp0
  set L := V / (s * p) with hLdef
  have hL : 0 < L := div_pos hV hsp
  have hLsp : L * (s * p) = V := by rw [hLdef]; field_simp
  have hpt : ∀ ω, max (W ω) 0 ≤ (L * Bp.indicator (fun _ => (1 : ℝ)) ω + W ω ^ 2 / L) / 2 := by
    intro ω
    by_cases hω : ω ∈ Bp
    · have hw : 0 < W ω := hω
      simp only [Set.indicator_of_mem hω, mul_one]
      rw [max_eq_left hw.le]
      have h1 : (L + W ω ^ 2 / L) / 2 - W ω = (L - W ω) ^ 2 / (2 * L) := by
        field_simp; ring
      have h2 : 0 ≤ (L - W ω) ^ 2 / (2 * L) := by positivity
      linarith
    · have hw : W ω ≤ 0 := not_lt.1 hω
      simp only [Set.indicator_of_notMem hω, mul_zero, zero_add]
      rw [max_eq_right hw]
      positivity
  have hint1 : Integrable (fun ω => (L * Bp.indicator (fun _ => (1 : ℝ)) ω + W ω ^ 2 / L) / 2)
      μ :=
    ((((integrable_const (1 : ℝ)).indicator₀ hBm).const_mul L).add
      (hW.integrable_sq.div_const L)).div_const 2
  have hEW : ∫ ω, max (W ω) 0 ∂μ ≤ (L * (1 - p) + s * p) / 2 := by
    calc ∫ ω, max (W ω) 0 ∂μ
        ≤ ∫ ω, (L * Bp.indicator (fun _ => (1 : ℝ)) ω + W ω ^ 2 / L) / 2 ∂μ :=
          integral_mono hpos hint1 hpt
      _ = (L * μ.real Bp + (∫ ω, W ω ^ 2 ∂μ) / L) / 2 := by
          rw [integral_div, integral_add (((integrable_const (1 : ℝ)).indicator₀ hBm).const_mul L)
            (hW.integrable_sq.div_const L), integral_const_mul, integral_indicator₀ hBm,
            setIntegral_const, integral_div, smul_eq_mul, mul_one]
      _ ≤ (L * (1 - p) + V / L) / 2 := by gcongr
      _ = (L * (1 - p) + s * p) / 2 := by
          rw [show V / L = s * p by rw [← hLsp]; field_simp]
  -- conclude: `s² p² ≤ (1 - p) V`, so `1 - p ≥ s²/(4V)`
  have h3 : s * p ≤ L * (1 - p) := by linarith
  have hs2 : s ^ 2 * p ^ 2 ≤ (1 - p) * V :=
    calc s ^ 2 * p ^ 2 = s * p * (s * p) := by ring
      _ ≤ L * (1 - p) * (s * p) := mul_le_mul_of_nonneg_right h3 hsp.le
      _ = (1 - p) * (L * (s * p)) := by ring
      _ = (1 - p) * V := by rw [hLsp]
  have hp1 : p ≤ 1 - s ^ 2 / (4 * V) := by
    have : s ^ 2 / (4 * V) ≤ 1 - p := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg s) (by linarith : (0 : ℝ) ≤ p - 1 / 2))
        (by linarith : (0 : ℝ) ≤ p + 1 / 2)]
    linarith
  exact hp1.trans (by
    have := Real.add_one_le_exp (-(s ^ 2 / (4 * V)))
    linarith)

/-- The upper side: if `E W = 0` and `E W² ≤ V`, then `P(W ≥ s) ≤ max(1/2, e^{-s²/(4V)})`. -/
theorem measure_le_ge_le_of_integral_sq_le [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hW : MemLp W 2 μ) (hmean : ∫ ω, W ω ∂μ = 0) {V : ℝ} (hV : 0 < V)
    (hsq : ∫ ω, W ω ^ 2 ∂μ ≤ V) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | s ≤ W ω} ≤ max (1 / 2) (Real.exp (-(s ^ 2 / (4 * V)))) := by
  have h := measure_le_neg_le_of_integral_sq_le (W := fun ω => -W ω) hW.neg
    (by rw [integral_neg, hmean, neg_zero]) hV (by simpa using hsq) hs
  have : {ω | -W ω ≤ -s} = {ω | s ≤ W ω} := by ext ω; simp
  rwa [this] at h

end CurvatureVariance.Infra.FPP
