/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Contracts.Inputs
public import CurvatureVariance.Paper.Contracts.Mean
public import CurvatureVariance.Paper.Contracts.Moments
import CurvatureVariance.Infra.FPP.TimeConstant
import CurvatureVariance.Paper.Proofs.Mean.Domain
import CurvatureVariance.Paper.Proofs.Mean.MeanAtN
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Proposition `prop:induction`

The paper proves Proposition `prop:induction` as in the proof of [AB26, Proposition 3.1], whose
Lean is `IsotropicVariance.Paper.Proofs.Induction.improvementStatement_of_contracts`.

* `lintegral_exp_abs_sub_integral_le`, `isOs_abs_sub_integral_of_evariance_le`: the step from the
  variance to `O₁`, by the Cauchy–Schwarz inequality, as in the proof of [AB26, Proposition 3.1].
  They are `IsotropicVariance.Paper.Proofs.Induction.lintegral_exp_abs_sub_integral_le` and
  `IsotropicVariance.Paper.Proofs.Induction.isOs_abs_sub_integral_of_evariance_le` of the continuum
  library, with `Cited.IsOs` read as `CurvatureVariance.IsOs`.
* `evariance_div_le_of_le`: the form of the hypothesis of Lemma `lem:smallmean`, as in
  `IsotropicVariance.Paper.Proofs.Induction.evariance_div_le`.
* `exists_quarter_displacement_of`, `exists_mean_quarter`: equation `eq:rounding` gives `y₀`, a path
  of at most `C` edges joins `(4s, 4y₀)` to `(N, y)`, and subadditivity through the points
  `k(s, y₀)` gives the first inequality of the display in the proof of Proposition `prop:induction`.
  With `RoundingStatement` as a hypothesis.
* `isOs_add_const_of_sum`: equation `eq:sum` with a constant term, from `SignedOsSumStatement`.
* `improvementAllKStatement_of`: Proposition `prop:induction` for every large `K`.

The case of `RangeA` is decided first, as in the model (the text before equation `eq:regime`): off
equation `eq:regime` the conclusion is `ClassicalRangeStatement`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

section Exponential

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The exponential moment from equation `eq:parent`** (the proof of [AB26, Proposition 3.1]):
if `|Y − c| − Cθ ≤ O₁(θ/100)`, then `E exp(8|Y − EY|/θ) ≤ 2 e^{16C + 1}`. As
`IsotropicVariance.Paper.Proofs.Induction.lintegral_exp_abs_sub_integral_le` in the continuum
library. -/
theorem lintegral_exp_abs_sub_integral_le [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : Integrable Y P) {c C θ : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    (h : CurvatureVariance.IsOs P 1 (θ / 100) (fun ω => |Y ω - c| - C * θ)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (8 * |Y ω - ∫ ω', Y ω' ∂P| / θ)) ∂P ≤
      ENNReal.ofReal (2 * Real.exp (16 * C + 1)) := by
  set W : Ω → ℝ := fun ω => max (|Y ω - c| - C * θ) 0 with hW
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => le_max_right _ _
  have hWle : ∀ ω, |Y ω - c| ≤ C * θ + W ω := fun ω => by
    have := le_max_left (|Y ω - c| - C * θ) 0
    simp only [W]; linarith
  have hWle' : ∀ ω, W ω ≤ |Y ω - c| := fun ω => by
    refine max_le (by linarith [mul_nonneg hC hθ.le]) (abs_nonneg _)
  have hWm : AEMeasurable W P := h.1.max aemeasurable_const
  have hYc : Integrable (fun ω => |Y ω - c|) P := (hY.sub (integrable_const c)).abs
  have hWi : Integrable W P :=
    hYc.mono' hWm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hW0 ω)]; exact hWle' ω)
  have hθ100 : 0 < θ / 100 := by positivity
  have hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (W ω / (θ / 100))) ∂P ≤ 2 := by
    simpa only [Real.rpow_one, W] using h.2
  -- the mean of `W`
  have hEW : ∫ ω, W ω ∂P ≤ θ / 50 := by
    have h1 : ∫⁻ ω, ENNReal.ofReal (W ω) ∂P ≤ ENNReal.ofReal (θ / 50) := by
      calc ∫⁻ ω, ENNReal.ofReal (W ω) ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal (θ / 100) *
              ENNReal.ofReal (Real.exp (W ω / (θ / 100))) ∂P := by
            refine lintegral_mono fun ω => ?_
            rw [← ENNReal.ofReal_mul hθ100.le]
            refine ENNReal.ofReal_le_ofReal ?_
            have := Real.add_one_le_exp (W ω / (θ / 100))
            have h3 : W ω / (θ / 100) ≥ 0 := div_nonneg (hW0 ω) hθ100.le
            calc W ω = θ / 100 * (W ω / (θ / 100)) := by field_simp
              _ ≤ θ / 100 * Real.exp (W ω / (θ / 100)) :=
                  mul_le_mul_of_nonneg_left (by linarith) hθ100.le
        _ = ENNReal.ofReal (θ / 100) *
              ∫⁻ ω, ENNReal.ofReal (Real.exp (W ω / (θ / 100))) ∂P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (θ / 100) * 2 := by gcongr
        _ = ENNReal.ofReal (θ / 50) := by
            rw [show θ / 50 = θ / 100 * 2 by ring,
              ENNReal.ofReal_mul hθ100.le, ENNReal.ofReal_ofNat]
    rw [← ofReal_integral_eq_lintegral_ofReal hWi (Filter.Eventually.of_forall hW0)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have hmean : |(∫ ω', Y ω' ∂P) - c| ≤ C * θ + θ / 50 := by
    have h1 : |∫ ω, (Y ω - c) ∂P| ≤ ∫ ω, |Y ω - c| ∂P := abs_integral_le_integral_abs
    rw [integral_sub hY (integrable_const c)] at h1
    simp only [integral_const, probReal_univ, one_smul] at h1
    have h2 : ∫ ω, |Y ω - c| ∂P ≤ ∫ ω, (C * θ + W ω) ∂P :=
      integral_mono hYc ((integrable_const _).add hWi) hWle
    rw [integral_add (integrable_const _) hWi] at h2
    simp only [integral_const, probReal_univ, one_smul] at h2
    linarith
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (8 * |Y ω - ∫ ω', Y ω' ∂P| / θ)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (16 * C + 1)) *
          ENNReal.ofReal (Real.exp (W ω / (θ / 100))) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.exp_add, Real.exp_le_exp]
        have h1 : |Y ω - ∫ ω', Y ω' ∂P| ≤ |Y ω - c| + |(∫ ω', Y ω' ∂P) - c| := by
          calc |Y ω - ∫ ω', Y ω' ∂P| = |(Y ω - c) - ((∫ ω', Y ω' ∂P) - c)| := by ring_nf
            _ ≤ _ := abs_sub _ _
        have h2 : 8 * |Y ω - ∫ ω', Y ω' ∂P| ≤ 8 * (2 * C * θ + θ / 50 + W ω) := by
          nlinarith [hWle ω]
        have h3 : 8 * |Y ω - ∫ ω', Y ω' ∂P| / θ ≤ 8 * (2 * C * θ + θ / 50 + W ω) / θ :=
          div_le_div_of_nonneg_right h2 hθ.le
        have h4 : 8 * (2 * C * θ + θ / 50 + W ω) / θ = 16 * C + 8 / 50 + 8 * (W ω / θ) := by
          field_simp
          ring
        have h5 : W ω / (θ / 100) = 100 * (W ω / θ) := by field_simp
        have h6 : 0 ≤ W ω / θ := div_nonneg (hW0 ω) hθ.le
        rw [h5]
        linarith
    _ = ENNReal.ofReal (Real.exp (16 * C + 1)) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (W ω / (θ / 100))) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (16 * C + 1)) * 2 := by gcongr
    _ = ENNReal.ofReal (2 * Real.exp (16 * C + 1)) := by
        rw [mul_comm 2, ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_ofNat]

/-- **From a small variance to `O₁(θ/4)`** (the proof of [AB26, Proposition 3.1]): `eˣ − 1 ≤ x eˣ`
and the Cauchy–Schwarz inequality give
`E exp(4|Y − EY|/θ) ≤ 1 + (16 Var(Y)/θ²)^{1/2} (E exp(8|Y − EY|/θ))^{1/2}`. As
`IsotropicVariance.Paper.Proofs.Induction.isOs_abs_sub_integral_of_evariance_le` in the continuum
library. -/
theorem isOs_abs_sub_integral_of_evariance_le [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) {θ v B : ℝ} (hθ : 0 < θ) (hv : 0 ≤ v)
    (hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (8 * |Y ω - ∫ ω', Y ω' ∂P| / θ)) ∂P ≤
      ENNReal.ofReal B)
    (hvar : evariance Y P ≤ ENNReal.ofReal (v * θ ^ 2)) (hvB : 16 * v * B ≤ 1) :
    CurvatureVariance.IsOs P 1 (θ / 4) (fun ω => |Y ω - ∫ ω', Y ω' ∂P|) := by
  set m : ℝ := ∫ ω', Y ω' ∂P with hm
  set x : Ω → ℝ := fun ω => 4 * |Y ω - m| / θ with hx
  have hx0 : ∀ ω, 0 ≤ x ω := fun ω => by positivity
  have hmeas : AEMeasurable (fun ω => |Y ω - m|) P :=
    (continuous_abs.measurable.comp_aemeasurable
      (hY.aestronglyMeasurable.aemeasurable.sub_const m))
  have hxm : AEMeasurable x P := (hmeas.const_mul 4).div_const θ
  refine ⟨hmeas, ?_⟩
  have hform : ∀ ω, max |Y ω - m| 0 / (θ / 4) = x ω := fun ω => by
    rw [max_eq_left (abs_nonneg _)]; simp only [x]; field_simp
  simp only [Real.rpow_one, hform]
  -- pointwise
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (x ω)) ≤
      1 + ENNReal.ofReal (x ω) * ENNReal.ofReal (Real.exp (x ω)) := fun ω => by
    have h1 := Real.add_one_le_exp (-x ω)
    rw [Real.exp_neg] at h1
    have h2 := Real.exp_pos (x ω)
    have h3 : Real.exp (x ω) ≤ 1 + x ω * Real.exp (x ω) := by
      have := mul_le_mul_of_nonneg_left h1 h2.le
      rw [mul_add, mul_inv_cancel₀ h2.ne'] at this
      linarith
    calc ENNReal.ofReal (Real.exp (x ω))
        ≤ ENNReal.ofReal (1 + x ω * Real.exp (x ω)) := ENNReal.ofReal_le_ofReal h3
      _ = 1 + ENNReal.ofReal (x ω) * ENNReal.ofReal (Real.exp (x ω)) := by
        rw [ENNReal.ofReal_add zero_le_one (mul_nonneg (hx0 ω) h2.le),
          ENNReal.ofReal_mul (hx0 ω), ENNReal.ofReal_one]
  have hfm : AEMeasurable (fun ω => ENNReal.ofReal (x ω)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable hxm
  have hgm : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (x ω))) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (Real.measurable_exp.comp_aemeasurable hxm)
  have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hfm hgm
  -- the two factors
  have hA : ∫⁻ ω, ENNReal.ofReal (x ω) ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal (16 * v) := by
    have e1 : ∀ ω, ENNReal.ofReal (x ω) ^ (2 : ℝ) =
        ENNReal.ofReal (16 / θ ^ 2) * ENNReal.ofReal ((Y ω - m) ^ 2) := fun ω => by
      rw [ENNReal.ofReal_rpow_of_nonneg (hx0 ω) (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [x, Real.rpow_two]
      rw [div_pow, mul_pow, sq_abs]
      field_simp
      ring
    simp_rw [e1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← evariance_eq_lintegral_ofReal]
    calc ENNReal.ofReal (16 / θ ^ 2) * evariance Y P
        ≤ ENNReal.ofReal (16 / θ ^ 2) * ENNReal.ofReal (v * θ ^ 2) := by gcongr
      _ = ENNReal.ofReal (16 * v) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
  have hG : ∫⁻ ω, ENNReal.ofReal (Real.exp (x ω)) ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal B := by
    refine le_trans (le_of_eq ?_) hexp
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2
    simp only [x]; ring
  have hone : (∫⁻ ω, ENNReal.ofReal (x ω) * ENNReal.ofReal (Real.exp (x ω)) ∂P) ≤ 1 := by
    refine hHold.trans ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc (_ * _) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (16 * v) * ENNReal.ofReal B) ^ (1 / 2 : ℝ) := by
          gcongr
      _ ≤ (ENNReal.ofReal 1) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          gcongr
      _ = 1 := by simp
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (x ω)) ∂P
      ≤ ∫⁻ ω, (1 + ENNReal.ofReal (x ω) * ENNReal.ofReal (Real.exp (x ω))) ∂P :=
        lintegral_mono hpt
    _ = 1 + ∫⁻ ω, ENNReal.ofReal (x ω) * ENNReal.ofReal (Real.exp (x ω)) ∂P := by
        rw [lintegral_add_left' aemeasurable_const]
        simp
    _ ≤ 1 + 1 := by gcongr
    _ = 2 := by norm_num

/-- A bound on `Var X` gives the bound on `Var[X/Q]` that Lemma `lem:smallmean` asks for. -/
theorem evariance_div_le_of_le {X : Ω → ℝ} {v Q : ℝ} (hQ : 0 < Q)
    (h : evariance X P ≤ ENNReal.ofReal (v * Q ^ 2)) :
    evariance (fun ω => X ω / Q) P ≤ ENNReal.ofReal v := by
  have he : (fun ω => X ω / Q) = fun ω => Q⁻¹ * X ω := by
    funext ω
    rw [div_eq_inv_mul]
  rw [he, evariance_mul]
  calc ENNReal.ofReal (Q⁻¹ ^ 2) * evariance X P
      ≤ ENNReal.ofReal (Q⁻¹ ^ 2) * ENNReal.ofReal (v * Q ^ 2) := by gcongr
    _ = ENNReal.ofReal v := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      field_simp

/-- **Equation `eq:sum` with a constant term**: `X ≤ O₁(θ)` and a constant `b > 0` give
`X + b ≤ O₁(θ + b/log 2)`, by `SignedOsSumStatement`, since `b ≤ O₁(b/log 2)`. -/
theorem isOs_add_const_of_sum (hSum : SignedOsSumStatement.{0, 0}) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {θ b : ℝ}
    (hθ : 0 < θ) (hb : 0 < b) (hX : CurvatureVariance.IsOs P 1 θ X) :
    CurvatureVariance.IsOs P 1 (θ + b / Real.log 2) (fun ω => X ω + b) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hc : CurvatureVariance.IsOs P 1 (b / Real.log 2) (fun _ : Ω => b) := by
    refine ⟨aemeasurable_const, ?_⟩
    have heq : b / (b / Real.log 2) = Real.log 2 := by field_simp
    simp only [max_eq_left hb.le, heq, Real.rpow_one, Real.exp_log two_pos,
      ENNReal.ofReal_ofNat, lintegral_const, measure_univ, mul_one]
    exact le_rfl
  obtain ⟨C, -, hC1, hsum⟩ := hSum 1 zero_lt_one
  have hC : C = 1 := hC1 le_rfl
  let scales : Fin 2 → ℝ := ![θ, b / Real.log 2]
  let vars : Fin 2 → Ω → ℝ := ![X, fun _ => b]
  have hh := hsum P Finset.univ Finset.univ_nonempty scales
    (fun i _ => by fin_cases i <;> dsimp [scales] <;> positivity) vars
    (fun i _ => by fin_cases i; exact hX; exact hc)
  simpa only [hC, one_mul, Fin.sum_univ_two, scales, vars, Matrix.cons_val_zero,
    Matrix.cons_val_one] using hh

end Exponential

/-- **The point `y₀`** (the proof of Proposition `prop:induction`): by equation `eq:rounding`, there
is `y₀` as in Lemma `lem:smallmean` at `s = ⌊N/4⌋` with `|y₀ − sy/N| ≤ 2(d−1)^{1/2}`, and
`(N, y) − 4(s, y₀)` is bounded. `RoundingStatement` is a hypothesis. -/
theorem exists_quarter_displacement_of {m : ℕ} (hRound : RoundingStatement m) (M : Model m)
    (hM : M.Standing) {bd : Bounds m} (hfit : M.Fits bd)
    {N : ℕ} (hN : 8 ≤ N) {y : Fin m → ℤ} (hy : y ∈ premiseDomain M N)
    (hR : 2 * Real.sqrt m ≤ (N / 4 : ℕ) * (N : ℝ) ^ (M.δ / 100 - 1 / 4)) :
    ∃ y₀ : Fin m → ℤ,
      ‖transversePoint y₀ - ((N / 4 : ℕ) : ℝ) • M.t₀‖ ≤
        (N / 4 : ℕ) * (N : ℝ) ^ (M.δ / 100 - 1 / 4) ∧
      ‖point (((N : ℤ), y) - 4 • (((N / 4 : ℕ) : ℤ), y₀))‖ ≤
        4 + 4 * (bd.T + 1) + 8 * Real.sqrt m := by
  let s := N / 4
  let c : ℝ := (s : ℝ) / N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg s) hN0.le
  obtain ⟨_, _, hs₁, hs₂⟩ := quarter_length_bounds hN
  have hscaled : ‖c • transversePoint y - (s : ℝ) • M.t₀‖ ≤
      (s : ℝ) * (N : ℝ) ^ (M.δ / 100 - 1 / 4) := by
    have he : c • transversePoint y - (s : ℝ) • M.t₀ =
        c • (transversePoint y - (N : ℝ) • M.t₀) := by
      rw [smul_sub, smul_smul, div_mul_cancel₀ _ hN0.ne']
    rw [he, norm_smul, Real.norm_of_nonneg hc]
    calc c * ‖transversePoint y - (N : ℝ) • M.t₀‖ ≤
          c * (N : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) :=
            mul_le_mul_of_nonneg_left hy hc
      _ = _ := by
        rw [show (3 : ℝ) / 4 + M.δ / 100 = (M.δ / 100 - 1 / 4) + 1 by ring,
          Real.rpow_add hN0, Real.rpow_one]
        dsimp only [c]
        field_simp
  obtain ⟨y₀, hy₀, hround⟩ := hRound
    ((s : ℝ) • M.t₀) (c • transversePoint y)
    ((s : ℝ) * (N : ℝ) ^ (M.δ / 100 - 1 / 4)) hR hscaled
  refine ⟨y₀, hy₀, ?_⟩
  have hys := norm_transverse_le_of_mem_fit hM hfit
    (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)) hy
  have hd : 0 ≤ ((N : ℝ) - 4 * s) / N := div_nonneg hs₁ hN0.le
  have hmain : ‖(((N : ℝ) - 4 * s) / N) • transversePoint y‖ ≤
      4 * (bd.T + 1) := by
    rw [norm_smul, Real.norm_of_nonneg hd]
    calc ((N : ℝ) - 4 * s) / N * ‖transversePoint y‖ ≤
          ((N : ℝ) - 4 * s) / N * ((bd.T + 1) * N) :=
            mul_le_mul_of_nonneg_left hys hd
      _ = ((N : ℝ) - 4 * s) * (bd.T + 1) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hs₂.le
        (by linarith only [norm_nonneg M.t₀, hfit.t₀_le])
  have htrans : ‖transversePoint y - (4 : ℝ) • transversePoint y₀‖ ≤
      4 * (bd.T + 1) + 8 * Real.sqrt m := by
    have he : transversePoint y - (4 : ℝ) • transversePoint y₀ =
        (((N : ℝ) - 4 * s) / N) • transversePoint y -
          (4 : ℝ) • (transversePoint y₀ - c • transversePoint y) := by
      ext j
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      dsimp only [c]
      field_simp
      ring
    rw [he]
    refine (norm_sub_le _ _).trans (add_le_add hmain ?_)
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    linarith only [mul_le_mul_of_nonneg_left hround (by norm_num : (0 : ℝ) ≤ 4)]
  let r : Vertex m := ((N : ℤ), y) - 4 • (((s : ℕ) : ℤ), y₀)
  have hf : |(r.1 : ℝ)| ≤ 4 := by
    change |(((N : ℤ) - 4 * (s : ℤ) : ℤ) : ℝ)| ≤ 4
    push_cast
    rw [abs_of_nonneg hs₁]
    exact hs₂.le
  have hr : transversePoint r.2 = transversePoint y - (4 : ℝ) • transversePoint y₀ := by
    ext j
    change ((y j - (4 : ℕ) • y₀ j : ℤ) : ℝ) = (y j : ℝ) - 4 * (y₀ j : ℝ)
    simp only [nsmul_eq_mul, Int.cast_sub, Int.cast_mul]
    norm_num
  have hT : 0 ≤ bd.T := (norm_nonneg _).trans hfit.t₀_le
  apply le_of_sq_le_sq _ (by positivity)
  rw [norm_point_sq, hr]
  have hf2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)).mpr hf
  have ht2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htrans
  simp only [sq_abs] at hf2
  nlinarith only [hf2, ht2, hT, Real.sqrt_nonneg (m : ℝ)]

/-- **The first inequality of the display** (the proof of Proposition `prop:induction`): a path of
at most `C` edges joins `(4s, 4y₀)` to `(N, y)`, and subadditivity through the points `k(s, y₀)`,
`0 ≤ k ≤ 4`, gives `E[T] − μ(N,y) ≤ 4(E[T(0,(s,y₀))] − μ(s,y₀)) + C`, at `s = ⌊N/4⌋`. -/
theorem exists_mean_quarter {m : ℕ} (hRound : RoundingStatement m) (bd : Bounds m)
    (hbd : bd.Valid) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd → ∀ N : ℕ, N₀ ≤ N →
      ∀ y ∈ premiseDomain M N, ∃ y₀ : Fin m → ℤ,
        ‖transversePoint y₀ - ((N / 4 : ℕ) : ℝ) • M.t₀‖ ≤
          (N / 4 : ℕ) * (N : ℝ) ^ (M.δ / 100 - 1 / 4) ∧
        (∫ ω, passageTimeReal ω 0 ((N : ℤ), y) ∂M.P) - M.μ.1 (point ((N : ℤ), y)) ≤
          4 * ((∫ ω, passageTimeReal ω 0 (((N / 4 : ℕ) : ℤ), y₀) ∂M.P) -
            M.μ.1 (point (((N / 4 : ℕ) : ℤ), y₀))) + C := by
  have : IsProbabilityMeasure bd.law.F := hbd.law.probF
  obtain ⟨α, hα, hexp⟩ := hbd.law.assumptionW.1
  have hF := integrable_coe_of_exp hα hexp
  obtain ⟨hi, hhi, hmu⟩ := exists_seminorm_le bd.law.μ.1
  let Cm : ℝ := ((m : ℝ) + 1) * ∫ t, (t : ℝ) ∂bd.law.F
  have hCm : 0 ≤ Cm := mul_nonneg (by positivity)
    (integral_nonneg fun t => NNReal.coe_nonneg t)
  let C : ℝ := (Cm + hi) * (4 + 4 * (bd.T + 1) + 8 * Real.sqrt m)
  have hgrowthR : Tendsto (fun N : ℕ => (N : ℝ) ^
      ((3 : ℝ) / 4 + bd.law.δ / 100)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith only [hbd.law.delta_pos])).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1
    (hgrowthR.eventually (eventually_ge_atTop (16 * Real.sqrt m)))
  refine ⟨C, max N₃ 8, ?_⟩
  intro M hM hfit N hN y hy
  have : IsProbabilityMeasure M.P := hM.probP
  have : IsProbabilityMeasure M.F := hM.probF
  have hF : Integrable (fun t : ℝ≥0 => (t : ℝ)) M.F := by rw [hfit.F_eq]; exact hF
  have hI := IsIIDWeights.integrable_passageTime hM.iid hF
  have hT := IsIIDWeights.measurePreserving_translate hM.iid
  have hmu : ∀ x, M.μ.1 x ≤ hi * ‖x‖ := by rw [hfit.μ_eq]; exact hmu
  have hN8 : 8 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hs₁, _, _, _⟩ := quarter_length_bounds hN8
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR : 2 * Real.sqrt m ≤ (N / 4 : ℕ) * (N : ℝ) ^ (M.δ / 100 - 1 / 4) := by
    have hg := hN₃ N ((le_max_left _ _).trans hN)
    rw [← hfit.δ_eq] at hg
    have hh := mul_le_mul_of_nonneg_right hs₁
      (Real.rpow_nonneg hNpos.le (M.δ / 100 - 1 / 4))
    have he : (N : ℝ) / 8 * (N : ℝ) ^ (M.δ / 100 - 1 / 4) =
        (N : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 8 := by
      rw [show (3 : ℝ) / 4 + M.δ / 100 = 1 + (M.δ / 100 - 1 / 4) by ring,
        Real.rpow_add hNpos, Real.rpow_one]
      ring
    rw [he] at hh
    linarith only [hg, hh]
  obtain ⟨y₀, hy₀, hres⟩ := exists_quarter_displacement_of hRound M hM hfit hN8 hy hR
  refine ⟨y₀, hy₀, ?_⟩
  let x : Vertex m := ((N : ℤ), y)
  let v : Vertex m := (((N / 4 : ℕ) : ℤ), y₀)
  let r : Vertex m := x - 4 • v
  have hsplit : x = 4 • v + r := by dsimp [r]; abel
  have hfour : meanTime M.P x ≤ 4 * meanTime M.P v + Cm * ‖point r‖ := by
    calc meanTime M.P x = meanTime M.P (4 • v + r) := congrArg _ hsplit
      _ ≤ meanTime M.P (4 • v) + meanTime M.P r := meanTime_add_le hT hI _ _
      _ ≤ (4 : ℕ) * meanTime M.P v + Cm * ‖point r‖ :=
        add_le_add (meanTime_nsmul_le hT hI 4 v)
          (by simpa only [Cm, hfit.F_eq] using IsIIDWeights.meanTime_le hM.iid hF r)
      _ = 4 * meanTime M.P v + Cm * ‖point r‖ := by norm_num
  have hmuhom : M.μ.1 (point ((4 : ℕ) • v)) = 4 * M.μ.1 (point v) := by
    rw [point_nsmul, map_smul_eq_mul]
    norm_num
  have hmutri : 4 * M.μ.1 (point v) ≤ M.μ.1 (point x) + hi * ‖point r‖ := by
    rw [← hmuhom]
    calc M.μ.1 (point (4 • v)) = M.μ.1 (point x - point r) := by
          rw [← point_sub]
          congr 2
          dsimp [r]
          abel
      _ ≤ M.μ.1 (point x) + M.μ.1 (point r) := map_sub_le_add _ _ _
      _ ≤ M.μ.1 (point x) + hi * ‖point r‖ := add_le_add le_rfl (hmu _)
  have hcost : (Cm + hi) * ‖point r‖ ≤ C :=
    mul_le_mul_of_nonneg_left hres (by linarith only [hCm, hhi])
  change meanTime M.P x - M.μ.1 (point x) ≤ 4 * (meanTime M.P v - M.μ.1 (point v)) + C
  linarith only [hfour, hmutri, hcost]

/-- **Proposition `prop:induction` for every large `K`** (the text of Section `sec:induction` after
the proof of Theorem `thm:main`, and the proof of Proposition `prop:induction`), from the premises
of the edge `prop:induction` of the graph in `Closing.Main`: equation `eq:parent` and Proposition
`prop:gain` fix `K`, here every large `K`, so that `Var[T/Q]` is as small as Lemma `lem:smallmean`
requires, and `|T − E[T]| ≤ O₁(Q_N/4)`. Lemma `lem:smallmean` at `s = ⌊N/4⌋` and subadditivity give
`0 ≤ E[T] − μ(N,y) ≤ Q_N/8`, where `0 ≤` is equation `eq:classical`, and equation `eq:improvement`
follows by equation `eq:sum`. -/
theorem improvementAllKStatement_of {m : ℕ} (hCR : ClassicalRangeStatement m)
    (hCl : ClassicalStatement m) (hP : ParentStatement m) (hG : GainStatement m)
    (hSM : SmallMeanStatement m) (hRound : RoundingStatement m)
    (hSum : SignedOsSumStatement.{0, 0}) : ImprovementAllKStatement m := by
  intro bd hbd
  obtain ⟨Cstar, -, hCR⟩ := hCR bd hbd
  obtain ⟨c₀, hc₀, hSM⟩ := hSM bd hbd Cstar
  obtain ⟨Cp, hCp, hP⟩ := hP bd hbd Cstar
  obtain ⟨φ, hφ, K₀, hG⟩ := hG bd hbd Cstar
  obtain ⟨Ccl, -, hCl⟩ := hCl bd hbd
  obtain ⟨Cr, Nr, hround⟩ := exists_mean_quarter hRound bd hbd
  -- the choice of `K`
  let B : ℝ := 2 * Real.exp (16 * Cp + 1)
  have hB : 0 < B := by positivity
  have hv : 0 < min c₀ (1 / (16 * B)) := lt_min hc₀ (by positivity)
  obtain ⟨K₁, hK₁⟩ := (hφ.eventually (gt_mem_nhds hv)).exists_forall_of_atTop
  refine ⟨max K₀ K₁, fun K hKK hK => ?_⟩
  have hφK : φ K < min c₀ (1 / (16 * B)) := hK₁ K ((le_max_right _ _).trans hKK)
  let v₀ : ℝ := max (φ K) 0
  have hv0 : 0 ≤ v₀ := le_max_right _ _
  have hvc : v₀ ≤ c₀ := max_le (hφK.le.trans (min_le_left _ _)) hc₀.le
  have hvB : 16 * v₀ * B ≤ 1 := by
    have h1 : v₀ ≤ 1 / (16 * B) := max_le (hφK.le.trans (min_le_right _ _)) (by positivity)
    calc 16 * v₀ * B = (16 * B) * v₀ := by ring
      _ ≤ (16 * B) * (1 / (16 * B)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by field_simp
  -- the thresholds on `N`, which depend only on `K`
  obtain ⟨N₁, hN₁⟩ := hCR K hK
  obtain ⟨N₂, hN₂⟩ := hSM K hK
  obtain ⟨N₃, hN₃⟩ := hP (1 / 8) (by norm_num) K hK
  obtain ⟨N₄, hN₄⟩ := hG K ((le_max_left _ _).trans hKK) hK
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKlarge : (4 : ℝ) ≤ K := by exact_mod_cast (show 4 ≤ K by omega)
  have hq : 0 < (1 : ℝ) / 2 - bd.law.δ / K := by
    have hdiv : bd.law.δ / K ≤ (1 : ℝ) / 4 := (div_le_iff₀ hKpos).2 (by
      linarith only [hbd.law.delta_le_one, hKlarge])
    linarith only [hdiv]
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 - bd.law.δ / K)) atTop atTop :=
    (tendsto_rpow_atTop hq).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.1 (hgrowth.eventually (eventually_ge_atTop (16 * Cr)))
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) (max N₅ (max Nr 8))), ?_⟩
  intro M hM hfit N hN A hA hprem y hy
  have : IsProbabilityMeasure M.P := hM.probP
  have h1 : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have h2 : N₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have h3 : N₃ ≤ N :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hN
  have h4 : N₄ ≤ N :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hN
  have h5 : N₅ ≤ N :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN
  have hrest : max Nr 8 ≤ N :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN
  have hNr : Nr ≤ N := (le_max_left _ _).trans hrest
  have hN8 : 8 ≤ N := (le_max_right _ _).trans hrest
  -- off equation `eq:regime`, the classical range
  by_cases hR : RangeA M K A N Cstar
  swap
  · exact hN₁ M hM hfit N h1 A hA hR y hy
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hQ : 0 < Q M K A N := mul_pos (zero_lt_one.trans_le hA) (Real.rpow_pos_of_pos hNpos _)
  obtain ⟨hs₁, hs₂, _, _⟩ := quarter_length_bounds hN8
  have hNN8 : (N : ℝ) / 8 ≤ N := by linarith only [hNpos]
  -- the variance bounds from Proposition `prop:gain`
  have hvar : ∀ ℓ : ℕ, (N : ℝ) / 8 ≤ ℓ → ℓ ≤ N → ∀ y' ∈ premiseDomain M ℓ,
      evariance (fun ω => passageTimeReal ω 0 ((ℓ : ℤ), y')) M.P ≤
        ENNReal.ofReal (v₀ * Q M K A ℓ ^ 2) := fun ℓ hℓ₁ hℓ₂ y' hy' =>
    (hN₄ M hM hfit N h4 A hA hprem hR ℓ hℓ₁ hℓ₂ y' hy').trans
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
  -- the fluctuation: equation `eq:parent` and the Cauchy–Schwarz inequality
  let T : Config m → ℝ := fun ω => passageTimeReal ω 0 ((N : ℤ), y)
  let μ₀ : ℝ := M.μ.1 (point ((N : ℤ), y))
  let e : ℝ := ∫ ω, T ω ∂M.P
  have hx : (((N : ℤ), y) : Vertex m) ≠ 0 := by
    intro h
    have hfst := congrArg Prod.fst h
    simp only [Prod.fst_zero] at hfst
    have hzero : N = 0 := by exact_mod_cast hfst
    omega
  obtain ⟨hTint, _, hlo, _⟩ := hCl M hM hfit ((N : ℤ), y) hx
  have hTm : AEMeasurable T M.P := hTint.aemeasurable
  have hvarN := hvar N hNN8 le_rfl y hy
  have hmem : MemLp T 2 M.P :=
    (evariance_lt_top_iff_memLp hTm.aestronglyMeasurable).1
      (hvarN.trans_lt ENNReal.ofReal_lt_top)
  have hyrad : ‖transversePoint y - (N : ℝ) • M.t₀‖ ≤
      7 / 4 * (N : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
    have hh := Real.rpow_nonneg hNpos.le ((3 : ℝ) / 4 + M.δ / 100)
    exact hy.trans (by linarith only [hh])
  have hparent := hN₃ M hM hfit N h3 A hA hprem hR N (by linarith only [hNpos])
    (by linarith only [hNpos]) y hyrad
  have hexpB := lintegral_exp_abs_sub_integral_le hTint hQ hCp.le hparent
  have hO : CurvatureVariance.IsOs M.P 1 (Q M K A N / 4) (fun ω => |T ω - e|) :=
    isOs_abs_sub_integral_of_evariance_le hmem hQ hv0 hexpB hvarN hvB
  -- the mean: Lemma `lem:smallmean` at `s = ⌊N/4⌋`, and subadditivity
  obtain ⟨y₀, hy₀, hquarter⟩ := hround M hM hfit N hNr y hy
  have hsmall := hN₂ M hM hfit N h2 A hA hprem hR (N / 4) hs₁ hs₂
    (fun y' hy' => by
      have hs0 : (0 : ℝ) < (N / 4 : ℕ) := by linarith only [hs₁, hNpos]
      have hQs : 0 < Q M K A (N / 4 : ℕ) :=
        mul_pos (zero_lt_one.trans_le hA) (Real.rpow_pos_of_pos hs0 _)
      exact (evariance_div_le_of_le hQs (hvar (N / 4) hs₁ (Nat.div_le_self N 4) y' hy')).trans
        (ENNReal.ofReal_le_ofReal hvc))
    y₀ hy₀
  have hqM : 0 < (1 : ℝ) / 2 - M.δ / K := by rw [hfit.δ_eq]; exact hq
  have hQmono : Q M K A (N / 4 : ℕ) ≤ Q M K A N := by
    apply mul_le_mul_of_nonneg_left _ (by linarith only [hA])
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self N 4) hqM.le
  have hCQ : Cr ≤ Q M K A N / 16 := by
    have hh : (N : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ Q M K A N := by
      simpa only [Q, one_mul] using mul_le_mul_of_nonneg_right hA
        (Real.rpow_nonneg (Nat.cast_nonneg N) ((1 : ℝ) / 2 - M.δ / K))
    have hg := hN₅ N h5
    rw [← hfit.δ_eq] at hg
    linarith only [hg, hh]
  have hbias : |e - μ₀| ≤ Q M K A N / 8 := by
    rw [abs_of_nonneg hlo]
    linarith only [hquarter, hsmall, hQmono, hCQ, hQ]
  -- equation `eq:sum`
  have hshift := isOs_add_const_of_sum hSum (by positivity : 0 < Q M K A N / 4)
    (by positivity : 0 < Q M K A N / 8) hO
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at hh
    linarith only [hh]
  have hscale : Q M K A N / 4 + (Q M K A N / 8) / Real.log 2 ≤ Q M K A N / 2 := by
    have hdiv : (Q M K A N / 8) / Real.log 2 ≤ Q M K A N / 4 := by
      apply (div_le_iff₀ (Real.log_pos one_lt_two)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hlog hQ.le]
    linarith only [hdiv]
  have hmajor := hshift.mono_scale (by norm_num) (by positivity) hscale
  have hm : AEMeasurable (fun ω => T ω - μ₀) M.P := hTm.sub_const μ₀
  refine ⟨hm, hmajor.mono (by norm_num) (by positivity)
    (by simpa only [Real.norm_eq_abs] using hm.norm) ?_⟩
  exact Eventually.of_forall fun ω =>
    (abs_sub_le (T ω) e μ₀).trans (add_le_add le_rfl hbias)

end CurvatureVariance.Paper.Mean
