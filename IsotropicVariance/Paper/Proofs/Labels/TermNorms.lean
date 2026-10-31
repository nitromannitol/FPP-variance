/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Statements.Cited.IsOs
public import IsotropicVariance.Infra.Os.Moments
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# `L^p` bounds for the terms of equation `eq:labelprofile`

Elementary bounds in `[0, ∞]` used to sum the terms of the bound of equation `eq:labelprofile`
for one block (`ofReal_abs_sub_value_le`):
* `eLpNorm_le_of_lintegral_le`: an `L^p` bound from a bound on the `p`-th moment;
* `eLpNorm_const_enn`: the norm of a constant on a probability space;
* `eLpNorm_ofReal_div_le`: dividing a nonnegative variable by `Q` (the moduli of equation
  `eq:modulus`);
* `lintegral_ofReal_div_sub_rpow_le`: the excess over `t` of `X/Q` for `X ≤ O_1(CQ)` has `q`-th
  moment at most `2(1 + ⌈2q⌉!) C^{2q} / t^q` (the profiles of equation `eq:profiles`);
* `eLpNorm_ofReal_div_sub_le`: the corresponding `L^p` bound `c_q^{1/q} C² / t`;
* `eLpNorm_indicator_const_le`: a constant on an event.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Labels

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- An `L^p` bound from a bound on the `p`-th moment. -/
theorem eLpNorm_le_of_lintegral_le {f : Ω → ℝ≥0∞} (hf : AEStronglyMeasurable f P)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {c : ℝ≥0∞}
    (h : ∫⁻ ω, f ω ^ p.toReal ∂P ≤ c ^ p.toReal) : eLpNorm f p P ≤ c := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf]
  simp only [enorm_eq_self]
  calc (∫⁻ ω, f ω ^ p.toReal ∂P) ^ (1 / p.toReal) ≤ (c ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = c := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- The `L^p` norm of a constant on a probability space. -/
theorem eLpNorm_const_enn [IsProbabilityMeasure P] (c : ℝ≥0∞) {p : ℝ≥0∞} (hp0 : p ≠ 0) :
    eLpNorm (fun _ : Ω => c) p P = c := by
  rw [eLpNorm_const c hp0 (IsProbabilityMeasure.ne_zero P), measure_univ, ENNReal.one_rpow,
    mul_one, enorm_eq_self]

/-- Dividing a nonnegative variable by `Q`. -/
theorem eLpNorm_ofReal_div_le {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) {Q η : ℝ} (hQ : 0 < Q)
    {p : ℝ≥0∞} (h : eLpNorm f p P ≤ ENNReal.ofReal (η * Q)) :
    eLpNorm (fun ω => ENNReal.ofReal (f ω / Q)) p P ≤ ENNReal.ofReal η := by
  have heq : (fun ω => ENNReal.ofReal (f ω / Q)) = ENNReal.ofReal ∘ (Q⁻¹ • f) := by
    funext ω
    simp [div_eq_inv_mul]
  rw [heq, eLpNorm_ofReal _ (Filter.Eventually.of_forall fun ω => by
      simpa using mul_nonneg (inv_nonneg.2 hQ.le) (hf0 ω)), eLpNorm_const_smul]
  calc ‖Q⁻¹‖ₑ * eLpNorm f p P ≤ ENNReal.ofReal Q⁻¹ * ENNReal.ofReal (η * Q) := by
        rw [Real.enorm_of_nonneg (inv_nonneg.2 hQ.le)]
        exact mul_le_mul_right h _
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hQ.le)]
        congr 1
        field_simp

/-- The constant `2(1 + ⌈2q⌉!)` of the `q`-th moment of the excess of an `O_1` variable. -/
noncomputable def momentConst (q : ℝ) : ℝ := 2 * (1 + ((Nat.ceil (2 * q)).factorial : ℝ))

theorem momentConst_pos (q : ℝ) : 0 < momentConst q := by
  unfold momentConst
  positivity

/-- **The excess of a normalized `O_1` variable.** For `X ≤ O_1(CQ)`, the excess of `X/Q` over
`t > 0` has `q`-th moment at most `2(1 + ⌈2q⌉!) C^{2q} / t^q`, since `(x − t)₊ ≤ x₊²/t`. -/
theorem lintegral_ofReal_div_sub_rpow_le [IsProbabilityMeasure P] {X : Ω → ℝ} {C Q t q : ℝ}
    (hX : Cited.IsOs P 1 (C * Q) X) (hC : 0 < C) (hQ : 0 < Q) (ht : 0 < t) (hq : 0 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal (X ω / Q - t) ^ q ∂P ≤
      ENNReal.ofReal (2 * (1 + ((Nat.ceil (2 * q)).factorial : ℝ)) * C ^ (2 * q) / t ^ q) := by
  have hCQ : 0 < C * Q := mul_pos hC hQ
  have hmom := Cited.IsOs.lintegral_pos_rpow_le (P := P) (s := 1) (θ := C * Q) (p := 2 * q)
    hX zero_lt_one hCQ (by positivity)
  simp only [div_one] at hmom
  -- the pointwise bound
  have hpt : ∀ ω, ENNReal.ofReal (X ω / Q - t) ^ q ≤
      ENNReal.ofReal (max (X ω) 0 ^ (2 * q)) * ENNReal.ofReal (1 / (Q ^ (2 * q) * t ^ q)) := by
    intro ω
    set y := max (X ω) 0 with hy
    have hy0 : 0 ≤ y := le_max_right _ _
    rcases le_or_gt (X ω / Q - t) 0 with hneg | hpos
    · rw [ENNReal.ofReal_of_nonpos hneg]
      rcases eq_or_lt_of_le hq with hq0 | hq0
      · rw [← hq0]; simp
      · rw [ENNReal.zero_rpow_of_pos hq0]; exact zero_le
    · have hXy : X ω ≤ y := le_max_left _ _
      have hyQ : t ≤ y / Q := by
        have : t < X ω / Q := by linarith
        exact this.le.trans (div_le_div_of_nonneg_right hXy hQ.le)
      have hbound : X ω / Q - t ≤ (y / Q) ^ 2 / t := by
        rw [le_div_iff₀ ht]
        have h1 : X ω / Q - t ≤ y / Q := by
          have := div_le_div_of_nonneg_right hXy hQ.le
          linarith
        nlinarith [div_nonneg hy0 hQ.le]
      calc ENNReal.ofReal (X ω / Q - t) ^ q ≤ ENNReal.ofReal ((y / Q) ^ 2 / t) ^ q :=
            ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hbound) hq
        _ = ENNReal.ofReal (((y / Q) ^ 2 / t) ^ q) :=
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hq
        _ = ENNReal.ofReal (y ^ (2 * q) * (1 / (Q ^ (2 * q) * t ^ q))) := by
            congr 1
            rw [div_pow, Real.div_rpow (by positivity) ht.le, Real.div_rpow (by positivity)
              (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
              ← Real.rpow_mul hy0, ← Real.rpow_mul hQ.le]
            push_cast
            field_simp
        _ = ENNReal.ofReal (y ^ (2 * q)) * ENNReal.ofReal (1 / (Q ^ (2 * q) * t ^ q)) :=
            ENNReal.ofReal_mul (by positivity)
  calc ∫⁻ ω, ENNReal.ofReal (X ω / Q - t) ^ q ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (max (X ω) 0 ^ (2 * q)) *
          ENNReal.ofReal (1 / (Q ^ (2 * q) * t ^ q)) ∂P := lintegral_mono hpt
    _ = (∫⁻ ω, ENNReal.ofReal (max (X ω) 0 ^ (2 * q)) ∂P) *
          ENNReal.ofReal (1 / (Q ^ (2 * q) * t ^ q)) := lintegral_mul_const' _ _ (by simp)
    _ ≤ ENNReal.ofReal (2 * (1 + ((Nat.ceil (2 * q)).factorial : ℝ)) * (C * Q) ^ (2 * q)) *
          ENNReal.ofReal (1 / (Q ^ (2 * q) * t ^ q)) := mul_le_mul_left hmom _
    _ = ENNReal.ofReal (2 * (1 + ((Nat.ceil (2 * q)).factorial : ℝ)) * C ^ (2 * q) / t ^ q) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.mul_rpow hC.le hQ.le]
        field_simp

/-- The `L^p` form of `lintegral_ofReal_div_sub_rpow_le`. -/
theorem eLpNorm_ofReal_div_sub_le [IsProbabilityMeasure P] {X : Ω → ℝ} {C Q t : ℝ}
    (hX : Cited.IsOs P 1 (C * Q) X) (hC : 0 < C) (hQ : 0 < Q) (ht : 0 < t) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm (fun ω => ENNReal.ofReal (X ω / Q - t)) p P ≤
      ENNReal.ofReal (momentConst p.toReal ^ (1 / p.toReal) * C ^ 2 / t) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hc := momentConst_pos p.toReal
  refine eLpNorm_le_of_lintegral_le
    ((hX.1.div_const Q).sub_const t).ennreal_ofReal.aestronglyMeasurable hp0 hpt ?_
  refine (lintegral_ofReal_div_sub_rpow_le hX hC hQ ht hq.le).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le]
  congr 1
  rw [Real.div_rpow (by positivity) ht.le, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hc.le, one_div_mul_cancel hq.ne', Real.rpow_one, ← Real.rpow_natCast,
    ← Real.rpow_mul hC.le]
  unfold momentConst
  push_cast
  ring_nf

/-- A constant on an event. -/
theorem eLpNorm_indicator_const_le {B : Set Ω} (hB : MeasurableSet B) (c : ℝ≥0∞) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {ε : ℝ≥0∞} (hε : P B ≤ ε) :
    eLpNorm (B.indicator fun _ => c) p P ≤ c * ε ^ (1 / p.toReal) := by
  rw [eLpNorm_indicator_const hB.nullMeasurableSet hp0 hpt, enorm_eq_self]
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  exact mul_le_mul_right (ENNReal.rpow_le_rpow hε (by positivity)) _

end IsotropicVariance.Paper.Proofs.Labels
