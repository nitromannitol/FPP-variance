/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Interpolation for the centered profiles in Lemma `lem:smallmean`

Interpolate between orders two and `8d` at order `4d`, retaining an explicit
positive tolerance.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace CurvatureVariance.Paper.Mean

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- Hölder interpolation between two positive finite moment orders. -/
theorem eLpNorm_interpolation {p q r θ : ℝ}
    (hX : AEStronglyMeasurable X μ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hθ : 0 < θ) (hθ₁ : θ < 1)
    (heq : 1 / q = θ / p + (1 - θ) / r) :
    eLpNorm X (ENNReal.ofReal q) μ ≤
      eLpNorm X (ENNReal.ofReal p) μ ^ θ *
        eLpNorm X (ENNReal.ofReal r) μ ^ (1 - θ) := by
  have hθ' : 0 < 1 - θ := sub_pos.mpr hθ₁
  have hqp : q < p / θ := by
    have hpos : 0 < (1 - θ) / r := div_pos hθ' hr
    have hlt : θ / p < 1 / q := by linarith
    apply (lt_div_iff₀ hθ).2
    have := (div_lt_div_iff₀ hp hq).1 hlt
    nlinarith
  have hsum : 1 / q = 1 / (p / θ) + 1 / (r / (1 - θ)) := by
    simpa only [one_div_div] using heq
  have hA : AEStronglyMeasurable (fun x => ‖X x‖ ^ θ) μ := (hX.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  have hB : AEStronglyMeasurable (fun x => ‖X x‖ ^ (1 - θ)) μ :=
    (hX.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  have h := eLpNorm'_le_eLpNorm'_mul_eLpNorm' hA hB (fun a b : ℝ => a * b) 1
    (by filter_upwards with x; simp) hq hqp hsum
  have hprod : (fun x => ‖X x‖ ^ θ * ‖X x‖ ^ (1 - θ)) = fun x => ‖X x‖ := by
    funext x
    rw [← Real.rpow_add' (norm_nonneg _) (by linarith : θ + (1 - θ) ≠ 0)]
    simp
  rw [hprod, eLpNorm'_norm_rpow X (p / θ) θ hθ,
    eLpNorm'_norm_rpow X (r / (1 - θ)) (1 - θ) hθ'] at h
  simp only [div_mul_cancel₀ _ hθ.ne', div_mul_cancel₀ _ hθ'.ne',
    ENNReal.coe_one, one_mul] at h
  simpa only [eLpNorm_eq_eLpNorm' (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
      ENNReal.ofReal_ne_top hX,
    eLpNorm_eq_eLpNorm' (ne_of_gt (ENNReal.ofReal_pos.mpr hq))
      ENNReal.ofReal_ne_top hX,
    eLpNorm_eq_eLpNorm' (ne_of_gt (ENNReal.ofReal_pos.mpr hr))
      ENNReal.ofReal_ne_top hX,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le,
    ENNReal.toReal_ofReal hr.le, eLpNorm'_norm] using h


/-- The interpolation weight `θ = 2/(r-2)` on order two, `r = (8 * (m + 1))`. -/
noncomputable def interpTheta (m : ℕ) : ℝ := 2 / (((8 * (m + 1)) : ℝ) - 2)

/-- The `L²` tolerance `δ₂ = (σ' / B_r^{1-θ})^{1/θ}` that interpolation turns into `σ'`. -/
noncomputable def interpDelta (m : ℕ) (Br σ' : ℝ) : ℝ :=
  (σ' / Br ^ (1 - interpTheta m)) ^ (1 / interpTheta m)

theorem meanMoment_ge (m : ℕ) : (8 : ℝ) ≤ ((8 * (m + 1) : ℕ) : ℝ) := by
  push_cast
  linarith only [Nat.cast_nonneg (α := ℝ) m]

lemma interpTheta_pos (m : ℕ) : 0 < interpTheta m := by
  have := meanMoment_ge m
  unfold interpTheta
  apply div_pos <;> linarith

lemma interpTheta_lt_one (m : ℕ) : interpTheta m < 1 := by
  have := meanMoment_ge m
  unfold interpTheta
  rw [div_lt_one (by linarith)]
  linarith

theorem interpDelta_pos (m : ℕ) {Br σ' : ℝ} (hBr : 0 < Br) (hσ : 0 < σ') :
    0 < interpDelta m Br σ' := by
  unfold interpDelta
  exact Real.rpow_pos_of_pos (div_pos hσ (Real.rpow_pos_of_pos hBr _)) _

/-- Interpolation between orders `2` and `r` at order `k_* = r/2`. -/
theorem eLpNorm_meanMoment_le_of_two_of_double {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m : ℕ} {S : Ω → ℝ} (hS : AEStronglyMeasurable S P)
    {Q Br σ' : ℝ} (hQ : 0 < Q) (hBr : 0 < Br) (hσ : 0 < σ')
    (h2 : eLpNorm S 2 P ≤ ENNReal.ofReal (interpDelta m Br σ' * Q))
    (hr : eLpNorm S ((8 * (m + 1) : ℕ) : ℝ≥0∞) P ≤ ENNReal.ofReal (Br * Q)) :
    eLpNorm S ((4 * (m + 1) : ℕ) : ℝ≥0∞) P ≤ ENNReal.ofReal (σ' * Q) := by
  have hr8 := meanMoment_ge m
  have hθ := interpTheta_pos m
  have hθ1 := interpTheta_lt_one m
  set θ := interpTheta m with hθdef
  set r : ℝ := ((8 * (m + 1)) : ℝ) with hrdef
  have hδ := interpDelta_pos m hBr hσ
  have hheq : 1 / (r / 2) = θ / 2 + (1 - θ) / r := by
    have hθ' : θ = 2 / (r - 2) := rfl
    rw [hθ']
    have : r - 2 ≠ 0 := by linarith
    have : r ≠ 0 := by linarith
    field_simp
    ring
  have key := eLpNorm_interpolation (μ := P) (p := 2) (q := r / 2) (r := r) (θ := θ) hS
    (by norm_num) (by linarith) (by linarith) hθ hθ1 hheq
  have e1 : (((4 * (m + 1)) : ℕ) : ℝ≥0∞) = ENNReal.ofReal (r / 2) := by
    rw [show r / 2 = ((4 * (m + 1) : ℕ) : ℝ) by dsimp only [r]; push_cast; ring,
      ENNReal.ofReal_natCast]
  have e2 : (((8 * (m + 1)) : ℕ) : ℝ≥0∞) = ENNReal.ofReal r := by
    rw [show r = ((8 * (m + 1) : ℕ) : ℝ) by dsimp only [r]; push_cast; ring,
      ENNReal.ofReal_natCast]
  have e3 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [e1]
  rw [e3] at h2
  rw [e2] at hr
  refine key.trans ?_
  have hA := ENNReal.rpow_le_rpow h2 hθ.le
  have hB := ENNReal.rpow_le_rpow hr (sub_nonneg.mpr hθ1.le)
  refine (mul_le_mul' hA hB).trans ?_
  have hδQ : 0 ≤ interpDelta m Br σ' * Q := by positivity
  have hBQ : 0 ≤ Br * Q := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hδQ hθ.le,
    ENNReal.ofReal_rpow_of_nonneg hBQ (sub_nonneg.mpr hθ1.le),
    ← ENNReal.ofReal_mul (by positivity)]
  apply le_of_eq
  congr 1
  have hd : interpDelta m Br σ' ^ θ = σ' / Br ^ (1 - θ) := by
    unfold interpDelta
    rw [← Real.rpow_mul (div_pos hσ (Real.rpow_pos_of_pos hBr _)).le]
    rw [← hθdef]
    have : 1 / θ * θ = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [Real.mul_rpow hδ.le hQ.le, Real.mul_rpow hBr.le hQ.le, hd]
  have hQQ : Q ^ θ * Q ^ (1 - θ) = Q := by
    rw [← Real.rpow_add hQ]; simp
  have hBp : Br ^ (1 - θ) ≠ 0 := (Real.rpow_pos_of_pos hBr _).ne'
  calc σ' / Br ^ (1 - θ) * Q ^ θ * (Br ^ (1 - θ) * Q ^ (1 - θ))
      = σ' * (Q ^ θ * Q ^ (1 - θ)) := by field_simp
    _ = σ' * Q := by rw [hQQ]


end CurvatureVariance.Paper.Mean
