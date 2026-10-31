/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring

/-!
# Polynomial moments of `O_s` variables

Explicit (nonoptimal) constants for the positive-part moments. These follow directly from
AKM (A.2), without any independence.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
namespace IsotropicVariance.Infra.Os

open Cited

/-- A polynomial is dominated by an exponential, with a factorial constant. -/
theorem rpow_le_factorial_mul_exp {x q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q)
    (n : ℕ) (hn : q ≤ n) :
    x ^ q ≤ (1 + (n.factorial : ℝ)) * Real.exp x := by
  have hexp : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hfac : 0 ≤ (n.factorial : ℝ) := Nat.cast_nonneg _
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx hx1 hq).trans
      (le_trans hexp (le_mul_of_one_le_left (Real.exp_pos x).le (le_add_of_nonneg_right hfac)))
  · have hpow := (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mp (Real.pow_div_factorial_le_exp x hx n)
    have hr : x ^ q ≤ x ^ n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hn
    exact hr.trans (hpow.trans (by rw [add_mul, one_mul, mul_comm (n.factorial : ℝ)]; exact le_add_of_nonneg_left (Real.exp_pos _).le))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Every positive-part moment of an `O_s(θ)` variable is bounded by
`2 (1 + ceil(p/s)!) θ^p`. In particular, the constant depends only on `s,p`. -/
theorem _root_.IsotropicVariance.Cited.IsOs.lintegral_pos_rpow_le {s θ p : ℝ} {X : Ω → ℝ}
    (hX : IsOs P s θ X) (hs : 0 < s) (hθ : 0 < θ) (hp : 0 ≤ p) :
    (∫⁻ ω, ENNReal.ofReal (max (X ω) 0 ^ p) ∂P) ≤
      ENNReal.ofReal (2 * (1 + ((Nat.ceil (p / s)).factorial : ℝ)) * θ ^ p) := by
  let n := Nat.ceil (p / s)
  let B : ℝ := (1 + (n.factorial : ℝ)) * θ ^ p
  have hB : 0 ≤ B := mul_nonneg (by positivity) (Real.rpow_nonneg hθ.le _)
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal B * ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s)) ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [← ENNReal.ofReal_mul hB]
      apply ENNReal.ofReal_le_ofReal
      have hNorm : ((max (X ω) 0 / θ) ^ s) ^ (p / s) = (max (X ω) 0 / θ) ^ p := by
        rw [← Real.rpow_mul (by positivity), show s * (p / s) = p by field_simp]
      have hh := rpow_le_factorial_mul_exp (Real.rpow_nonneg (show 0 ≤ max (X ω) 0 / θ from div_nonneg (le_max_right _ _) hθ.le) s)
        (div_nonneg hp hs.le) n (Nat.le_ceil _)
      rw [hNorm, Real.div_rpow (le_max_right _ _) hθ.le] at hh
      have hh' := (div_le_iff₀ (Real.rpow_pos_of_pos hθ p)).mp hh
      exact hh'.trans_eq (by dsimp only [B]; ring)
    _ = ENNReal.ofReal B * (∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s)) ∂P) :=
      lintegral_const_mul'' _ (aemeasurable_exp_pos_rpow hX.1 s θ)
    _ ≤ ENNReal.ofReal B * 2 := mul_le_mul le_rfl hX.2 zero_le zero_le
    _ = _ := by rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul hB]; congr 1; dsimp only [B, n]; ring


/-- Every nonnegative positive-part power is integrable. -/
theorem _root_.IsotropicVariance.Cited.IsOs.integrable_pos_rpow {s θ p : ℝ} {X : Ω → ℝ}
    (hX : IsOs P s θ X) (hs : 0 < s) (hθ : 0 < θ) (hp : 0 ≤ p) :
    Integrable (fun ω => max (X ω) 0 ^ p) P := by
  refine ⟨((hX.1.max aemeasurable_const).pow_const p).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (le_max_right (X ω) 0) p)).mpr ?_⟩
  exact (hX.lintegral_pos_rpow_le hs hθ hp).trans_lt ENNReal.ofReal_lt_top

/-- The usual real-valued expectation form of the positive-part moment bound. -/
theorem _root_.IsotropicVariance.Cited.IsOs.integral_pos_rpow_le {s θ p : ℝ} {X : Ω → ℝ}
    (hX : IsOs P s θ X) (hs : 0 < s) (hθ : 0 < θ) (hp : 0 ≤ p) :
    (∫ ω, max (X ω) 0 ^ p ∂P) ≤
      2 * (1 + ((Nat.ceil (p / s)).factorial : ℝ)) * θ ^ p := by
  have hh := hX.lintegral_pos_rpow_le hs hθ hp
  rw [← ofReal_integral_eq_lintegral_ofReal (hX.integrable_pos_rpow hs hθ hp)
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (le_max_right (X ω) 0) p)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

/-- A nonnegative `O_s` variable is integrable. -/
theorem _root_.IsotropicVariance.Cited.IsOs.integrable {s θ : ℝ} {X : Ω → ℝ} (hX : IsOs P s θ X)
    (hs : 0 < s) (hθ : 0 < θ) (hX0 : 0 ≤ᵐ[P] X) : Integrable X P := by
  refine ⟨hX.1.aestronglyMeasurable, ?_⟩
  have hb := hX.lintegral_pos_rpow_le hs hθ (show (0 : ℝ) ≤ 1 by norm_num)
  have heq : (fun ω => ENNReal.ofReal ‖X ω‖) =ᵐ[P] (fun ω => ENNReal.ofReal (max (X ω) 0 ^ (1 : ℝ))) := by
    filter_upwards [hX0] with ω hω
    change (0 : ℝ) ≤ X ω at hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω, max_eq_left hω, Real.rpow_one]
  rw [hasFiniteIntegral_iff_norm]
  exact ((lintegral_congr_ae heq).trans_le hb).trans_lt ENNReal.ofReal_lt_top

end IsotropicVariance.Infra.Os
