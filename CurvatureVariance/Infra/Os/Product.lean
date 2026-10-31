/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Os.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Products of stochastic bounds

AKM Lemma A.3(ii), p. 456, with constant one and no independence.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
namespace CurvatureVariance.Infra.Os

/-- The weighted Young and exponential-convexity estimate behind AKM A.3(ii). -/
theorem exp_mul_rpow_le {x y s t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : 0 < s) (ht : 0 < t) :
    Real.exp ((x * y) ^ (s * t / (s + t))) ≤
      (t / (s + t)) * Real.exp (x ^ s) + (s / (s + t)) * Real.exp (y ^ t) := by
  have hsum : 0 < s + t := add_pos hs ht
  have hw : t / (s + t) + s / (s + t) = 1 := by field_simp; ring
  have hYoung := Real.geom_mean_le_arith_mean2_weighted
    (div_nonneg ht.le hsum.le) (div_nonneg hs.le hsum.le)
    (Real.rpow_nonneg hx s) (Real.rpow_nonneg hy t) hw
  have heq : (x * y) ^ (s * t / (s + t)) =
      (x ^ s) ^ (t / (s + t)) * (y ^ t) ^ (s / (s + t)) := by
    rw [Real.mul_rpow hx hy, ← Real.rpow_mul hx, ← Real.rpow_mul hy]
    congr 2 <;> ring
  rw [heq]
  exact (Real.exp_le_exp.mpr hYoung).trans
    (convexOn_exp.2 (mem_univ _) (mem_univ _)
      (div_nonneg ht.le hsum.le) (div_nonneg hs.le hsum.le) hw)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- AKM A.3(ii): products of nonnegative `O_s` variables have harmonic exponent,
with exactly the product of their scales. No independence is assumed. -/
theorem isOs_mul_nonneg {s t θ η : ℝ} {X Y : Ω → ℝ}
    (hX : IsOs P s θ X) (hY : IsOs P t η Y)
    (hs : 0 < s) (ht : 0 < t) (hθ : 0 < θ) (hη : 0 < η)
    (hX0 : 0 ≤ᵐ[P] X) (hY0 : 0 ≤ᵐ[P] Y) :
    IsOs P (s * t / (s + t)) (θ * η) (fun ω => X ω * Y ω) := by
  let a := t / (s + t)
  let b := s / (s + t)
  have ha : 0 ≤ a := div_nonneg ht.le (add_pos hs ht).le
  have hb : 0 ≤ b := div_nonneg hs.le (add_pos hs ht).le
  have hab : a + b = 1 := by dsimp only [a, b]; field_simp; ring
  refine ⟨hX.1.mul hY.1, ?_⟩
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (a * Real.exp ((max (X ω) 0 / θ) ^ s) +
        b * Real.exp ((max (Y ω) 0 / η) ^ t)) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hX0, hY0] with ω hx hy
      change (0 : ℝ) ≤ X ω at hx
      change (0 : ℝ) ≤ Y ω at hy
      apply ENNReal.ofReal_le_ofReal
      rw [max_eq_left hx, max_eq_left hy, max_eq_left (mul_nonneg hx hy)]
      rw [← div_mul_div_comm]
      exact exp_mul_rpow_le (div_nonneg hx hθ.le) (div_nonneg hy hη.le) hs ht
    _ = ENNReal.ofReal a * (∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s)) ∂P) +
        ENNReal.ofReal b * (∫⁻ ω, ENNReal.ofReal (Real.exp ((max (Y ω) 0 / η) ^ t)) ∂P) := by
      simp_rw [ENNReal.ofReal_add (mul_nonneg ha (Real.exp_pos _).le) (mul_nonneg hb (Real.exp_pos _).le),
        ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
      rw [lintegral_add_left' ((aemeasurable_exp_pos_rpow hX.1 s θ).const_mul _),
        lintegral_const_mul'' _ (aemeasurable_exp_pos_rpow hX.1 s θ),
        lintegral_const_mul'' _ (aemeasurable_exp_pos_rpow hY.1 t η)]
    _ ≤ ENNReal.ofReal a * 2 + ENNReal.ofReal b * 2 :=
      add_le_add (mul_le_mul le_rfl hX.2 zero_le zero_le) (mul_le_mul le_rfl hY.2 zero_le zero_le)
    _ = 2 := by rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul]

end CurvatureVariance.Infra.Os
