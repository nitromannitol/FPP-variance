/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Concentration.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The symmetrized entropy step in BLM Proposition 10

The coordinate Bregman-entropy symmetrization. The coordinates and their laws are arbitrary,
and the bound is in terms of the positive refresh differences.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
namespace IsotropicVariance.Infra.Concentration
open IsotropicVariance.Infra.Entropy

/-- Bregman symmetrization of two exponential values. -/
theorem entropyDensity_exp_pair (a b : ℝ) :
    entropyDensity (exp b) (exp a) + entropyDensity (exp a) (exp b) = (a - b) * (exp a - exp b) := by
  simp only [entropyDensity, Real.log_exp]
  ring

/-- The one-dimensional positive-difference estimate used in the entropy step. -/
theorem entropyDensity_exp_pair_le {a b θ C : ℝ} (hab : b ≤ a)
    (hψ : (-θ * (a - b)) * (exp (-θ * (a - b)) - 1) ≤ C * (a - b) ^ 2) :
    entropyDensity (exp (θ * b)) (exp (θ * a)) + entropyDensity (exp (θ * a)) (exp (θ * b)) ≤
      C * exp (θ * a) * max (a - b) 0 ^ 2 + C * exp (θ * b) * max (b - a) 0 ^ 2 := by
  rw [max_eq_left (sub_nonneg.mpr hab), max_eq_right (sub_nonpos.mpr hab)]
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, entropyDensity_exp_pair]
  have hExp : exp (θ * b) = exp (θ * a) * exp (-θ * (a - b)) := by
    rw [← exp_add]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_left hψ (exp_pos (θ * a)).le
  rw [hExp]
  nlinarith only [hh]

/-- Averaging the coordinate Bregman inequality and symmetrizing its reference
point gives the positive-difference entropy bound. -/
theorem eentropy_exp_le_positive_proxy {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsProbabilityMeasure ν] (f : A → ℝ) (hf : Measurable f) (θ C : ℝ) (hC : 0 ≤ C)
    (hInt : Integrable (fun a => exp (θ * f a)) ν)
    (hψ : ∀ a b, f b ≤ f a →
      (-θ * (f a - f b)) * (exp (-θ * (f a - f b)) - 1) ≤ C * (f a - f b) ^ 2) :
    eentropy ν (fun a => exp (θ * f a)) ≤
      ENNReal.ofReal C * ∫⁻ a, ENNReal.ofReal (exp (θ * f a)) *
        ∫⁻ b, ENNReal.ofReal (max (f a - f b) 0 ^ 2) ∂ν ∂ν := by
  let S := fun a b => ENNReal.ofReal (entropyDensity (exp (θ * f b)) (exp (θ * f a)))
  let G := fun a b => ENNReal.ofReal (C * exp (θ * f a) * max (f a - f b) 0 ^ 2)
  have hS : Measurable (Function.uncurry S) := ENNReal.measurable_ofReal.comp
    (measurable_entropyDensity.comp (((hf.comp measurable_snd).const_mul θ).exp.prodMk
      ((hf.comp measurable_fst).const_mul θ).exp))
  have hG : Measurable (Function.uncurry G) := by
    dsimp only [G, Function.uncurry_def]
    fun_prop
  have h1 : eentropy ν (fun a => exp (θ * f a)) ≤ ∫⁻ a, ∫⁻ b, S a b ∂ν ∂ν := by
    have hOne (b : A) : eentropy ν (fun a => exp (θ * f a)) ≤ ∫⁻ a, S a b ∂ν := by
      rw [lintegral_entropyDensity_eq (exp_pos _) (fun a => (exp_pos _).le) hInt]
      exact le_self_add
    calc
      _ = ∫⁻ b, eentropy ν (fun a => exp (θ * f a)) ∂ν := by rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ b, ∫⁻ a, S a b ∂ν ∂ν := lintegral_mono hOne
      _ = _ := lintegral_lintegral_swap (hS.comp measurable_swap).aemeasurable
  have hSG (a b : A) : S a b + S b a ≤ G a b + G b a := by
    dsimp only [S, G]
    rw [← ENNReal.ofReal_add (entropyDensity_nonneg (exp_pos _) (exp_pos _).le)
      (entropyDensity_nonneg (exp_pos _) (exp_pos _).le),
      ← ENNReal.ofReal_add (by positivity : 0 ≤ C * exp (θ * f a) * max (f a - f b) 0 ^ 2)
        (by positivity : 0 ≤ C * exp (θ * f b) * max (f b - f a) 0 ^ 2)]
    apply ENNReal.ofReal_le_ofReal
    rcases le_total (f b) (f a) with hab | hab
    · exact entropyDensity_exp_pair_le hab (hψ a b hab)
    · simpa only [add_comm] using entropyDensity_exp_pair_le hab (hψ b a hab)
  have hSym {H : A → A → ℝ≥0∞} (hH : Measurable (Function.uncurry H)) :
      2 * (∫⁻ a, ∫⁻ b, H a b ∂ν ∂ν) = ∫⁻ a, ∫⁻ b, H a b + H b a ∂ν ∂ν := by
    have hSwap : (∫⁻ a, ∫⁻ b, H b a ∂ν ∂ν) = ∫⁻ a, ∫⁻ b, H a b ∂ν ∂ν :=
      lintegral_lintegral_swap (hH.comp measurable_swap).aemeasurable
    have hm1 : ∀ a, Measurable fun b => H a b := fun _ => hH.comp measurable_prodMk_left
    have hi1 : Measurable fun a => ∫⁻ b, H a b ∂ν := hH.lintegral_prod_right'
    simp_rw [lintegral_add_left (hm1 _)]
    rw [lintegral_add_left hi1, hSwap, two_mul]
  have h2 : (∫⁻ a, ∫⁻ b, S a b ∂ν ∂ν) ≤ ∫⁻ a, ∫⁻ b, G a b ∂ν ∂ν := by
    apply (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).mp
    rw [hSym hS, hSym hG]
    exact lintegral_mono fun a => lintegral_mono fun b => hSG a b
  apply h1.trans (h2.trans_eq _)
  simp_rw [G, ENNReal.ofReal_mul (mul_nonneg hC (exp_pos _).le), ENNReal.ofReal_mul hC]
  simp_rw [mul_assoc]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end IsotropicVariance.Infra.Concentration
