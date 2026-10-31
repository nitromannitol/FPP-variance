/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Poisson.Cloud
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Thinning a finite Poisson cloud

The probability generating function of the number of retained marks in a Borel set.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Complex
open scoped NNReal ENNReal BigOperators

namespace IsotropicVariance.Infra.Poisson

/-- Natural-valued cloud counts are measurable. -/
theorem measurable_cloudCount {X : Type*} [MeasurableSpace X] {B : Set X}
    (hB : MeasurableSet B) : Measurable (cloudCount B : CloudSample X → ℕ) := by
  classical
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun xs : ℕ → X => ∑ i : Fin n, if xs i ∈ B then 1 else 0)
  exact Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
    Measurable.ite (hB.preimage (measurable_pi_apply (i : ℕ))) measurable_const measurable_const

/-- A product of mark weights is the generating monomial of the number in a set. -/
theorem cloudCount_pow {X : Type*} (B : Set X) [DecidablePred (· ∈ B)] (w : CloudSample X) (z : ℂ) :
    z ^ cloudCount B w = ∏ i : Fin w.1, if w.2 i ∈ B then z else 1 := by
  classical
  rw [cloudCount, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

/-- Integrating the one-mark weight gives the Bernoulli generating polynomial. -/
theorem integral_markWeight {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {B : Set X} (hB : MeasurableSet B) [DecidablePred (· ∈ B)] (z : ℂ) :
    (∫ x, if x ∈ B then z else 1 ∂ν) = 1 + (ν.real B : ℂ) * (z - 1) := by
  classical
  have heq : (fun x => if x ∈ B then z else (1 : ℂ)) =
      (fun _ => (1 : ℂ)) + B.indicator (fun _ => z - 1) := by
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [heq, integral_add' (integrable_const _) ((integrable_const _).indicator hB),
    integral_const, integral_indicator_const _ hB]
  simp [Complex.real_smul]

/-- The probability generating function after retaining the marks in a Borel set. -/
theorem integral_pow_cloudCount {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (r : ℝ≥0) {B : Set X} (hB : MeasurableSet B)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∫ w, z ^ cloudCount B w ∂cloudLaw r ν) =
      Complex.exp ((r : ℂ) * ν.real B * (z - 1)) := by
  classical
  simp_rw [cloudCount_pow]
  rw [integral_cloud_prod ν r (h := fun x => if x ∈ B then z else 1)
    (Measurable.ite hB measurable_const measurable_const)
    (by intro x; split_ifs; exact hz; simp), integral_markWeight ν hB]
  congr 1
  ring

/-- Thinning a finite Poisson cloud gives the literal natural Poisson count law. -/
theorem hasLaw_cloudCount {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (r : ℝ≥0) {B : Set X} (hB : MeasurableSet B) :
    HasLaw (cloudCount B) (poissonMeasure (r * (ν B).toNNReal)) (cloudLaw r ν) := by
  have hm := measurable_cloudCount hB
  have hc : Measurable (Nat.cast : ℕ → ℝ) := .of_discrete
  refine ⟨hm.aemeasurable, ?_⟩
  apply (hc.measurableEmbedding Nat.cast_injective).map_injective
  rw [Measure.map_map hc hm]
  have hmR : Measurable (fun w : CloudSample X => (cloudCount B w : ℝ)) := hc.comp hm
  have : IsProbabilityMeasure ((cloudLaw r ν).map (fun w => (cloudCount B w : ℝ))) :=
    by infer_instance
  apply Measure.ext_of_charFun
  funext t
  change charFun ((cloudLaw r ν).map (fun w => (cloudCount B w : ℝ))) t = _
  rw [charFun_apply_real, integral_map hmR.aemeasurable (by fun_prop), charFun_map_cast_poissonMeasure]
  have heq (w : CloudSample X) :
      Complex.exp ((t : ℂ) * ((cloudCount B w : ℝ) : ℂ) * I) =
        Complex.exp ((t : ℂ) * I) ^ cloudCount B w := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [heq]
  rw [integral_pow_cloudCount ν r hB _ (by simp [Complex.norm_exp])]
  congr 1
  simp only [NNReal.coe_mul, Complex.ofReal_mul, ENNReal.toReal,
    measureReal_def]

end IsotropicVariance.Infra.Poisson
