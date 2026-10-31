/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Poisson.Splitting
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Recognizing independent Poisson counts from their generating function

Complex probability generating functions determine finite joint natural count laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Complex
open scoped NNReal ENNReal BigOperators

namespace IsotropicVariance.Infra.Poisson

/-- A factorized Poisson generating function determines the joint real count law. -/
theorem map_real_counts_of_generating {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ} (N : Fin k → Ω → ℕ)
    (hmN : ∀ i, Measurable (N i)) (rates : Fin k → ℝ≥0)
    (hgen : ∀ z : Fin k → ℂ, (∀ i, ‖z i‖ ≤ 1) →
      (∫ w, ∏ i, z i ^ N i w ∂P) = ∏ i, Complex.exp ((rates i : ℂ) * (z i - 1))) :
    P.map (fun w => fun i => (N i w : ℝ)) =
      Measure.pi (fun i => (poissonMeasure (rates i)).map (Nat.cast : ℕ → ℝ)) := by
  have hm : Measurable (fun w : Ω => fun i => (N i w : ℝ)) :=
    Measurable.of_eval fun i => Measurable.of_discrete.comp (hmN i)
  apply charFun_eq_pi_iff.mp
  intro t
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop),
    integral_map hm.aemeasurable (by fun_prop)]
  simp only [PiLp.inner_apply, Real.inner_apply,
    Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  have heq (w : Ω) (i : Fin k) :
      Complex.exp (((N i w : ℝ) : ℂ) * ((t i : ℝ) : ℂ) * I) =
        Complex.exp (((t i : ℝ) : ℂ) * I) ^ N i w := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [Complex.ofReal_mul, heq]
  rw [hgen _ (by intro i; simp [Complex.norm_exp])]
  apply Finset.prod_congr rfl
  intro i _
  rw [charFun_map_cast_poissonMeasure]

/-- A factorized Poisson generating function determines the joint natural count law. -/
theorem hasLaw_counts_of_generating {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ} (N : Fin k → Ω → ℕ)
    (hmN : ∀ i, Measurable (N i)) (rates : Fin k → ℝ≥0)
    (hgen : ∀ z : Fin k → ℂ, (∀ i, ‖z i‖ ≤ 1) →
      (∫ w, ∏ i, z i ^ N i w ∂P) = ∏ i, Complex.exp ((rates i : ℂ) * (z i - 1))) :
    HasLaw (fun w => fun i => N i w) (Measure.pi (fun i => poissonMeasure (rates i))) P := by
  have hm : Measurable (fun w : Ω => fun i => N i w) :=
    Measurable.of_eval fun i => hmN i
  have hc : Measurable (fun n : Fin k → ℕ => fun i => (n i : ℝ)) :=
    Measurable.of_eval fun i => Measurable.of_discrete.comp (measurable_pi_apply i)
  have hi : Function.Injective (fun n : Fin k → ℕ => fun i => (n i : ℝ)) := by
    intro n m hnm
    funext i
    exact Nat.cast_injective (congrFun hnm i)
  refine ⟨hm.aemeasurable, ?_⟩
  apply (hc.measurableEmbedding hi).map_injective
  rw [Measure.map_map hc hm, Measure.pi_map_pi (fun _ => Measurable.of_discrete.aemeasurable)]
  exact map_real_counts_of_generating P N hmN rates hgen

/-- A product joint natural law implies independence of its coordinates. -/
theorem iIndepFun_of_hasLaw_pi_nat {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ} (N : Fin k → Ω → ℕ)
    (hmN : ∀ i, Measurable (N i)) (rates : Fin k → ℝ≥0)
    (hlaw : HasLaw (fun w => fun i => N i w) (Measure.pi (fun i => poissonMeasure (rates i))) P) :
    iIndepFun N P := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hmN i).aemeasurable)).mpr
  have hsingle (i : Fin k) : P.map (N i) = poissonMeasure (rates i) := by
    have hh := (measurePreserving_eval (fun i => poissonMeasure (rates i)) i).hasLaw.comp hlaw
    simpa only [Function.comp_def, Function.eval] using hh.map_eq
  simp_rw [hsingle]
  exact hlaw.map_eq

end IsotropicVariance.Infra.Poisson
