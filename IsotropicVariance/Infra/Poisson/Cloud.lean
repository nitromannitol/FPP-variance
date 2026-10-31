/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Poisson.Operations
public import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Finite Poisson clouds

Sample a Poisson count independently of an infinite iid sequence of marks and retain the
first N marks. The cloud is the finite sum of their Dirac measures, with all-outcome counting
and Giry measurability. Its generating functional is computed from the exponential series.
These are construction ingredients, not an assumed point-process existence statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Complex
open scoped NNReal ENNReal BigOperators Nat

namespace IsotropicVariance.Infra.Poisson

/-- A finite count together with an infinite sequence of possible marks. -/
abbrev CloudSample (X : Type*) := ℕ × (ℕ → X)

/-- Retain the first N marks, including multiplicities. -/
noncomputable def cloud {X : Type*} [MeasurableSpace X] (w : CloudSample X) : Measure X :=
  ∑ i : Fin w.1, Measure.dirac (w.2 i)

/-- The natural-valued number of retained marks in a set. -/
noncomputable def cloudCount {X : Type*} (B : Set X) (w : CloudSample X) : ℕ := by
  classical
  exact ∑ i : Fin w.1, if w.2 i ∈ B then 1 else 0

/-- The count is literally the evaluation of the sum of Diracs. -/
theorem cloud_apply {X : Type*} [MeasurableSpace X] {B : Set X} (hB : MeasurableSet B)
    (w : CloudSample X) : cloud w B = (cloudCount B w : ℝ≥0∞) := by
  classical
  simp only [cloud, Measure.finsetSum_apply, Measure.dirac_apply' _ hB, cloudCount, Nat.cast_sum]
  congr 1
  funext i
  split_ifs with hi <;> simp [hi]

/-- The finite cloud is measurable as a random measure. -/
theorem measurable_cloud {X : Type*} [MeasurableSpace X] :
    Measurable (cloud : CloudSample X → Measure X) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun x : ℕ → X => ∑ i : Fin n, Measure.dirac (x i))
  exact Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
    Measure.measurable_dirac.comp (measurable_pi_apply (i : ℕ))

/-- Independent Poisson count and iid marks. -/
noncomputable def cloudLaw {X : Type*} [MeasurableSpace X] (r : ℝ≥0) (ν : Measure X) :
    Measure (CloudSample X) := (poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => ν))

instance cloudLaw.isProbabilityMeasure {X : Type*} [MeasurableSpace X] (r : ℝ≥0)
    (ν : Measure X) [IsProbabilityMeasure ν] : IsProbabilityMeasure (cloudLaw r ν) := by
  unfold cloudLaw
  infer_instance

/-- Poisson probability generating function, valid also for complex arguments. -/
theorem integral_pow_poisson (r : ℝ≥0) (z : ℂ) :
    ∫ n : ℕ, z ^ n ∂poissonMeasure r = Complex.exp (r * (z - 1)) := by
  rw [integral_poissonMeasure r]
  simp only [Complex.real_smul]
  calc ∑' n, (Real.exp (-r) * (r : ℝ) ^ n / (Nat.factorial n) : ℝ) * z ^ n
      = ∑' n, (Real.exp (-r) : ℂ) * (((r : ℂ) * z) ^ n / (Nat.factorial n)) := by
          congr with n
          push_cast
          rw [mul_pow]
          ring
    _ = (Real.exp (-r) : ℂ) * ∑' n, (((r : ℂ) * z) ^ n / (Nat.factorial n)) := tsum_mul_left
    _ = (Real.exp (-r) : ℂ) * Complex.exp (r * z) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℂ) * z)).tsum_eq, exp_eq_exp_ℂ]
    _ = _ := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      push_cast
      congr 1
      ring

/-- Integrating a product over the first n iid marks factors into the n-th power. -/
theorem integral_firstMarks_prod {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (n : ℕ) {h : X → ℂ} (hh : Integrable h ν) :
    ∫ x : ℕ → X, ∏ i : Fin n, h (x i) ∂Measure.infinitePi (fun _ : ℕ => ν) =
      (∫ x, h x ∂ν) ^ n := by
  have hind : iIndepFun (fun (i : Fin n) (x : ℕ → X) => x i)
      (Measure.infinitePi (fun _ : ℕ => ν)) :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ x => x)
      (fun _ => measurable_id)).precomp Fin.val_injective
  have hlaw : HasLaw (fun x : ℕ → X => fun i : Fin n => x i)
      (Measure.pi (fun _ : Fin n => ν)) (Measure.infinitePi (fun _ : ℕ => ν)) :=
    hind.hasLaw_pi (fun i => (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) i).hasLaw)
  have hint : Integrable (fun x : Fin n → X => ∏ i, h (x i)) (Measure.pi (fun _ : Fin n => ν)) :=
    Integrable.fintype_prod fun _ => hh
  have heq := hlaw.integral_comp hint.aestronglyMeasurable
  change (∫ x : ℕ → X, ∏ i : Fin n, h (x i) ∂Measure.infinitePi (fun _ : ℕ => ν)) = _ at heq
  rw [heq, integral_fintype_prod_eq_pow]
  simp only [Fintype.card_fin]

/-- The generating functional of a Poisson number of independent marks. -/
theorem integral_cloud_prod {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (r : ℝ≥0) {h : X → ℂ} (hm : Measurable h)
    (hb : ∀ x, ‖h x‖ ≤ 1) :
    ∫ w : CloudSample X, ∏ i : Fin w.1, h (w.2 i) ∂cloudLaw r ν =
      Complex.exp (r * ((∫ x, h x ∂ν) - 1)) := by
  have hmeas : Measurable (fun w : CloudSample X => ∏ i : Fin w.1, h (w.2 i)) := by
    apply measurable_from_prod_countable_right
    intro n
    change Measurable (fun xs : ℕ → X => ∏ i : Fin n, h (xs i))
    exact Finset.measurable_prod (Finset.univ : Finset (Fin n)) fun i _ =>
      hm.comp (measurable_pi_apply (i : ℕ))
  have hnorm (w : CloudSample X) : ‖∏ i : Fin w.1, h (w.2 i)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hb _)
  have hint : Integrable (fun w : CloudSample X => ∏ i : Fin w.1, h (w.2 i)) (cloudLaw r ν) :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hnorm)
  rw [cloudLaw, integral_prod _ hint]
  have hi : Integrable h ν := Integrable.of_bound hm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hb)
  simp_rw [integral_firstMarks_prod ν _ hi]
  exact integral_pow_poisson r _

end IsotropicVariance.Infra.Poisson
