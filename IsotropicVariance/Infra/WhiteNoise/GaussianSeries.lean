/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import IsotropicVariance.Infra.WhiteNoise.Summability

/-!
# An absolutely convergent series of independent standard Gaussians is Gaussian

Under `Measure.infinitePi (fun _ : J => gaussianReal 0 1)` the coordinates are independent
standard Gaussians. If `∑ⱼ aⱼ² = σ²` and `S` is almost surely the (summable) series `∑ⱼ aⱼ ωⱼ`,
then `S` has law `gaussianReal 0 σ²` (`hasLaw_tsum_mul_gaussian`). The proof computes the
characteristic function of finite partial sums by independence and passes to the limit by
dominated convergence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology

namespace IsotropicVariance.Infra.WhiteNoise

variable {J : Type*}

/-- The characteristic integrand of a finite Gaussian sum factors through independence. -/
lemma integral_cexp_finset_sum (a : J → ℝ) (F : Finset J) (t : ℝ) :
    ∫ ω, cexp (((t * ∑ j ∈ F, a j * ω j : ℝ) : ℂ) * I)
        ∂(Measure.infinitePi fun _ : J => gaussianReal 0 1) =
      ∏ j ∈ F, cexp (-((a j * t) ^ 2 / 2 : ℝ)) := by
  set P : Measure (J → ℝ) := Measure.infinitePi fun _ : J => gaussianReal 0 1 with hP
  have hind : iIndepFun (fun (j : F) (ω : J → ℝ) => ω j) P :=
    (iIndepFun_infinitePi (P := fun _ : J => gaussianReal 0 1) (X := fun _ => id)
      (fun _ => measurable_id)).precomp Subtype.val_injective
  have hmeas : ∀ j : F, AEMeasurable (fun ω : J → ℝ => ω j) P := fun j =>
    (measurable_pi_apply (j : J)).aemeasurable
  have h1 : ∀ ω : J → ℝ, cexp (((t * ∑ j ∈ F, a j * ω j : ℝ) : ℂ) * I) =
      ∏ j : F, cexp (((t * a j * ω j : ℝ) : ℂ) * I) := by
    intro ω
    rw [Finset.prod_coe_sort F (fun j => cexp (((t * a j * ω j : ℝ) : ℂ) * I)),
      ← Complex.exp_sum, Finset.mul_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [h1]
  have h2 := hind.integral_fun_prod_comp (f := fun (j : F) (x : ℝ) => cexp (((t * a j * x : ℝ) : ℂ) * I))
    hmeas (fun j => (by fun_prop : Continuous _).aestronglyMeasurable)
  rw [h2, Finset.prod_coe_sort F (fun j => ∫ ω, cexp (((t * a j * ω j : ℝ) : ℂ) * I) ∂P)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hmp := measurePreserving_eval_infinitePi (fun _ : J => gaussianReal 0 1) j
  have h3 : ∫ ω, cexp (((t * a j * ω j : ℝ) : ℂ) * I) ∂P =
      ∫ x, cexp (((t * a j * x : ℝ) : ℂ) * I) ∂(gaussianReal 0 1) := by
    rw [← hmp.map_eq, integral_map (measurable_pi_apply j).aemeasurable
      (by fun_prop : Continuous fun x : ℝ => cexp (((t * a j * x : ℝ) : ℂ) * I)).aestronglyMeasurable]
  have h4 : ∫ x, cexp (((t * a j * x : ℝ) : ℂ) * I) ∂(gaussianReal 0 1) =
      charFun (gaussianReal 0 1) (t * a j) := by
    rw [charFun_apply_real]
    simp only [Complex.ofReal_mul]
  rw [h3, h4, charFun_gaussianReal]
  congr 1
  push_cast
  ring

open MeasureTheory ProbabilityTheory

/-- **An absolutely convergent series of independent standard Gaussians is Gaussian**: if
`∑ⱼ aⱼ² = σ²` and, almost surely, `S ω = ∑' j, aⱼ ωⱼ` with a summable series, then `S` has law
`gaussianReal 0 σ²`. -/
theorem hasLaw_tsum_mul_gaussian {J : Type*} [Countable J] {a : J → ℝ} {σ2 : ℝ}
    (ha : HasSum (fun j => a j ^ 2) σ2) {S : (J → ℝ) → ℝ}
    (hSm : AEMeasurable S (Measure.infinitePi fun _ : J => gaussianReal 0 1))
    (hS : ∀ᵐ ω ∂(Measure.infinitePi fun _ : J => gaussianReal 0 1),
      Summable (fun j => a j * ω j) ∧ S ω = ∑' j, a j * ω j) :
    HasLaw S (gaussianReal 0 σ2.toNNReal) (Measure.infinitePi fun _ : J => gaussianReal 0 1) := by
  set P : Measure (J → ℝ) := Measure.infinitePi fun _ : J => gaussianReal 0 1 with hP
  refine ⟨hSm, ?_⟩
  obtain ⟨F, hFm, hFj⟩ := exists_finset_seq' J
  have hFt : Tendsto F atTop atTop := tendsto_atTop_finset_of_monotone hFm hFj
  have hσ : 0 ≤ σ2 := ha.nonneg fun j => sq_nonneg _
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hc : charFun (P.map S) t = ∫ ω, cexp (((t * S ω : ℝ) : ℂ) * I) ∂P := by
    rw [charFun_apply_real, integral_map hSm
      (by fun_prop : Continuous fun x : ℝ => cexp ((t : ℂ) * x * I)).aestronglyMeasurable]
    simp only [Complex.ofReal_mul]
  rw [hc, charFun_gaussianReal]
  have hlim : Tendsto (fun n => ∫ ω, cexp (((t * ∑ j ∈ F n, a j * ω j : ℝ) : ℂ) * I) ∂P) atTop
      (𝓝 (∫ ω, cexp (((t * S ω : ℝ) : ℂ) * I) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => ?_)
      (integrable_const _) (fun n => ?_) ?_
    · have : Measurable fun ω : J → ℝ => ∑ j ∈ F n, a j * ω j :=
        Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).const_mul _
      exact (by fun_prop : Continuous fun x : ℝ => cexp (((t * x : ℝ) : ℂ) * I)).comp_aestronglyMeasurable
        this.aestronglyMeasurable
    · refine Eventually.of_forall fun ω => ?_
      rw [Complex.norm_exp_ofReal_mul_I]
    · filter_upwards [hS] with ω ⟨hsum, hSω⟩
      have h1 : Tendsto (fun n => ∑ j ∈ F n, a j * ω j) atTop (𝓝 (S ω)) := by
        rw [hSω]; exact hsum.hasSum.comp hFt
      exact ((by fun_prop : Continuous fun x : ℝ => cexp (((t * x : ℝ) : ℂ) * I)).tendsto _).comp h1
  have hlim2 : Tendsto (fun n => ∫ ω, cexp (((t * ∑ j ∈ F n, a j * ω j : ℝ) : ℂ) * I) ∂P) atTop
      (𝓝 (cexp (-((σ2 * t ^ 2 / 2 : ℝ) : ℂ)))) := by
    have h3 : Tendsto (fun n => ∑ j ∈ F n, a j ^ 2) atTop (𝓝 σ2) := ha.comp hFt
    have h4 : Tendsto (fun n => -(((∑ j ∈ F n, a j ^ 2) * t ^ 2 / 2 : ℝ) : ℂ)) atTop
        (𝓝 (-((σ2 * t ^ 2 / 2 : ℝ) : ℂ))) :=
      ((Complex.continuous_ofReal.tendsto _).comp ((h3.mul_const _).div_const _)).neg
    refine ((Complex.continuous_exp.tendsto _).comp h4).congr fun n => ?_
    rw [integral_cexp_finset_sum, ← Complex.exp_sum]
    simp only [Function.comp]
    congr 1
    push_cast
    rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have := tendsto_nhds_unique hlim hlim2
  rw [this]
  congr 1
  rw [Real.coe_toNNReal _ hσ]
  push_cast
  ring

end IsotropicVariance.Infra.WhiteNoise
