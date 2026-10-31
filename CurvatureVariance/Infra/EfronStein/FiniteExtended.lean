/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.EfronStein.Coordinates
public import CurvatureVariance.Infra.EfronStein.Finite

/-!
# The extended-valued Efron–Stein inequality on a finite product

As in the continuum library, `IsotropicVariance.Infra.EfronStein.FiniteExtended`. This is
[BLM03, Proposition 1, p. 1584], which the paper reaches through the proof of Lemma `lem:residual`
and the third paragraph of [AB26, proof of Lemma 6.3]. The one change: the continuum has the fact
`‖a‖ₑ² = ofReal (a²)` in its `IsotropicVariance.Infra.EfronStein.Coordinates`
(`enorm_sq_eq_ofReal_sq`), and the lattice has it in `CurvatureVariance.Infra.EfronStein.Countable`
(`enorm_sub_sq_eq_ofReal`), which this file does not import. The two `simp only`
calls that used it use Mathlib's `enorm_pow` and `Real.enorm_eq_ofReal` instead.

Let `(X i, μ i)`, `i : Fin n`, be probability spaces and `f` a measurable function on `Π i, X i`.
The theorem `evariance_le_half_sum_refresh_energy_fin` states the Efron–Stein inequality in
`[0, ∞]`, with no moment assumption on `f`:

`evariance f (Measure.pi μ) ≤ ½ ∑ᵢ ∫⁻ x, ∫⁻ y, ‖f x - f (x[i ↦ y])‖ₑ² dμᵢ(y) d(Measure.pi μ)(x)`.

The case of a right side equal to `∞` is trivial. Otherwise each refresh energy is finite, and this
forces `f ∈ L²` (`memLp_two_of_refresh_energy_ne_top_fin`): telescope between two independent
complete configurations, then fix one integrable section. The inequality then follows from
`efronStein_fin`.

This file imports neither `CurvatureVariance.Infra.EfronStein.Countable` nor anything above it, so
that the countable inequality may be built on the finite one.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace CurvatureVariance.Infra.EfronStein

variable {n : ℕ} {X : Fin n → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : Fin n) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Finite single-coordinate refresh energies force square integrability on a finite product,
without an a priori moment assumption. -/
theorem memLp_two_of_refresh_energy_ne_top_fin (f : ((i : Fin n) → X i) → ℝ) (hf : Measurable f)
    (hE : ∀ i, (∫⁻ x, ∫⁻ y, ‖f x - f (Function.update x i y)‖ₑ ^ 2 ∂μ i ∂Measure.pi μ) ≠ ∞) :
    MemLp f 2 (Measure.pi μ) := by
  classical
  let P := Measure.infinitePi μ
  have hP : P = Measure.pi μ := Measure.infinitePi_eq_pi μ
  let D := fun (i : Fin n) (q : ((j : Fin n) → X j) × X i) =>
    f q.1 - f (Function.update q.1 i q.2)
  have hD (i : Fin n) : MemLp (D i) 2 (P.prod (μ i)) := by
    have hDm : Measurable (D i) := (hf.comp measurable_fst).sub (hf.comp measurable_update')
    apply (memLp_two_iff_integrable_sq hDm.aestronglyMeasurable).mpr
    refine ⟨hDm.aestronglyMeasurable.pow 2, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun q => sq_nonneg (D i q))).mpr ?_⟩
    have he : (∫⁻ q : ((j : Fin n) → X j) × X i, ENNReal.ofReal (D i q ^ 2) ∂P.prod (μ i)) =
        ∫⁻ x, ∫⁻ y, ‖f x - f (Function.update x i y)‖ₑ ^ 2 ∂μ i ∂Measure.pi μ := by
      rw [lintegral_prod _ (hDm.pow_const 2).ennreal_ofReal.aemeasurable, hP]
      simp only [D, ← enorm_pow, Real.enorm_eq_ofReal (sq_nonneg _)]
    exact he.trans_lt (lt_top_iff_ne_top.mpr (hE i))
  let T := fun k : ℕ => {i : Fin n | (i : ℕ) < k}
  let R := fun k (x y : (j : Fin n) → X j) => resample (T k) x y
  have hInc (i : Fin n) : MemLp (fun q : ((j : Fin n) → X j) × ((j : Fin n) → X j) =>
      f (R (i + 1) q.1 q.2) - f (R i q.1 q.2)) 2 (P.prod P) := by
    have hEval : MeasurePreserving
        (fun q : ((j : Fin n) → X j) × ((j : Fin n) → X j) => (q.1, q.2 i))
        (P.prod P) (P.prod (μ i)) :=
      (MeasurePreserving.id P).prod (measurePreserving_eval_infinitePi μ i)
    have hSwap := measurePreserving_swap_outside μ (T (i + 1))
    have hh := (hD i).comp_measurePreserving (hEval.comp hSwap)
    have hUpd (q : ((j : Fin n) → X j) × ((j : Fin n) → X j)) :
        Function.update (R (i + 1) q.1 q.2) i ((R (i + 1) q.2 q.1) i) = R i q.1 q.2 := by
      funext j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self, R, resample, T, mem_ofPred_eq, Nat.lt_succ_self, ite_true,
          lt_self_iff_false, ite_false]
      · have hv : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
        have hh : (j : ℕ) < (i : ℕ) + 1 ↔ (j : ℕ) < i := by omega
        simp only [Function.update_of_ne hji, R, resample, T, mem_ofPred_eq, hh]
        split_ifs <;> rfl
    convert hh using 1
    funext q
    change _ = D i (R (i + 1) q.1 q.2, R (i + 1) q.2 q.1 i)
    dsimp only [D]
    rw [hUpd]
  have hPair : MemLp (fun q : ((j : Fin n) → X j) × ((j : Fin n) → X j) => f q.1 - f q.2) 2
      (P.prod P) := by
    have hh := memLp_finsetSum Finset.univ (fun i _ => hInc i)
    convert hh using 1
    funext q
    rw [Fin.sum_univ_eq_sum_range (fun k => f (R (k + 1) q.1 q.2) - f (R k q.1 q.2)) n]
    rw [Finset.sum_range_sub (fun k => f (R k q.1 q.2)) n]
    have hRn : R n q.1 q.2 = q.1 := by ext i; exact resample_apply_of_mem i.isLt
    have hR0 : R 0 q.1 q.2 = q.2 := by
      ext i
      exact resample_apply_of_notMem (Nat.not_lt_zero _)
    rw [hRn, hR0]
  have hSection : ∀ᵐ x ∂P, Integrable (fun y => (f x - f y) ^ 2) P :=
    hPair.integrable_sq.prod_right_ae
  obtain ⟨x, hx⟩ := hSection.exists
  have hSec2 : MemLp (fun y => f x - f y) 2 P :=
    (memLp_two_iff_integrable_sq ((hf.const_sub (f x)).aestronglyMeasurable)).mpr hx
  have hh := (memLp_const (f x)).sub hSec2
  rw [hP] at hh
  convert hh using 1
  ext y
  simp only [Pi.sub_apply, sub_sub_cancel]

/-- **The Efron–Stein inequality on a finite product, in `[0, ∞]`**, for a measurable function
with no moment assumption. -/
theorem evariance_le_half_sum_refresh_energy_fin (f : ((i : Fin n) → X i) → ℝ)
    (hf : Measurable f) :
    evariance f (Measure.pi μ) ≤
      (1 / 2 : ℝ≥0∞) * ∑ i, ∫⁻ x, ∫⁻ y, ‖f x - f (Function.update x i y)‖ₑ ^ 2 ∂μ i
        ∂Measure.pi μ := by
  let E := fun i : Fin n => ∫⁻ x, ∫⁻ y, ‖f x - f (Function.update x i y)‖ₑ ^ 2 ∂μ i
    ∂Measure.pi μ
  by_cases htop : ∑ i, E i = ∞
  · change _ ≤ (1 / 2 : ℝ≥0∞) * ∑ i, E i
    rw [htop, ENNReal.mul_top (by norm_num)]
    exact le_top
  have hE (i : Fin n) : E i ≠ ∞ := ne_of_lt ((Finset.single_le_sum (fun j _ => zero_le)
    (Finset.mem_univ i)).trans_lt (lt_top_iff_ne_top.mpr htop))
  have hf2 := memLp_two_of_refresh_energy_ne_top_fin μ f hf hE
  have hh := efronStein_fin n X μ f hf hf2
  rw [← integral_sub_integral_sq hf2] at hh
  rw [← hf2.ofReal_variance_eq, variance_eq_integral hf.aemeasurable]
  apply (ENNReal.ofReal_le_ofReal hh).trans_eq
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun i _ => integral_nonneg (fun x => integral_nonneg fun y => sq_nonneg _))]
  apply Finset.sum_congr rfl
  intro i _
  have hI : Integrable (fun q : ((j : Fin n) → X j) × X i =>
      (f q.1 - f (Function.update q.1 i q.2)) ^ 2) ((Measure.pi μ).prod (μ i)) :=
    (memLp_resampleDiff_fin μ hf2 i).integrable_sq
  rw [← integral_prod _ hI,
    ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun q => sq_nonneg _)]
  have hMeas : Measurable (fun q : ((j : Fin n) → X j) × X i => ENNReal.ofReal
      ((f q.1 - f (Function.update q.1 i q.2)) ^ 2)) :=
    (((hf.comp measurable_fst).sub (hf.comp measurable_update')).pow_const 2).ennreal_ofReal
  rw [lintegral_prod _ hMeas.aemeasurable]
  simp only [← enorm_pow, Real.enorm_eq_ofReal (sq_nonneg _)]

end CurvatureVariance.Infra.EfronStein
