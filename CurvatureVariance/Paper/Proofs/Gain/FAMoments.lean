/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Os.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CurvatureVariance.Infra.Os.Moments
import CurvatureVariance.Paper.Proofs.Gain.FAAnalysis
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Localization.RadiusMoments

/-!
# Moments of finite sums of `O₁` variables (the proof of Lemma `lem:labels`)

* `exists_measurable_family`: measurable versions of finitely many `O_s` variables, each with an
  almost sure property (the variables of Proposition `prop:profiles` on the fine pairs of a
  block);
* `lintegral_ofReal_posPart_div_pow_le`: the `k`-th moment of `max(X, 0)/Q` for `X ≤ O₁(C Q)` is
  at most `2 (1 + k!) C^k`;
* `eLpNorm_posPart_le_of_isOs`: `‖max(X, 0)‖_k ≤ (2 (1 + k!))^{1/k} θ` for `X ≤ O₁(θ)`;
* `lintegral_ofReal_add_pow_comp_le`: `E (g(f₁) + g(f₂))^k ≤ 2^k · 2 E g^k` for two
  measure-preserving maps.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Measurable versions of finitely many `O_s` variables** with almost sure properties: if for
every `i ∈ T` there is `X ≤ O_s(θ)` with `R i ω (X ω)` almost surely, there is a family of
measurable variables with the same properties, almost surely for all `i ∈ T` at once. -/
theorem exists_measurable_family {ι : Type*} {P : Measure Ω} {s θ : ℝ} (T : Finset ι)
    {R : ι → Ω → ℝ → Prop}
    (h : ∀ i ∈ T, ∃ X : Ω → ℝ, CurvatureVariance.IsOs P s θ X ∧ ∀ᵐ ω ∂P, R i ω (X ω)) :
    ∃ X : ι → Ω → ℝ, (∀ i, Measurable (X i)) ∧ (∀ i ∈ T, CurvatureVariance.IsOs P s θ (X i)) ∧
      ∀ᵐ ω ∂P, ∀ i ∈ T, R i ω (X i ω) := by
  classical
  choose X₀ hX₀ using h
  let X : ι → Ω → ℝ := fun i => if hi : i ∈ T then (hX₀ i hi).1.1.mk (X₀ i hi) else 0
  have hXeq : ∀ i (hi : i ∈ T), X i =ᵐ[P] X₀ i hi := by
    intro i hi
    simp only [X, hi, dite_true]
    exact (hX₀ i hi).1.1.ae_eq_mk.symm
  refine ⟨X, fun i => ?_, fun i hi => (hX₀ i hi).1.congr (hXeq i hi).symm, ?_⟩
  · by_cases hi : i ∈ T
    · simp only [X, hi, dite_true]
      exact (hX₀ i hi).1.1.measurable_mk
    · simp only [X, hi, dite_false]
      exact measurable_const
  · refine (Filter.eventually_all_finset T).mpr fun i hi => ?_
    filter_upwards [(hX₀ i hi).2, hXeq i hi] with ω hω heq
    rw [heq]
    exact hω

/-- The `k`-th moment of `max(X, 0)/Q` for `X ≤ O₁(C Q)` is at most `2 (1 + k!) C^k`. -/
theorem lintegral_ofReal_posPart_div_pow_le {P : Measure Ω} {X : Ω → ℝ} {C Q : ℝ}
    (hC : 0 < C) (hQ : 0 < Q) (hX : CurvatureVariance.IsOs P 1 (C * Q) X) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((max (X ω) 0 / Q) ^ k) ∂P ≤
      ENNReal.ofReal (2 * (1 + (k.factorial : ℝ)) * C ^ k) := by
  have hX' : CurvatureVariance.IsOs P 1 C (fun ω => Q⁻¹ * X ω) := by
    have h := (Infra.Os.isOs_mul_iff (P := P) (s := 1) (θ := C * Q) (X := X)
      (inv_pos.mpr hQ)).mpr hX
    rwa [show Q⁻¹ * (C * Q) = C by field_simp] at h
  have h := hX'.lintegral_pos_rpow_le (by norm_num) hC (Nat.cast_nonneg k)
  have hceil : Nat.ceil ((k : ℝ) / 1) = k := by rw [div_one, Nat.ceil_natCast]
  rw [hceil, Real.rpow_natCast] at h
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) h
  rw [Real.rpow_natCast, div_eq_inv_mul, mul_max_of_nonneg _ _ (inv_nonneg.mpr hQ.le), mul_zero]

/-- **`L^k` norm of the positive part of an `O₁(θ)` variable**:
`‖max(X, 0)‖_k ≤ (2 (1 + k!))^{1/k} θ`. -/
theorem eLpNorm_posPart_le_of_isOs {P : Measure Ω} {X : Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hX : CurvatureVariance.IsOs P 1 θ X) {k : ℕ} (hk : 1 ≤ k) :
    eLpNorm (fun ω => max (X ω) 0) k P ≤
      ENNReal.ofReal ((2 * (1 + (k.factorial : ℝ))) ^ (1 / (k : ℝ)) * θ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  refine eLpNorm_le_ofReal_of_lintegral_le (hX.1.max aemeasurable_const).aestronglyMeasurable hk
    (by positivity) ?_
  have h := lintegral_ofReal_posPart_div_pow_le (C := θ) (Q := 1) hθ one_pos
    (by rwa [mul_one]) k
  simp only [div_one] at h
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) (h.trans (le_of_eq ?_))
  · rw [abs_of_nonneg (le_max_right _ _)]
  · congr 1
    rw [mul_pow, ← Real.rpow_natCast ((2 * (1 + (k.factorial : ℝ))) ^ (1 / (k : ℝ))),
      ← Real.rpow_mul (by positivity), one_div_mul_cancel hk0.ne', Real.rpow_one]

/-- **Moments under two measure-preserving maps**: `E (g(f₁) + g(f₂))^k ≤ 2^k · 2 E g^k` for
`g ≥ 0` measurable. -/
theorem lintegral_ofReal_add_pow_comp_le {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {P : Measure Ω} {f₁ f₂ : Ω' → Ω} (h₁ : MeasurePreserving f₁ P' P)
    (h₂ : MeasurePreserving f₂ P' P) {g : Ω → ℝ} (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω)
    (k : ℕ) :
    ∫⁻ z, ENNReal.ofReal ((g (f₁ z) + g (f₂ z)) ^ k) ∂P' ≤
      ENNReal.ofReal (2 ^ k) * (2 * ∫⁻ ω, ENNReal.ofReal (g ω ^ k) ∂P) := by
  have hgk : Measurable fun ω => ENNReal.ofReal (g ω ^ k) := (hg.pow_const k).ennreal_ofReal
  calc ∫⁻ z, ENNReal.ofReal ((g (f₁ z) + g (f₂ z)) ^ k) ∂P'
      ≤ ∫⁻ z, ENNReal.ofReal (2 ^ k) *
          (ENNReal.ofReal (g (f₁ z) ^ k) + ENNReal.ofReal (g (f₂ z) ^ k)) ∂P' := by
        refine lintegral_mono fun z => ?_
        rw [← ENNReal.ofReal_add (pow_nonneg (hg0 _) _) (pow_nonneg (hg0 _) _),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (Localization.Radius.add_pow_le (hg0 _) (hg0 _) k)
    _ = ENNReal.ofReal (2 ^ k) * (∫⁻ z, ENNReal.ofReal (g (f₁ z) ^ k) ∂P' +
          ∫⁻ z, ENNReal.ofReal (g (f₂ z) ^ k) ∂P') := by
        rw [lintegral_const_mul (ENNReal.ofReal (2 ^ k))
          (f := fun z => ENNReal.ofReal (g (f₁ z) ^ k) + ENNReal.ofReal (g (f₂ z) ^ k))
          ((hgk.comp h₁.measurable).add (hgk.comp h₂.measurable)),
          lintegral_add_left (f := fun z => ENNReal.ofReal (g (f₁ z) ^ k))
            (hgk.comp h₁.measurable)]
    _ = ENNReal.ofReal (2 ^ k) * (2 * ∫⁻ ω, ENNReal.ofReal (g ω ^ k) ∂P) := by
        rw [h₁.lintegral_comp hgk, h₂.lintegral_comp hgk, two_mul]

end CurvatureVariance.Paper.Gain
