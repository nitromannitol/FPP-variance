/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Inputs.Entropy
public import CurvatureVariance.Infra.Entropy.CoordinateBound

/-!
# The elementary entropy bound

As `IsotropicVariance.Infra.Entropy.Atoms` in the continuum library, with two changes:

* the continuum's `Infra.Entropy.FiniteLaws` has no counterpart here, since the lattice has its
  three lemmas under the same names in `Infra.Entropy.CoordinateBound`: `ae_of_atoms`,
  `sq_le_div_of_atom` and `integral_sub_mean_sq`;
* the continuum's `IsotropicVariance.Cited.entropy` is `CurvatureVariance.entropy` here. The
  lattice has a twin `Infra.Entropy.entropy` with the same body, which the proofs meet through
  `entropy_eq_integral_entropyDensity`. The statements below use `CurvatureVariance.entropy`, the
  definition that `CurvatureVariance.variance_mul_log_le_of_entropy_le` takes.

For a law on a finite set whose values have probability `0` or at least `α`, the logarithmic Sobolev
inequality `Ent[g²] ≤ (4/α) Var[g]` holds. This is the sentence after [AB26, Proposition 1.3]:
"`g² ≤ E[g²]/α` gives `Ent[g²] ≤ Var[g²]/E[g²] ≤ 4 Var[g]/α`". The three
steps:

* `g² ≤ E[g²]/α` on the values of positive probability (`sq_le_div_of_atom`);
* `Ent[h] ≤ Var[h]/E[h]` for `h ≥ 0`, from `log x ≤ x − 1` (`entropy_le_variance_div`);
* `Var[g²] ≤ 4 S Var[g]` if `g² ≤ S` (`variance_sq_le_mul_variance`), from
  `Var[g²] ≤ E[(g² − E[g]²)²]` and `g² − E[g]² = (g − E[g])(g + E[g])`.

## Main results

* `entropy_sq_le_four_div_mul_variance_of_atoms`: the bound.
-/

@[expose] public section

open MeasureTheory Real ProbabilityTheory

namespace CurvatureVariance.Infra.Entropy

/-- `ψ_m(t) ≤ (t − m)²/m` for `m > 0` and `t ≥ 0`: this is `log x ≤ x − 1` at `x = t/m`. -/
theorem entropyDensity_le_sq_div {m t : ℝ} (hm : 0 < m) (ht : 0 ≤ t) :
    entropyDensity m t ≤ (t - m) ^ 2 / m := by
  have e : (t - m) ^ 2 / m = t * (t / m - 1) - t + m := by
    field_simp
    ring
  rw [e]
  rcases ht.eq_or_lt with rfl | ht
  · simp
  · have h := log_le_sub_one_of_pos (div_pos ht hm)
    rw [log_div ht.ne' hm.ne'] at h
    have h' := mul_le_mul_of_nonneg_left h ht.le
    unfold entropyDensity
    rw [mul_sub] at h'
    linarith only [h']

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

/-- `Ent[h] ≤ Var[h]/E[h]` for `h ≥ 0` (the first inequality of the sentence after
[AB26, Proposition 1.3]). If `E[h] = 0`, then `h = 0` almost everywhere and both sides vanish. -/
theorem entropy_le_variance_div (σ : Measure X) [IsProbabilityMeasure σ] {h : X → ℝ}
    (hh : 0 ≤ᵐ[σ] h) : CurvatureVariance.entropy σ h ≤ variance h σ / ∫ x, h x ∂σ := by
  have hi : Integrable h σ := Integrable.of_finite
  have hm0 : 0 ≤ ∫ x, h x ∂σ := integral_nonneg_of_ae hh
  rcases hm0.eq_or_lt with hm | hm
  · have hz := integral_eq_zero_imp_ae_zero hh hi hm.symm
    have hlog : ∫ x, h x * log (h x) ∂σ = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hz] with x hx
      simp [hx]
    simp [CurvatureVariance.entropy, ← hm, hlog]
  · set m := ∫ x, h x ∂σ with hmdef
    have hpt : ∀ᵐ x ∂σ, entropyDensity m (h x) ≤ (h x - m) ^ 2 / m := by
      filter_upwards [hh] with x hx
      exact entropyDensity_le_sq_div hm hx
    calc CurvatureVariance.entropy σ h = ∫ x, entropyDensity m (h x) ∂σ :=
          entropy_eq_integral_entropyDensity hi Integrable.of_finite
      _ ≤ ∫ x, (h x - m) ^ 2 / m ∂σ :=
          integral_mono_ae Integrable.of_finite Integrable.of_finite hpt
      _ = variance h σ / m := by
          rw [integral_div, variance_eq_integral Measurable.of_discrete.aemeasurable]

/-- `Var[g²] ≤ 4 S Var[g]` if `g² ≤ S` almost everywhere (the second inequality of the sentence
after [AB26, Proposition 1.3]): `Var[g²] ≤ E[(g² − E[g]²)²]`, with
`g² − E[g]² = (g − E[g])(g + E[g])` and `(g + E[g])² ≤ 2 g² + 2 E[g]² ≤ 4 S`. -/
theorem variance_sq_le_mul_variance (σ : Measure X) [IsProbabilityMeasure σ] (g : X → ℝ) {S : ℝ}
    (hS : ∀ᵐ x ∂σ, g x ^ 2 ≤ S) : variance (fun x => g x ^ 2) σ ≤ 4 * S * variance g σ := by
  have hm : ∫ x, g x ^ 2 ∂σ ≤ S := by
    simpa using integral_mono_ae (Integrable.of_finite : Integrable (fun x => g x ^ 2) σ)
      (integrable_const S) hS
  have hvar : 0 ≤ ∫ x, (g x - ∫ y, g y ∂σ) ^ 2 ∂σ := integral_nonneg fun x => sq_nonneg _
  rw [integral_sub_mean_sq] at hvar
  set a := ∫ y, g y ∂σ with ha
  have ha2 : a ^ 2 ≤ S := by linarith only [hvar, hm]
  have hpt : ∀ᵐ x ∂σ, (g x ^ 2 - a ^ 2) ^ 2 ≤ 4 * S * (g x - a) ^ 2 := by
    filter_upwards [hS] with x hx
    have hplus : (g x + a) ^ 2 ≤ 4 * S := by
      linarith only [sq_nonneg (g x - a), hx, ha2]
    have e : (g x ^ 2 - a ^ 2) ^ 2 = (g x + a) ^ 2 * (g x - a) ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hplus (sq_nonneg _)
  calc variance (fun x => g x ^ 2) σ = variance (fun x => g x ^ 2 - a ^ 2) σ :=
        (variance_sub_const Measurable.of_discrete.aestronglyMeasurable _).symm
    _ ≤ ∫ x, (g x ^ 2 - a ^ 2) ^ 2 ∂σ :=
        variance_le_expectation_sq Measurable.of_discrete.aestronglyMeasurable
    _ ≤ ∫ x, 4 * S * (g x - a) ^ 2 ∂σ :=
        integral_mono_ae Integrable.of_finite Integrable.of_finite hpt
    _ = 4 * S * variance g σ := by
        rw [integral_const_mul, variance_eq_integral Measurable.of_discrete.aemeasurable]

/-- **The elementary entropy bound** (the logarithmic Sobolev inequality assumed in
[AB26, Proposition 1.3], from the sentence after it): for a law on a finite set whose values have
probability `0` or at least `α > 0`, every function `g` satisfies `Ent[g²] ≤ (4/α) Var[g]`. [AB26]
writes: "`g² ≤ E[g²]/α` gives `Ent[g²] ≤ Var[g²]/E[g²] ≤ 4 Var[g]/α`". -/
theorem entropy_sq_le_four_div_mul_variance_of_atoms (σ : Measure X) [IsProbabilityMeasure σ]
    {α : ℝ} (hα : 0 < α) (hatom : ∀ x, σ {x} = 0 ∨ ENNReal.ofReal α ≤ σ {x}) (g : X → ℝ) :
    CurvatureVariance.entropy σ (fun x => g x ^ 2) ≤ 4 / α * variance g σ := by
  have hatom' : ∀ x, 0 < σ.real {x} → α ≤ σ.real {x} := by
    intro x hx
    rcases hatom x with h0 | hle
    · simp [Measure.real, h0] at hx
    · exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hle
  have hm0 : 0 ≤ ∫ x, g x ^ 2 ∂σ := integral_nonneg fun x => sq_nonneg _
  have hS := ae_of_atoms σ (P := fun x => g x ^ 2 ≤ (∫ y, g y ^ 2 ∂σ) / α)
    fun x hx => sq_le_div_of_atom σ hα hatom' g hx
  have hvar := variance_sq_le_mul_variance σ g hS
  refine (entropy_le_variance_div σ (ae_of_all _ fun x => sq_nonneg (g x))).trans ?_
  rcases hm0.eq_or_lt with hm | hm
  · rw [← hm, div_zero]
    exact mul_nonneg (div_pos four_pos hα).le (variance_nonneg _ _)
  · rw [div_le_iff₀ hm]
    calc variance (fun x => g x ^ 2) σ ≤ 4 * ((∫ y, g y ^ 2 ∂σ) / α) * variance g σ := hvar
      _ = 4 / α * variance g σ * ∫ y, g y ^ 2 ∂σ := by ring

end CurvatureVariance.Infra.Entropy
