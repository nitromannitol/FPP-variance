/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Quadratic forms on a finite-dimensional space: two-sided bounds

A quadratic form `q` on a finite-dimensional real normed space `E` satisfies:

* `exists_abs_le_mul_norm_sq_of_quadraticForm`: `|q h| ≤ C ‖h‖²` for some `C ≥ 0`. The polar form
  of `q` is a bilinear map on a finite-dimensional space, hence continuous, and `2 q h` is its value
  at `(h, h)`.
* `exists_pos_mul_norm_sq_le_of_posDef`: if `q` is positive definite, `c ‖h‖² ≤ q h` for some
  `c > 0`. The form is continuous, so it attains a positive minimum `c` on the compact unit sphere,
  and `q h = ‖h‖² q(h/‖h‖)`.

These are the constants of the quadratic part `h·Bh` of equation `eq:curvature`: the least and
greatest eigenvalues of `B` in the proof of Lemma `lem:support`, and the
positive definiteness in the proof of Lemma `lem:chart`.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Proofs.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The polar form of a quadratic form on a finite-dimensional space, as a continuous bilinear
map. -/
noncomputable def polarCLM (q : QuadraticForm ℝ E) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).toLinearMap ∘ₗ
      QuadraticMap.polarBilin q)

theorem polarCLM_apply (q : QuadraticForm ℝ E) (x y : E) :
    polarCLM q x y = QuadraticMap.polar q x y := rfl

/-- `2 q h` is the polar form at `(h, h)`. -/
theorem two_mul_apply_eq_polarCLM (q : QuadraticForm ℝ E) (h : E) :
    2 * q h = polarCLM q h h := by
  rw [polarCLM_apply, QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat]

/-- **A quadratic form is bounded by a multiple of `‖h‖²`.** -/
theorem exists_abs_le_mul_norm_sq_of_quadraticForm (q : QuadraticForm ℝ E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : E, |q h| ≤ C * ‖h‖ ^ 2 := by
  refine ⟨‖polarCLM q‖ / 2, by positivity, fun h => ?_⟩
  have h1 : |2 * q h| ≤ ‖polarCLM q‖ * ‖h‖ * ‖h‖ := by
    rw [two_mul_apply_eq_polarCLM, ← Real.norm_eq_abs]
    exact (polarCLM q).le_opNorm₂ h h
  rw [abs_mul, abs_two] at h1
  nlinarith [abs_nonneg (q h)]

/-- A quadratic form on a finite-dimensional space is continuous. -/
theorem continuous_quadraticForm (q : QuadraticForm ℝ E) : Continuous fun h : E => q h := by
  have hc : Continuous fun h : E => polarCLM q h h :=
    (polarCLM q).continuous.clm_apply continuous_id
  have heq : (fun h : E => q h) = fun h => (1 / 2 : ℝ) * polarCLM q h h := by
    funext h
    rw [← two_mul_apply_eq_polarCLM]
    ring
  rw [heq]
  exact continuous_const.mul hc

/-- **A positive definite quadratic form is bounded below by a positive multiple of `‖h‖²`.** -/
theorem exists_pos_mul_norm_sq_le_of_posDef {q : QuadraticForm ℝ E} (hq : q.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ h : E, c * ‖h‖ ^ 2 ≤ q h := by
  by_cases hne : (Metric.sphere (0 : E) 1).Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne
      (continuous_quadraticForm q).continuousOn
    have hx₀0 : x₀ ≠ 0 := by
      rintro rfl
      simp at hx₀
    refine ⟨q x₀, hq x₀ hx₀0, fun h => ?_⟩
    by_cases hh : h = 0
    · subst hh
      simp
    have hn : 0 < ‖h‖ := norm_pos_iff.2 hh
    set u : E := ‖h‖⁻¹ • h with hudef
    have hu : u ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, hudef, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
    have hqu : q x₀ ≤ q u := hmin hu
    have hhu : h = ‖h‖ • u := by
      rw [hudef, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hqh : q h = ‖h‖ ^ 2 * q u := by
      conv_lhs => rw [hhu]
      rw [QuadraticMap.map_smul, smul_eq_mul, sq]
    rw [hqh, mul_comm]
    exact mul_le_mul_of_nonneg_left hqu (sq_nonneg _)
  · refine ⟨1, one_pos, fun h => ?_⟩
    have hh : h = 0 := by
      by_contra hh
      have hn : 0 < ‖h‖ := norm_pos_iff.2 hh
      refine hne ⟨‖h‖⁻¹ • h, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn),
        inv_mul_cancel₀ hn.ne']
    subst hh
    simp

end CurvatureVariance.Paper.Proofs.Geometry
