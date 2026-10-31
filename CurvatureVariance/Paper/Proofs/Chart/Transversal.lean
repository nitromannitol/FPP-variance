/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Lemma `lem:chart`: the transversal functional

The linear algebra of the proof of Lemma `lem:chart`. For a direction `ξ` and a hyperplane `H`
with `ℝξ ⊕ H = ℝ^d`:

* `transversal ξ H hc hξ`, the linear functional `ℓ` with `ℓ(ξ) = 1` and `ker ℓ = H`, and the
  projection `projectionOnto H (ℝξ)` along `ξ`, with `x = ℓ(x) ξ + π_H(x)`
  (`transversal_smul_add`);
* `inr`, the embedding `h ↦ (0, h)` of `ℝ^{d-1}`, and the injectivity of `h ↦ v_h = π_H(0, h)`
  when `ξ` has nonzero first coordinate (`projectionOnto_inr_ne_zero`);
* `exists_norm_le_mul_norm`, the bound `‖f h‖ ≤ C‖h‖` of a linear map on a finite-dimensional
  space. The bound `|q(h)| ≤ C‖h‖²` of a quadratic form is
  `Proofs.Geometry.exists_abs_le_mul_norm_sq_of_quadraticForm`.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Chart

open CurvatureVariance.Paper

variable {m : ℕ}

/-- A linear map from a finite-dimensional space is bounded. -/
theorem exists_norm_le_mul_norm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →ₗ[ℝ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : E, ‖f h‖ ≤ C * ‖h‖ :=
  ⟨‖LinearMap.toContinuousLinearMap f‖, norm_nonneg _,
    fun h => (LinearMap.toContinuousLinearMap f).le_opNorm h⟩

/-- The embedding `h ↦ (0, h)` of `ℝ^m` into `ℝ × ℝ^m`. -/
noncomputable def inr : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Pt m :=
  (WithLp.linearEquiv 2 ℝ (ℝ × EuclideanSpace ℝ (Fin m))).symm.toLinearMap ∘ₗ
    LinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin m))

theorem inr_apply (h : EuclideanSpace ℝ (Fin m)) : inr h = WithLp.toLp 2 ((0 : ℝ), h) := rfl

section Transversal

variable (ξ : Pt m) (H : Submodule ℝ (Pt m)) (hc : IsCompl (Submodule.span ℝ {ξ}) H)
  (hξ : ξ ≠ 0)

/-- The transversal functional `ℓ` of the proof of Lemma `lem:chart`: `ℓ(ξ) = 1` and
`ker ℓ = H`. -/
noncomputable def transversal : Pt m →ₗ[ℝ] ℝ :=
  (LinearEquiv.coord ℝ (Pt m) ξ hξ).toLinearMap ∘ₗ Submodule.projectionOnto _ _ hc

/-- Every point is `x = ℓ(x) ξ + π_H(x)`, with `π_H` the projection onto `H` along `ξ`. -/
theorem transversal_smul_add (x : Pt m) :
    transversal ξ H hc hξ x • ξ + (Submodule.projectionOnto H _ hc.symm x : Pt m) = x := by
  simp only [transversal, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coord_apply_smul, Submodule.coe_projectionOnto_apply]
  exact Submodule.projection_add_projection_eq_self hc x

/-- The map `h ↦ v_h = π_H(0, h)` is injective when `ξ` has nonzero first coordinate (the proof
of Lemma `lem:chart`). -/
theorem projectionOnto_inr_ne_zero (ha : ξ.ofLp.1 ≠ 0) {h : EuclideanSpace ℝ (Fin m)}
    (hh : h ≠ 0) : Submodule.projectionOnto H _ hc.symm (inr h) ≠ 0 := by
  intro h0
  rw [Submodule.projectionOnto_apply_eq_zero_iff, Submodule.mem_span_singleton] at h0
  obtain ⟨s, hs⟩ := h0
  have h1 := congrArg (fun z : Pt m => z.ofLp.1) hs
  simp only [WithLp.ofLp_smul, Prod.smul_fst, smul_eq_mul, inr_apply] at h1
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 ha
  have h2 := congrArg (fun z : Pt m => z.ofLp.2) hs
  simp [hs0, inr_apply] at h2
  exact hh h2.symm

end Transversal

end CurvatureVariance.Paper.Chart
