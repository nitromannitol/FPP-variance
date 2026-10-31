/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Slabs
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Subgradients exist

`exists_isSubgradient`: every norm on `ℝ^d` has a supporting covector at every point (Hahn–Banach),
so the subgradients `P_t ∈ ∂μ(1, t)` exist (the paper's subgradients `ζ_t`, the text
before Lemma `lem:support`). This file depends only on the definitions, so the files that need a
covector need not import the proof of Lemma `lem:support`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper

variable {m : ℕ}

/-- **Every norm has a subgradient at every point** (Hahn–Banach). -/
theorem exists_isSubgradient (μ : PtNorm m) (x : Pt m) : ∃ p : Pt m, IsSubgradient μ x p := by
  by_cases hx : x = 0
  · refine ⟨0, ?_, fun z => ?_⟩
    · simp [hx]
    · simp only [inner_zero_left]
      exact apply_nonneg _ _
  let f : Pt m →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton x (μ.1 x) hx
  obtain ⟨g, hgf, hgμ⟩ := exists_extension_of_le_sublinear f μ.1
    (fun c hc z => by rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hc])
    (fun y z => map_add_le_add μ.1 y z) (fun y => by
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 y.2
      have hy : y = a • (⟨x, Submodule.mem_span_singleton_self x⟩ : f.domain) :=
        Subtype.ext (by simp [ha])
      rw [hy, LinearPMap.map_smul, LinearPMap.mkSpanSingleton_apply ℝ ℝ hx, Submodule.coe_smul,
        smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (le_abs_self a) (apply_nonneg _ _))
  let p : Pt m := (InnerProductSpace.toDual ℝ (Pt m)).symm (LinearMap.toContinuousLinearMap g)
  have hp : ∀ z, ⟪p, z⟫_ℝ = g z := fun z => by
    simp [p, InnerProductSpace.toDual_symm_apply]
  refine ⟨p, ?_, fun z => (hp z).trans_le (hgμ z)⟩
  rw [hp]
  exact (hgf ⟨x, Submodule.mem_span_singleton_self x⟩).trans
    (LinearPMap.mkSpanSingleton_apply ℝ ℝ hx _)

end CurvatureVariance.Paper.Proofs.Geometry
