/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Lipschitz curves: definitions

Lipschitz curves on `[0, 1]` for the continuum model, with cost `∫₀¹ ρ(γ t) ‖γ' t‖ dt`
and length `∫₀¹ ‖γ' t‖ dt`. Everything is stated for curves in a real normed space `E`, and for an
arbitrary weight `G : E → ℝ≥0∞` along the curve, which gives the cost (`G = ρ`) and the length
(`G = 1`). Nothing here depends on the definitions of the model.

* `LipCurve E u v`: a map `ℝ → E`, Lipschitz on `[0, 1]`, from `u` to `v`. Its values off
  `[0, 1]` enter the integrals only through `deriv` at the endpoints, a null set.
* `LipCurve.reverse`, `LipCurve.concat`, `segment`: reversal, concatenation at a common endpoint
  (at speed two), and the straight segment.
* `LipCurve.arcIntegral γ G a b = ∫_{[a,b]} G(γ s) ‖γ' s‖ ds`; `arcCost`, `arcLength`, `cost`,
  `length`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace IsotropicVariance.Infra.Curves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Lipschitz curve from `u` to `v`: a map `ℝ → E`, Lipschitz on `[0, 1]`, with `γ 0 = u` and
`γ 1 = v`. -/
structure LipCurve (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (u v : E) where
  /-- The parametrization. -/
  toFun : ℝ → E
  lipschitzOnWith : ∃ K : ℝ≥0, LipschitzOnWith K toFun (Icc (0 : ℝ) 1)
  map_zero : toFun 0 = u
  map_one : toFun 1 = v

namespace LipCurve

/-- `∫_{[a,b]} G(γ s) ‖γ' s‖ ds`, for a weight `G : E → ℝ≥0∞`. -/
noncomputable def arcIntegral {u v : E} (γ : LipCurve E u v) (G : E → ℝ≥0∞) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Icc a b, G (γ.toFun s) * ‖deriv γ.toFun s‖ₑ

/-- The cost `∫_{[a,b]} ρ(γ s) ‖γ' s‖ ds` of the arc over `[a, b]`, for a density `ρ ≥ 0`. -/
noncomputable def arcCost {u v : E} (γ : LipCurve E u v) (ρ : E → ℝ≥0) (a b : ℝ) : ℝ≥0∞ :=
  γ.arcIntegral (fun x => (ρ x : ℝ≥0∞)) a b

/-- The length `∫_{[a,b]} ‖γ' s‖ ds` of the arc over `[a, b]`. -/
noncomputable def arcLength {u v : E} (γ : LipCurve E u v) (a b : ℝ) : ℝ≥0∞ :=
  γ.arcIntegral (fun _ => 1) a b

/-- The cost `∫₀¹ ρ(γ t) ‖γ' t‖ dt` of a curve. -/
noncomputable def cost {u v : E} (γ : LipCurve E u v) (ρ : E → ℝ≥0) : ℝ≥0∞ :=
  γ.arcCost ρ 0 1

/-- The length `∫₀¹ ‖γ' t‖ dt` of a curve. -/
noncomputable def length {u v : E} (γ : LipCurve E u v) : ℝ≥0∞ :=
  γ.arcLength 0 1

/-- An affine map `t ↦ a + t c`, `c ≥ 0`, is `c`-Lipschitz. -/
theorem lipschitzWith_affine (a c : ℝ) (hc : 0 ≤ c) :
    LipschitzWith (Real.toNNReal c) (fun t : ℝ => a + t * c) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hc,
    show a + x * c - (a + y * c) = (x - y) * c by ring, abs_mul, abs_of_nonneg hc, mul_comm]

/-- The reversed curve `t ↦ γ (1 - t)`, from `v` to `u`. -/
def reverse {u v : E} (γ : LipCurve E u v) : LipCurve E v u where
  toFun t := γ.toFun (1 - t)
  lipschitzOnWith := by
    obtain ⟨K, hK⟩ := γ.lipschitzOnWith
    have hl : LipschitzWith 1 (fun t : ℝ => 1 - t) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, Real.dist_eq, show 1 - x - (1 - y) = -(x - y) by ring, abs_neg]
      simp
    exact ⟨K * 1, hK.comp hl.lipschitzOnWith
      (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)⟩
  map_zero := by simp [γ.map_one]
  map_one := by simp [γ.map_zero]

end LipCurve

/-- The straight segment `t ↦ u + t (v - u)` from `u` to `v`. -/
noncomputable def segment (u v : E) : LipCurve E u v where
  toFun t := u + t • (v - u)
  lipschitzOnWith := by
    refine ⟨‖v - u‖₊, (LipschitzWith.of_dist_le_mul fun x y => ?_).lipschitzOnWith⟩
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
      Real.norm_eq_abs, mul_comm]
    simp
  map_zero := by simp
  map_one := by simp

end IsotropicVariance.Infra.Curves
