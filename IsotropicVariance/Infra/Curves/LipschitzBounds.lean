/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Lipschitz
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Lipschitz curves: length and cost bounds

For a Lipschitz curve in a finite-dimensional real normed space, the arc length dominates the
distance between endpoints, a density bounded below (above) along the arc bounds the cost below
(above) by the density bound times the length, and the straight segment has length `‖v - u‖`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace IsotropicVariance.Infra.Curves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of the segment is constant. -/
theorem hasDerivAt_segment (u v : E) (t : ℝ) :
    HasDerivAt (segment u v).toFun (v - u) t := by
  simpa [segment] using ((hasDerivAt_id t).smul_const (v - u)).const_add u

/-- The length of the segment is `‖v - u‖`. -/
theorem length_segment (u v : E) : (segment u v).length = ‖v - u‖ₑ := by
  unfold LipCurve.length LipCurve.arcLength LipCurve.arcIntegral
  simp [fun t => (hasDerivAt_segment u v t).deriv]

/-- The segment between two points of a convex set stays in the set. -/
theorem segment_mem_of_convex {S : Set E} (hS : Convex ℝ S) {u v : E} (hu : u ∈ S) (hv : v ∈ S) :
    ∀ t ∈ Icc (0 : ℝ) 1, (segment u v).toFun t ∈ S := fun _ ht =>
  hS.add_smul_sub_mem hu hv ht

end IsotropicVariance.Infra.Curves
