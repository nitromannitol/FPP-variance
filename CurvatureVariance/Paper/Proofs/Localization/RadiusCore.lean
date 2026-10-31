/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.RadiusBoxes
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.Shear

/-!
# Lemma `lem:localization`: a vertex splits a walk

`passageTime_add_le_walkCost`: for a vertex `x` of a walk from `u` to `v`, `T(u, x) + T(x, v)` is
at most the cost of the walk. It gives the upper bound in the proof of Lemma `lem:localization` at
the vertices of a path (`passageTime_through_le`).
-/

@[expose] public section

open MeasureTheory Set InnerProductGeometry
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization.Radius

open CurvatureVariance.Paper

variable {m : ℕ}

/-- For a vertex `x` of a walk from `u` to `v`, `T(u, x) + T(x, v)` is at most the cost. -/
theorem passageTime_add_le_walkCost (ω : Config m) {u v : Vertex m}
    (γ : (latticeGraph m).Walk u v) {x : Vertex m} (hx : x ∈ γ.support) :
    passageTimeReal ω u x + passageTimeReal ω x v ≤ (walkCost ω γ : ℝ) := by
  classical
  have h := congrArg (walkCost ω) (γ.take_spec hx)
  rw [Infra.FPP.walkCost_append] at h
  have h1 := Infra.FPP.passageTime_le_walkCost ω (γ.takeUntil x hx)
  have h2 := Infra.FPP.passageTime_le_walkCost ω (γ.dropUntil x hx)
  simp only [passageTimeReal]
  rw [← h]
  exact_mod_cast add_le_add h1 h2

end CurvatureVariance.Paper.Localization.Radius
