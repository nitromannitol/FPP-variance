/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Basic
public import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.Linarith
import CurvatureVariance.Infra.FPP.MeanSkeleton
import CurvatureVariance.Infra.Geodesics.Basic
import CurvatureVariance.Infra.Kesten.Estimate

/-!
# The pieces of a nearly optimal path between monotone indices

The second step of the proof of Lemma `lem:slabs` (2), for a walk `γ` from `u` to `v` split at
indices of its vertices:

* `Infra.FPP.walkCost_take_add_drop`, `walkCost_take_add_passageTime_le`: the prefix costs
  `walkCost (γ.take a)` increase, from `a` to `b ≥ a`, by at least `T(γ_a, γ_b)`;
* `walkCost_drop_le`: if `γ` costs at most `T(u,v) + ζ`, its suffix from `γ_a` costs at most
  `T(γ_a, v) + ζ`;
* `sum_passageTime_getVert_le`: along monotone indices `k 0 ≤ ⋯ ≤ k K`, the passage times between
  consecutive vertices `γ_{k i}` sum to at most `walkCost γ` ("the passage times of the pieces
  of the geodesic between consecutive `x_i` add up to `T(u,v)`" for a geodesic).

The decompositions use Mathlib's `Walk.take` and `Walk.drop`.
-/

@[expose] public section

open scoped NNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- From the index `a` to the index `b ≥ a`, the prefix cost increases by at least
`T(γ_a, γ_b)`. -/
theorem walkCost_take_add_passageTime_le (ω : Config m) {u v : Vertex m}
    (γ : (latticeGraph m).Walk u v) {a b : ℕ} (hab : a ≤ b) :
    walkCost ω (γ.take a) + passageTime ω (γ.getVert a) (γ.getVert b) ≤
      walkCost ω (γ.take b) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [γ.take_add_eq a c, Infra.Geodesics.walkCost_copy, walkCost_append]
  refine add_le_add le_rfl ?_
  calc passageTime ω (γ.getVert a) (γ.getVert (a + c))
      = passageTime ω (γ.getVert a) ((γ.drop a).getVert c) := by
        rw [SimpleGraph.Walk.drop_getVert]
    _ ≤ walkCost ω ((γ.drop a).take c) := Infra.FPP.passageTime_le_walkCost ω _

/-- **The suffix of a nearly optimal walk.** If `γ` costs at most `T(u,v) + ζ`, its suffix from
`γ_a` costs at most `T(γ_a, v) + ζ`. -/
theorem walkCost_drop_le {ω : Config m} {u v : Vertex m} {γ : (latticeGraph m).Walk u v} {ζ : ℝ}
    (hγ : (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + ζ) (a : ℕ) :
    (walkCost ω (γ.drop a) : ℝ) ≤ passageTimeReal ω (γ.getVert a) v + ζ := by
  have h1 : (walkCost ω (γ.take a) : ℝ) + walkCost ω (γ.drop a) = walkCost ω γ := by
    exact_mod_cast Infra.FPP.walkCost_take_add_drop ω γ a
  have h2 : (passageTime ω u (γ.getVert a) : ℝ) ≤ walkCost ω (γ.take a) := by
    exact_mod_cast Infra.FPP.passageTime_le_walkCost ω (γ.take a)
  have h3 : (passageTime ω u v : ℝ) ≤
      passageTime ω u (γ.getVert a) + passageTime ω (γ.getVert a) v := by
    exact_mod_cast passageTime_triangle ω u (γ.getVert a) v
  unfold passageTimeReal at hγ ⊢
  linarith

/-- Along monotone indices, the passage times between consecutive vertices plus the cost of the
first prefix are at most the cost of the last prefix. -/
theorem sum_passageTime_getVert_add_le (ω : Config m) {u v : Vertex m}
    (γ : (latticeGraph m).Walk u v) {k : ℕ → ℕ} {K : ℕ} (hk : ∀ i < K, k i ≤ k (i + 1)) :
    ∑ i ∈ Finset.range K, passageTime ω (γ.getVert (k i)) (γ.getVert (k (i + 1))) +
        walkCost ω (γ.take (k 0)) ≤ walkCost ω (γ.take (k K)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, add_right_comm]
    exact (add_le_add (ih fun i hi => hk i (by omega)) le_rfl).trans
      (walkCost_take_add_passageTime_le ω γ (hk K (by omega)))

/-- **The pieces sum to at most the walk.** Along monotone indices `k 0 ≤ ⋯ ≤ k K`, the passage
times between the consecutive vertices `γ_{k i}` sum to at most `walkCost γ`. -/
theorem sum_passageTime_getVert_le (ω : Config m) {u v : Vertex m}
    (γ : (latticeGraph m).Walk u v) {k : ℕ → ℕ} {K : ℕ} (hk : ∀ i < K, k i ≤ k (i + 1)) :
    ∑ i ∈ Finset.range K, passageTime ω (γ.getVert (k i)) (γ.getVert (k (i + 1))) ≤
      walkCost ω γ :=
  (le_self_add.trans (sum_passageTime_getVert_add_le ω γ hk)).trans (Infra.Kesten.walkCost_take_le ω γ _)

end CurvatureVariance.Paper.Proofs.Geometry
