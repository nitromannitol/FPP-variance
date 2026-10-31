/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.HitsFirst
public import CurvatureVariance.Paper.Proofs.Geometry.HitsSmall
public import CurvatureVariance.Paper.Proofs.Geometry.HitsIncrements
public import CurvatureVariance.Paper.Proofs.Geometry.HitsComparison
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:slabs` (2): two identities

Two identities for the proof of Lemma `lem:slabs` (2) (`slabTwo_of`, `Proofs.Geometry.SlabsHits`),
which follows the proof of Lemma `lem:slabs` (2): the first hits `x_i` come in
order along the geodesic (`exists_hitIndex`), the cone bounds give the increments
(`increment_of_coneAt`, with `eventually_cone_small` for the smallness of the cone bounds), and the
passage times of the pieces add up (`tupleCost_le_walkCost`).

* `mul_rpow_slope`: `n · n^{δ/100−1/4} = n^{3/4+δ/100}`;
* `point_sub_snd`: the transverse part of a difference of vertices.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- `n · n^{δ/100−1/4} = n^{3/4+δ/100}`. -/
theorem mul_rpow_slope {n δ : ℝ} (hn : 0 < n) :
    n * n ^ (δ / 100 - 1 / 4) = n ^ ((3 : ℝ) / 4 + δ / 100) := by
  calc n * n ^ (δ / 100 - 1 / 4) = n ^ (1 : ℝ) * n ^ (δ / 100 - 1 / 4) := by rw [Real.rpow_one]
    _ = n ^ (1 + (δ / 100 - 1 / 4)) := (Real.rpow_add hn _ _).symm
    _ = n ^ ((3 : ℝ) / 4 + δ / 100) := by ring_nf

/-- The transverse part of a difference of vertices. -/
theorem point_sub_snd (y z : Vertex m) :
    (point y - point z).snd = transversePoint (y.2 - z.2) := by
  simp

variable {M : Model m} {C Cs S ε : ℝ} {N : ℕ} {ω : Config m}

end CurvatureVariance.Paper.Proofs.Geometry
