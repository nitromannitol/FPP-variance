/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Slabs
public import CurvatureVariance.Paper.Proofs.Geometry.HitsPieces
public import CurvatureVariance.Paper.Proofs.Geometry.SlabSurgery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# The comparison between the slab minimum and the passage time in Lemma `lem:slabs` (2)

The lower bound and the last step of the proof of Lemma `lem:slabs` (2), deterministically:

* `passageTime_le_slabMin`: `T(u,v) ≤ F`, by `T_P ≥ T` and the triangle inequality: for every
  admissible tuple, `T(u,v) ≤ ∑ T(pieces) ≤ ∑ D(pieces)`, slab walks being walks; with no admissible
  tuple `F = ∞`;
* `tupleCost_le_walkCost`: for a tuple of vertices `γ_{k i}` of a walk `γ` at monotone indices, if
  each slab passage time exceeds the passage time of its piece by at most `c`, then
  `tupleCost ≤ walkCost γ + K c` ("the passage times of the pieces of the geodesic between
  consecutive `x_i` add up to `T(u,v)`, and, by (1), each piece has passage time at least
  `T^{(i)}(x_{i−1},x_i) − CS²`").
-/

@[expose] public section

open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- The triangle inequality along a tuple of vertices. -/
theorem passageTime_le_sum_fin (ω : Config m) : ∀ {K : ℕ} (P : Fin (K + 1) → Vertex m),
    passageTime ω (P 0) (P (Fin.last K)) ≤ ∑ i : Fin K, passageTime ω (P i.castSucc) (P i.succ)
  | 0, P => by simp
  | K + 1, P => by
    rw [Fin.sum_univ_castSucc]
    have ih := passageTime_le_sum_fin ω (fun i : Fin (K + 1) => P i.castSucc)
    simp only [Fin.castSucc_zero] at ih
    calc passageTime ω (P 0) (P (Fin.last (K + 1)))
        ≤ passageTime ω (P 0) (P (Fin.last K).castSucc) +
            passageTime ω (P (Fin.last K).castSucc) (P (Fin.last (K + 1))) :=
          passageTime_triangle ω _ _ _
      _ ≤ _ := by
        rw [Fin.succ_last]
        refine add_le_add (ih.trans_eq ?_) le_rfl
        simp only [Fin.succ_castSucc]

/-- The tuple point `(u₁ + i n, y_i)` at `i = 0` is `u` and at `i = K` is `v`, for an admissible
tuple and `v₁ = u₁ + K n`. -/
theorem tuplePoint_zero_last {M : Model m} {n K : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    {u v : Vertex m} (hv : v.1 = u.1 + K * n) {y : Fin (K + 1) → Fin m → ℤ}
    (hy : IsAdmissibleTuple M n K t u v y) :
    tuplePoint u n y 0 = u ∧ tuplePoint u n y (Fin.last K) = v := by
  obtain ⟨h0, hK, -⟩ := hy
  exact ⟨Prod.ext (by simp [tuplePoint]) h0, Prod.ext (by simp [tuplePoint, hv]) hK⟩

/-- **Lemma `lem:slabs` (2), lower bound** (by `T_P ≥ T` and the triangle inequality): for
`v₁ = u₁ + K n`, `T(u, v) ≤ F`. -/
theorem passageTime_le_slabMin (M : Model m) (ω : Config m) {n K : ℕ}
    (t : EuclideanSpace ℝ (Fin m)) {u v : Vertex m} (hv : v.1 = u.1 + K * n) :
    (passageTime ω u v : ℝ≥0∞) ≤ slabMin M ω n K t u v := by
  refine le_iInf₂ fun y hy => ?_
  obtain ⟨hP0, hPK⟩ := tuplePoint_zero_last hv hy
  calc (passageTime ω u v : ℝ≥0∞)
      = (passageTime ω (tuplePoint u n y 0) (tuplePoint u n y (Fin.last K)) : ℝ≥0∞) := by
        rw [hP0, hPK]
    _ ≤ ((∑ i : Fin K, passageTime ω (tuplePoint u n y i.castSucc)
          (tuplePoint u n y i.succ) : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.coe_le_coe.2 (passageTime_le_sum_fin ω _)
    _ = ∑ i : Fin K, (passageTime ω (tuplePoint u n y i.castSucc)
          (tuplePoint u n y i.succ) : ℝ≥0∞) := ENNReal.ofNNReal_finsetSum _ _
    _ ≤ tupleCost ω u n y :=
        Finset.sum_le_sum fun i _ => passageTime_le_slabTime ω _ _ _ _

/-- **Lemma `lem:slabs` (2), upper bound, along a walk.** For a walk `γ` from `u` to `v`,
monotone indices `k 0 ≤ ⋯ ≤ k K` and a tuple whose points are `γ_{k i}`: if each slab passage time
of the tuple exceeds the passage time of its piece by at most `c`, then
`tupleCost ≤ walkCost γ + K c`. -/
theorem tupleCost_le_walkCost {ω : Config m} {u v : Vertex m} (γ : (latticeGraph m).Walk u v)
    {n K : ℕ} {k : ℕ → ℕ} (hk : ∀ i < K, k i ≤ k (i + 1)) {y : Fin (K + 1) → Fin m → ℤ}
    {c : ℝ≥0∞}
    (hD : ∀ i : Fin K, slabTime ω (u.1 + (i : ℤ) * n) (u.1 + ((i : ℤ) + 1) * n)
      (tuplePoint u n y i.castSucc) (tuplePoint u n y i.succ) ≤
        passageTime ω (γ.getVert (k i)) (γ.getVert (k ((i : ℕ) + 1))) + c) :
    tupleCost ω u n y ≤ walkCost ω γ + K * c := by
  unfold tupleCost
  have hsum : ∑ i : Fin K, (passageTime ω (γ.getVert (k i)) (γ.getVert (k ((i : ℕ) + 1))) :
      ℝ≥0∞) ≤ walkCost ω γ := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (passageTime ω (γ.getVert (k i))
      (γ.getVert (k (i + 1))) : ℝ≥0∞)), ← ENNReal.ofNNReal_finsetSum]
    exact ENNReal.coe_le_coe.2 (sum_passageTime_getVert_le ω γ hk)
  calc ∑ i : Fin K, slabTime ω (u.1 + (i : ℤ) * n) (u.1 + ((i : ℤ) + 1) * n)
        (tuplePoint u n y i.castSucc) (tuplePoint u n y i.succ)
      ≤ ∑ i : Fin K, ((passageTime ω (γ.getVert (k i)) (γ.getVert (k ((i : ℕ) + 1))) :
          ℝ≥0∞) + c) := Finset.sum_le_sum fun i _ => hD i
    _ = ∑ i : Fin K, (passageTime ω (γ.getVert (k i)) (γ.getVert (k ((i : ℕ) + 1))) :
          ℝ≥0∞) + K * c := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ ≤ walkCost ω γ + K * c := add_le_add hsum le_rfl

end CurvatureVariance.Paper.Proofs.Geometry
