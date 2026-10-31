/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Gain
import CurvatureVariance.Paper.Proofs.Responses.RowGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Responses.IndexTubes

/-!
# Admissible tuples: finiteness, minimizers and retained pairs

Deterministic facts about the tuples (the chains of equation `eq:F`, with `K` slabs of width `n`):

* `finite_setOf_isAdmissibleTuple`: there are finitely many admissible tuples (each increment is
  bounded); `exists_isMinTuple`: a minimizing tuple exists as soon as an admissible one does.
* `isRetainedPair_tupleIndex`: for `N` large, every pair `(J_{i−1}, J_i)` of a chain is among the
  pairs `(j, k)` with `8w|k − j| ≤ n^{3/4+δ/100}` of Section `sec:gain`, off which `R_i` and `Y_i`
  vanish, since `w` is small against `n^{3/4+δ/100}`: for an admissible tuple,
  `8w|J_{i+1} − J_i| ≤ n^{3/4+δ/100}` as soon as `32√m (w + 1) ≤ n^{3/4+δ/100}` (from
  `Responses.tuple_index_increment_le`).
* `tupleIndex_zero`: `J_0 = 0` for tuples from the origin.
-/

@[expose] public section

open Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-! ### Finitely many admissible tuples -/

/-- The increments of an admissible tuple are bounded. -/
theorem norm_sub_le_of_isAdmissibleTuple {M : Model m} {n K : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {u v : Vertex m} {y : Fin (K + 1) → Fin m → ℤ}
    (hy : IsAdmissibleTuple M n K t u v y) (i : Fin K) :
    ‖y i.succ - y i.castSucc‖ ≤
      (n : ℝ) * ‖t‖ + (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 := by
  refine (Responses.Geometry.norm_index_le _).trans ?_
  have h := hy.2.2 i
  calc ‖transversePoint (y i.succ - y i.castSucc)‖
      ≤ ‖transversePoint (y i.succ - y i.castSucc) - (n : ℝ) • t‖ + ‖(n : ℝ) • t‖ :=
        norm_le_norm_sub_add _ _
    _ ≤ _ := by
        rw [norm_smul, Real.norm_natCast]
        linarith

/-- **There are finitely many admissible tuples.** -/
theorem finite_setOf_isAdmissibleTuple (M : Model m) (n K : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (u v : Vertex m) : {y : Fin (K + 1) → Fin m → ℤ | IsAdmissibleTuple M n K t u v y}.Finite := by
  set D : ℝ := (n : ℝ) * ‖t‖ + (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 with hD
  have hD0 : 0 ≤ D := by positivity
  have hind : ∀ y : Fin (K + 1) → Fin m → ℤ, IsAdmissibleTuple M n K t u v y →
      ∀ i : ℕ, ∀ hi : i < K + 1, ‖y ⟨i, hi⟩ - u.2‖ ≤ i * D := by
    intro y hy i
    induction i with
    | zero =>
      intro hi
      have h0 : y ⟨0, hi⟩ = u.2 := hy.1
      rw [h0, sub_self, norm_zero]
      simp
    | succ i ih =>
      intro hi
      have hi' : i < K := by omega
      have hstep := norm_sub_le_of_isAdmissibleTuple hy ⟨i, hi'⟩
      have hprev := ih (by omega)
      have heq1 : (⟨i, hi'⟩ : Fin K).succ = ⟨i + 1, hi⟩ := rfl
      have heq2 : (⟨i, hi'⟩ : Fin K).castSucc = ⟨i, by omega⟩ := rfl
      rw [heq1, heq2] at hstep
      calc ‖y ⟨i + 1, hi⟩ - u.2‖
          ≤ ‖y ⟨i + 1, hi⟩ - y ⟨i, by omega⟩‖ + ‖y ⟨i, by omega⟩ - u.2‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ D + i * D := add_le_add hstep hprev
        _ = ((i + 1 : ℕ) : ℝ) * D := by push_cast; ring
  refine (Set.Finite.pi (t := fun _ : Fin (K + 1) => Metric.closedBall u.2 (K * D))
    (fun _ => (isCompact_closedBall u.2 (K * D)).finite_of_discrete)).subset ?_
  intro y hy i _
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine (hind y hy i i.isLt).trans ?_
  have hiK : (i : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
  exact mul_le_mul_of_nonneg_right hiK hD0

/-- **A minimizing tuple exists** as soon as an admissible tuple does. -/
theorem exists_isMinTuple {M : Model m} {n K : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    {u v : Vertex m} (h : ∃ y, IsAdmissibleTuple M n K t u v y) (ω : Config m) :
    ∃ Y, IsMinTuple M ω n K t u v Y := by
  obtain ⟨Y, hY, hmin⟩ := Set.exists_min_image _ (fun y => tupleCost ω u n y)
    (finite_setOf_isAdmissibleTuple M n K t u v) h
  exact ⟨Y, hY, le_antisymm (le_iInf₂ fun y hy => hmin y hy) (iInf₂_le Y hY)⟩

/-- Without admissible tuples the minimum is infinite. -/
theorem slabMin_eq_top_of_forall_not {M : Model m} {n K : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    {u v : Vertex m} (h : ∀ y, ¬ IsAdmissibleTuple M n K t u v y) (ω : Config m) :
    slabMin M ω n K t u v = ⊤ := by
  unfold slabMin
  exact le_antisymm le_top (le_iInf₂ fun y hy => absurd hy (h y))

/-! ### Retained pairs -/

/-- **Adjacent cubes of an admissible tuple form retained pairs** (Section `sec:gain`): if
`32√m (w + 1) ≤ n^{3/4+δ/100}` and `w ≥ 1`, then `8w|J_{i+1} − J_i| ≤ n^{3/4+δ/100}` for every
admissible tuple and every `i`. From `Responses.tuple_index_increment_le`. -/
theorem isRetainedPair_tupleIndex {M : Model m} {n K w : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    {u v : Vertex m} {Y : Fin (K + 1) → Fin m → ℤ} (hY : IsAdmissibleTuple M n K t u v Y)
    (hw : 1 ≤ w)
    (hsmall : 32 * Real.sqrt m * ((w : ℝ) + 1) ≤ (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100))
    (i : Fin K) :
    IsRetainedPair M n w (tupleIndex n w t Y i.castSucc) (tupleIndex n w t Y i.succ) := by
  have h := Responses.tuple_index_increment_le hw hY hsmall i
  show 8 * (w : ℝ) * _ ≤ _
  linarith only [h]

end CurvatureVariance.Paper.Gain
