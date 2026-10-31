/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The triangle excess along a nearly optimal path

The first step of the proof of Lemma `lem:cone`: on `ConcentrationOn`, a path
with passage time at most `T(u,v) + S²` has every subpath within `S²` of the passage time between
its endpoints, so three of its vertices in order, at mutual distances at most `D ≥ S²`, almost
satisfy the triangle equality for `μ`: the excess `μ(y−x) + μ(z−y) − μ(z−x)` is at most
`(1 + 6A) S √D`.

The rest of the proof uses only this and unit steps, through the predicate `IsExcessPath` on the
sequence of points `i ↦ point (γ.getVert i)`; reversing the path is reversing and negating the
sequence (`IsExcessPath.reverse`).
-/

@[expose] public section

open InnerProductGeometry
open scoped NNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper

variable {m : ℕ}

/-- A sequence of points with unit steps whose triangle excess for the norm `μ`, at three indices
`i ≤ j ≤ k` with mutual distances at most `D ≥ S²`, is at most `b S √D`. -/
structure IsExcessPath (μ : Seminorm ℝ (Pt m)) (b S : ℝ) (f : ℕ → Pt m) : Prop where
  norm_succ_sub_le : ∀ i, ‖f (i + 1) - f i‖ ≤ 1
  excess_le : ∀ i j k, i ≤ j → j ≤ k → ∀ D, S ^ 2 ≤ D → ‖f j - f i‖ ≤ D → ‖f k - f j‖ ≤ D →
    ‖f k - f i‖ ≤ D → μ (f j - f i) + μ (f k - f j) - μ (f k - f i) ≤ b * S * Real.sqrt D

/-- Reversing and negating a sequence at a length `n` keeps the excess bound: the reversed path
from the final point. -/
theorem IsExcessPath.reverse {μ : Seminorm ℝ (Pt m)} {b S : ℝ} {f : ℕ → Pt m}
    (hf : IsExcessPath μ b S f) (n : ℕ) : IsExcessPath μ b S (fun i => -f (n - i)) where
  norm_succ_sub_le i := by
    simp only [neg_sub_neg]
    rcases lt_or_ge i n with h | h
    · have e : n - i = (n - (i + 1)) + 1 := by omega
      rw [e]
      exact hf.norm_succ_sub_le _
    · have e1 : n - i = 0 := by omega
      have e2 : n - (i + 1) = 0 := by omega
      rw [e1, e2, sub_self, norm_zero]
      exact zero_le_one
  excess_le i j k hij hjk D hD h1 h2 h3 := by
    simp only [neg_sub_neg] at h1 h2 h3 ⊢
    have := hf.excess_le (n - k) (n - j) (n - i) (by omega) (by omega) D hD h2 h1 h3
    linarith

/-! ### Walks -/

/-- Splitting a walk at an index, with the intermediate vertex given by an equation. -/
theorem exists_append_getVert_eq {V : Type*} {G : SimpleGraph V} {a b : V} (w : G.Walk a b)
    (k : ℕ) {x : V} (hx : w.getVert k = x) :
    ∃ (r : G.Walk a x) (s : G.Walk x b), w = r.append s ∧
      ∀ n, s.getVert n = w.getVert (k + n) := by
  subst hx
  exact ⟨w.take k, w.drop k, (SimpleGraph.Walk.append_take_drop_eq w k).symm,
    fun n => SimpleGraph.Walk.drop_getVert w k n⟩

/-- Three ordered indices split a walk into four consecutive pieces. -/
theorem exists_append_getVert_four {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    ∃ (q : G.Walk u (p.getVert i)) (r : G.Walk (p.getVert i) (p.getVert j))
      (s : G.Walk (p.getVert j) (p.getVert k)) (t : G.Walk (p.getVert k) v),
      p = q.append (r.append (s.append t)) := by
  obtain ⟨q, d1, h1, g1⟩ := exists_append_getVert_eq p i rfl
  obtain ⟨r, d2, h2, g2⟩ := exists_append_getVert_eq d1 (j - i) (x := p.getVert j) (by
    rw [g1]; congr 1; omega)
  obtain ⟨s, t, h3, -⟩ := exists_append_getVert_eq d2 (k - j) (x := p.getVert k) (by
    rw [g2, g1]; congr 1; omega)
  rw [h2, h3] at h1
  exact ⟨q, r, s, t, h1⟩

/-- **Subpaths of a nearly optimal path.** If the cost of `γ` is at most `T(u,v) + ζ`, then for
three of its vertices in order, `T(x,y) + T(y,z) ≤ T(x,z) + ζ`. -/
theorem passageTime_getVert_add_le {ω : Config m} {u v : Vertex m}
    {γ : (latticeGraph m).Walk u v} {ζ : ℝ} (hγ : (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + ζ)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    passageTimeReal ω (γ.getVert i) (γ.getVert j) +
        passageTimeReal ω (γ.getVert j) (γ.getVert k) ≤
      passageTimeReal ω (γ.getVert i) (γ.getVert k) + ζ := by
  obtain ⟨q, r, s, t, h⟩ := exists_append_getVert_four γ hij hjk
  have hc : (walkCost ω γ : ℝ) =
      walkCost ω q + walkCost ω r + walkCost ω s + walkCost ω t := by
    rw [congrArg (walkCost ω) h]
    simp only [Infra.FPP.walkCost_append, NNReal.coe_add]
    ring
  have e1 := NNReal.coe_le_coe.2 (Infra.FPP.passageTime_le_walkCost ω q)
  have e2 := NNReal.coe_le_coe.2 (Infra.FPP.passageTime_le_walkCost ω r)
  have e3 := NNReal.coe_le_coe.2 (Infra.FPP.passageTime_le_walkCost ω s)
  have e4 := NNReal.coe_le_coe.2 (Infra.FPP.passageTime_le_walkCost ω t)
  have t1 := NNReal.coe_le_coe.2 (Infra.FPP.passageTime_triangle ω u (γ.getVert i) v)
  have t2 := NNReal.coe_le_coe.2
    (Infra.FPP.passageTime_triangle ω (γ.getVert i) (γ.getVert k) v)
  simp only [NNReal.coe_add] at t1 t2
  unfold passageTimeReal at hγ ⊢
  linarith

/-- Consecutive vertices of a walk are at distance at most one. -/
theorem norm_point_getVert_succ_sub_le {u v : Vertex m} (γ : (latticeGraph m).Walk u v) (i : ℕ) :
    ‖point (γ.getVert (i + 1)) - point (γ.getVert i)‖ ≤ 1 := by
  rcases lt_or_ge i γ.length with h | h
  · rw [norm_sub_rev, Infra.FPP.norm_point_sub_point_of_adj (γ.adj_getVert_succ h)]
  · rw [γ.getVert_of_length_le h, γ.getVert_of_length_le (by omega), sub_self, norm_zero]
    exact zero_le_one

/-- **The triangle excess** (the proof of Lemma `lem:cone`). On `ConcentrationOn ω μ B A S`,
the vertices of a path in `B` with cost at most `T(u,v) + S²` form an excess path with constant
`1 + 6A`: at three ordered vertices with mutual distances at most `D ≥ S²`, the excess is at most
`S² + 3A (S √D + S²) ≤ (1 + 6A) S √D`. -/
theorem isExcessPath_of_concentrationOn {ω : Config m} {μ : Seminorm ℝ (Pt m)}
    {B : Set (Vertex m)} {A S : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S) (hconc : ConcentrationOn ω μ B A S)
    {u v : Vertex m} {γ : (latticeGraph m).Walk u v}
    (hγ : (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + S ^ 2) (hB : ∀ z ∈ γ.support, z ∈ B) :
    IsExcessPath μ (1 + 6 * A) S (fun i => point (γ.getVert i)) where
  norm_succ_sub_le i := norm_point_getVert_succ_sub_le γ i
  excess_le i j k hij hjk D hD h1 h2 h3 := by
    have hb : ∀ n, γ.getVert n ∈ B := fun n => hB _ (γ.getVert_mem_support n)
    have hD0 : 0 ≤ D := (sq_nonneg S).trans hD
    have hSD : S ≤ Real.sqrt D := Real.le_sqrt_of_sq_le hD
    have hconc' : ∀ x y : Vertex m, x ∈ B → y ∈ B → ‖point y - point x‖ ≤ D →
        |passageTimeReal ω x y - μ (point y - point x)| ≤ A * (S * Real.sqrt D + S ^ 2) := by
      intro x y hx hy hxy
      refine (hconc x hx y hy).trans (mul_le_mul_of_nonneg_left ?_ hA)
      gcongr
    have e1 := abs_le.1 (hconc' _ _ (hb i) (hb j) h1)
    have e2 := abs_le.1 (hconc' _ _ (hb j) (hb k) h2)
    have e3 := abs_le.1 (hconc' _ _ (hb i) (hb k) h3)
    have hT := passageTime_getVert_add_le hγ hij hjk
    have hS2 : S ^ 2 ≤ S * Real.sqrt D := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hSD hS
    have hAS : A * S ^ 2 ≤ A * (S * Real.sqrt D) := mul_le_mul_of_nonneg_left hS2 hA
    nlinarith

end CurvatureVariance.Paper.Proofs.Geometry
