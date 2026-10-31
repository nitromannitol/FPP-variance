/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.Basic
import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Block resampling changes only its own slab

The midpoint characterization makes the disjointness of slab edge sets explicit, including
transverse edges at faces (which belong to neither slab). This supplies the locality required by
the deterministic positive-response comparison behind equation `eq:blocksum`.
-/

@[expose] public section

open Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- A slab edge has its midpoint strictly between the two faces. -/
theorem edgeMid_fst_mem_Ioo {p q : ℤ} {e : Sym2 (Vertex m)} (he : e ∈ slabEdges p q) :
    (p : ℝ) < (edgeMid e).ofLp.1 ∧ (edgeMid e).ofLp.1 < q := by
  rcases he with ⟨x, (⟨rfl, hx, hx'⟩ | ⟨j, rfl, hx, hx'⟩)⟩
  · have hl : (p : ℝ) ≤ x.1 := by exact_mod_cast hx
    have hu : (x.1 : ℝ) + 1 ≤ q := by exact_mod_cast hx'
    change (p : ℝ) < (1 / 2 : ℝ) * ((x.1 : ℝ) + ((x + (1, 0)).1 : ℤ)) ∧
      (1 / 2 : ℝ) * ((x.1 : ℝ) + ((x + (1, 0)).1 : ℤ)) < q
    simp only [Prod.fst_add, Int.cast_add, Int.cast_one]
    constructor <;> linarith only [hl, hu]
  · have hl : (p : ℝ) < x.1 := by exact_mod_cast hx
    have hu : (x.1 : ℝ) < q := by exact_mod_cast hx'
    change (p : ℝ) < (1 / 2 : ℝ) * ((x.1 : ℝ) + ((x + (0, Pi.single j 1)).1 : ℤ)) ∧
      (1 / 2 : ℝ) * ((x.1 : ℝ) + ((x + (0, Pi.single j 1)).1 : ℤ)) < q
    simp only [Prod.fst_add, add_zero]
    constructor <;> linarith only [hl, hu]

/-- Slabs with disjoint longitudinal interiors have disjoint edge sets. -/
theorem disjoint_slabEdges {p q r s : ℤ} (hqr : q ≤ r) :
    Disjoint (slabEdges (m := m) p q) (slabEdges r s) := by
  refine Set.disjoint_left.mpr fun e he he' => ?_
  have h1 := (edgeMid_fst_mem_Ioo he).2
  have h2 := (edgeMid_fst_mem_Ioo he').1
  have hqr' : (q : ℝ) ≤ r := by exact_mod_cast hqr
  exact (lt_of_lt_of_le h1 hqr').not_gt h2

/-- Distinct members of a row of equal-width slabs own disjoint edges. -/
theorem pairwise_disjoint_slabEdges (u : ℤ) (n : ℕ) :
    Pairwise fun i j : ℕ => Disjoint
      (slabEdges (m := m) (u + (i : ℤ) * n) (u + ((i : ℤ) + 1) * n))
      (slabEdges (u + (j : ℤ) * n) (u + ((j : ℤ) + 1) * n)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · apply disjoint_slabEdges
    gcongr
    exact_mod_cast h
  · apply Disjoint.symm
    apply disjoint_slabEdges
    gcongr
    exact_mod_cast h

/-- Resampling a set disjoint from the allowed edges leaves a restricted distance unchanged. -/
theorem restrictedTime_resample_eq (ω ω' : Config m) (G E : Set (Sym2 (Vertex m)))
    (hGE : Disjoint G E) (u v : Vertex m) :
    restrictedTime (resample G ω ω') E u v = restrictedTime ω E u v := by
  classical
  apply restrictedTime_congr E u v
  intro e he
  have hnot : e.1 ∉ G := fun hG => Set.disjoint_left.mp hGE hG he
  simp only [resample, hnot, ite_false]

/-- Replacing a block of slab `i + 1` leaves every other slab distance unchanged. -/
theorem slabTime_resample_block_eq (ω ω' : Config m) (n w L : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (o g : Fin m → ℤ) {i j : ℕ} (hij : i ≠ j)
    (u v : Vertex m) :
    slabTime (resample (block n w L t (i + 1) o g) ω ω') ((j : ℤ) * n)
        (((j : ℤ) + 1) * n) u v =
      slabTime ω ((j : ℤ) * n) (((j : ℤ) + 1) * n) u v := by
  apply restrictedTime_resample_eq
  have hG : block n w L t (i + 1) o g ⊆ slabEdges ((i : ℤ) * n) (((i : ℤ) + 1) * n) := by
    intro e he
    have h := he.1
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h
  have hd : Disjoint
      (slabEdges (m := m) ((i : ℤ) * n) (((i : ℤ) + 1) * n))
      (slabEdges ((j : ℤ) * n) (((j : ℤ) + 1) * n)) := by
    simpa only [zero_add] using pairwise_disjoint_slabEdges (m := m) 0 n hij
  exact hd.mono_left hG

end CurvatureVariance.Paper.Responses
