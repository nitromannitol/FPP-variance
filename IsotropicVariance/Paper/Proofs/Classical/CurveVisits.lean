/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.CurveCover
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Counting visited neighborhoods from local overlap

A unit cover of the curve reduces counting all neighborhoods visited by it to
the deterministic maximum number of neighborhoods meeting any unit ball.
-/

@[expose] public section
open Set
open scoped Classical
namespace IsotropicVariance.Paper.Proofs.Classical

/-- Finite families with overlap at most `M` meet a curve in at most
`M * (length + 1)` neighborhoods. -/
theorem card_visited_le {E ι : Type*} [MetricSpace E] [DecidableEq ι]
    (γ : RectifiableCurve E) (J : Finset ι) (K : ι → Set E) (M : ℕ)
    (hOverlap : ∀ x : E, (J.filter fun i => ∃ y ∈ K i, dist y x ≤ 1).card ≤ M)
    (hVisit : ∀ i ∈ J, ∃ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ K i) :
    (J.card : ℝ) ≤ (M : ℝ) * (γ.length.toReal + 1) := by
  classical
  obtain ⟨N, p, hN, hCover⟩ := exists_unit_cover_curve γ
  let F := fun j : Fin N => J.filter fun i => ∃ y ∈ K i, dist y (p j) ≤ 1
  have hSub : J ⊆ Finset.univ.biUnion F := by
    intro i hi
    obtain ⟨t, ht, hKt⟩ := hVisit i hi
    obtain ⟨j, hj⟩ := hCover t ht
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hi, γ.toFun t, hKt, hj⟩⟩
  have hCard : J.card ≤ N * M := by
    calc
      _ ≤ (Finset.univ.biUnion F).card := Finset.card_le_card hSub
      _ ≤ ∑ j : Fin N, (F j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin N, M := Finset.sum_le_sum fun j _ => hOverlap (p j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hc : (J.card : ℝ) ≤ (N : ℝ) * M := by exact_mod_cast hCard
  exact hc.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg M))

end IsotropicVariance.Paper.Proofs.Classical
