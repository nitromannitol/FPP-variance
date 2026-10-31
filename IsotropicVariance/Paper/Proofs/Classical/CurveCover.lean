/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Natural
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.Linarith

/-! # A linear-size unit cover of a rectifiable curve

Sampling the unit-speed representative at integer arc lengths covers the whole
curve with at most `length + 1` closed unit balls. This is the geometric input
for counting visited unit-cube neighborhoods.
-/

@[expose] public section
open Set MeasureTheory
namespace IsotropicVariance.Paper.Proofs.Classical

/-- A curve of length `L` is covered by at most `L+1` unit balls. -/
theorem exists_unit_cover_curve {E : Type*} [MetricSpace E] (γ : RectifiableCurve E) :
    ∃ (N : ℕ) (p : Fin N → E), (N : ℝ) ≤ γ.length.toReal + 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∃ j : Fin N, dist (γ.toFun t) (p j) ≤ 1 := by
  let L := γ.length.toReal
  let N := ⌊L⌋₊ + 1
  refine ⟨N, fun j => γ.natural (j : ℝ), ?_, ?_⟩
  · dsimp only [N]
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add_left (Nat.floor_le ENNReal.toReal_nonneg) 1
  · intro t ht
    let s := γ.cumulativeLength t
    have hs0 : 0 ≤ s := by
      have hh := γ.monotone_cumulativeLength ht.1
      rwa [γ.cumulativeLength_of_nonpos le_rfl] at hh
    have hsL : s ≤ L := by
      have hh := γ.monotone_cumulativeLength ht.2
      rwa [γ.cumulativeLength_of_one_le le_rfl] at hh
    let j : Fin N := ⟨⌊s⌋₊, Nat.lt_succ_of_le (Nat.floor_mono hsL)⟩
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    have hjs : (j : ℝ) ≤ s := Nat.floor_le hs0
    have hjL : (j : ℝ) ≤ L := hjs.trans hsL
    have hDist := γ.lipschitzOnWith_natural.dist_le_mul s ⟨hs0, hsL⟩ (j : ℝ) ⟨hj0, hjL⟩
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hjs)] at hDist
    have hFrac : s - (j : ℝ) ≤ 1 := by
      have hh := Nat.lt_floor_add_one s
      change s - (⌊s⌋₊ : ℝ) ≤ 1
      linarith only [hh]
    refine ⟨j, ?_⟩
    rw [← γ.natural_cumulativeLength ht]
    exact hDist.trans hFrac

end IsotropicVariance.Paper.Proofs.Classical
