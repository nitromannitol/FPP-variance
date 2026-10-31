/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.GridBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval

/-! # Uniform overlap of enlarged grid neighborhoods -/

@[expose] public section
open Set Metric
open scoped Classical
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.WhiteNoise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A neighborhood meeting a unit ball has its index in a fixed integer box
about the grid index of the center. -/
theorem gridIndex_bounds_of_near {z : Coord E → ℤ} {x y : E}
    (hy : y ∈ gridNeighborhood z) (hd : dist y x ≤ 1) (i : Coord E) :
    gridIndex x i - 4 ≤ z i ∧ z i ≤ gridIndex x i + 4 := by
  have hdist : |coord y i - coord x i| ≤ 1 := by
    have hh := (abs_coord_le (y - x) i).trans (by simpa only [dist_eq_norm] using hd)
    have hs : coord (y - x) i = coord y i - coord x i := by
      simpa only [coordCLM_apply, Pi.sub_apply] using congrFun ((coordCLM E).map_sub y x) i
    rwa [hs] at hh
  have hf : (gridIndex x i : ℝ) ≤ coord x i := Int.floor_le _
  have hf' : coord x i < (gridIndex x i : ℝ) + 1 := Int.lt_floor_add_one _
  have h := hy i
  obtain ⟨hd1, hd2⟩ := abs_le.mp hdist
  constructor
  · have hh : (gridIndex x i : ℝ) - 4 ≤ (z i : ℝ) := by linarith only [hf, h.2, hd1]
    exact_mod_cast hh
  · have hh : (z i : ℝ) < (gridIndex x i : ℝ) + 4 := by linarith only [hf', h.1, hd2]
    have hh' : z i < gridIndex x i + 4 := by exact_mod_cast hh
    exact hh'.le

/-- Uniform finite overlap, independent of the chosen finite family and point. -/
theorem card_gridNeighborhood_near_le (J : Finset (Coord E → ℤ)) (x : E) :
    (J.filter fun z => ∃ y ∈ gridNeighborhood z, dist y x ≤ 1).card ≤
      9 ^ Module.finrank ℝ E := by
  classical
  let F := Fintype.piFinset (fun i : Coord E => Finset.Icc (gridIndex x i - 4) (gridIndex x i + 4))
  have hSub : (J.filter fun z => ∃ y ∈ gridNeighborhood z, dist y x ≤ 1) ⊆ F := by
    intro z hz
    obtain ⟨_, y, hy, hd⟩ := Finset.mem_filter.mp hz
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_Icc.mpr (gridIndex_bounds_of_near hy hd i)
  refine (Finset.card_le_card hSub).trans_eq ?_
  simp only [F, Fintype.card_piFinset, Int.card_Icc]
  have hh (i : Coord E) : (gridIndex x i + 4 + 1 - (gridIndex x i - 4)).toNat = 9 := by omega
  simp only [hh, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Coord]

end IsotropicVariance.Paper.Proofs.Classical
