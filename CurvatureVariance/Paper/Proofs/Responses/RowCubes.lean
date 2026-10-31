/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Targets
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The row cubes as transverse cubes

A half-open cube of integer side `w ≥ 1` has exactly the same lattice points as the closed cube
of side `w − 1`, centered halfway between its extreme lattice coordinates. This connects the
actual rows of Section `sec:gain` to the cube-pair localization contracts of Section
`sec:localization`.
-/

@[expose] public section

open Set

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- The Euclidean center of the lattice points of a row cube. -/
noncomputable def rowCenter (n w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ)
    (j : Fin m → ℤ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun k => (⌊(i : ℝ) * n * t k⌋ : ℝ) + (w : ℝ) * j k + ((w : ℝ) - 1) / 2

/-- Integer floor division describes the lattice interval of one row coordinate. -/
theorem floor_row_coord_iff {w : ℕ} (hw : 1 ≤ w) (a z j : ℤ) :
    ⌊((z : ℝ) - a) / w⌋ = j ↔
      |(z : ℝ) - ((a : ℝ) + (w : ℝ) * j + ((w : ℝ) - 1) / 2)| ≤ ((w : ℝ) - 1) / 2 := by
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hw)
  rw [Int.floor_eq_iff, abs_le]
  constructor
  · rintro ⟨hl, hu⟩
    have hl' := (le_div_iff₀ hwpos).mp hl
    have hu' := (div_lt_iff₀ hwpos).mp hu
    have hint : z - a < (j + 1) * (w : ℤ) := by exact_mod_cast hu'
    rw [add_mul, one_mul] at hint
    have hu'' : (z : ℝ) - a ≤ (j : ℝ) * w + w - 1 := by
      have h := (show z - a ≤ j * (w : ℤ) + w - 1 by omega)
      exact_mod_cast h
    constructor <;> linarith only [hl', hu'']
  · rintro ⟨hl, hu⟩
    constructor
    · apply (le_div_iff₀ hwpos).mpr
      linarith only [hl]
    · apply (div_lt_iff₀ hwpos).mpr
      linarith only [hu]

/-- The row cube is exactly a closed transverse cube of side `w − 1`. -/
theorem rowCube_eq_transverseCube (n : ℕ) {w : ℕ} (hw : 1 ≤ w)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (j : Fin m → ℤ) :
    rowCube n w t i j = transverseCube (i * n) (rowCenter n w t i j) ((w : ℝ) - 1) := by
  ext x
  constructor
  · rintro ⟨hx, hj⟩
    refine ⟨hx, fun k => ?_⟩
    have hk := congrFun hj k
    exact (floor_row_coord_iff hw ⌊(i : ℝ) * n * t k⌋ (x.2 k) (j k)).mp hk
  · rintro ⟨hx, hj⟩
    refine ⟨hx, funext fun k => ?_⟩
    exact (floor_row_coord_iff hw ⌊(i : ℝ) * n * t k⌋ (x.2 k) (j k)).mpr (hj k)

/-- The actual slope of the two row-cube centers. -/
noncomputable def rowPairSlope (n w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ)
    (j k : Fin m → ℤ) : EuclideanSpace ℝ (Fin m) :=
  (n : ℝ)⁻¹ • (rowCenter n w t (i + 1) k - rowCenter n w t i j)

/-- Two consecutive row cubes form a cube pair at their center slope. -/
theorem isCubePair_rows {M : Model m} {K n w : ℕ} {A b : ℝ} (hn : 1 ≤ n) (hw : 1 ≤ w)
    (hwidth : (w : ℝ) - 1 ≤ b * W M K A n) (t : EuclideanSpace ℝ (Fin m))
    (i : ℤ) (j k : Fin m → ℤ) :
    IsCubePair M K A n b (rowPairSlope n w t i j k) (rowCube n w t i j)
      (rowCube n w t (i + 1) k) := by
  refine ⟨i * n, rowCenter n w t i j, rowCenter n w t (i + 1) k,
    (w : ℝ) - 1, (w : ℝ) - 1, rowCube_eq_transverseCube n hw t i j, ?_,
    by
      have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
      linarith only [hw'], hwidth,
    by
      have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
      linarith only [hw'], hwidth, ?_⟩
  · have heq : (i + 1) * (n : ℤ) = i * n + n := by ring
    rw [rowCube_eq_transverseCube n hw t (i + 1) k, heq]
  · have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
    rw [rowPairSlope, smul_smul, mul_inv_cancel₀ hnne, one_smul, sub_self, norm_zero]
    positivity

end CurvatureVariance.Paper.Responses
