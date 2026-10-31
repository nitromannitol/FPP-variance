/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Cubes
public import CurvatureVariance.Paper.Proofs.Mean.MeanExcess
public import CurvatureVariance.Infra.Arrays.Basic
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Cube-index geometry for Lemma `lem:smallmean`

At the reference slope `t = y₀/s`, the rows in the proof of Lemma `lem:smallmean` have exact
integral offsets `i y₀`. The coordinate and norm estimates below are elementary cube arguments for
`rowCube`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

/-- A coordinate bound gives the Euclidean bound with constant `√m`. -/
theorem norm_le_sqrt_mul_of_coord_le {m : ℕ} {x : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (hx : ∀ j, |x j| ≤ r) : ‖x‖ ≤ Real.sqrt m * r := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [EuclideanSpace.norm_eq, Finset.univ_eq_empty, Finset.sum_empty,
      Real.sqrt_zero, Nat.cast_zero, zero_mul, le_refl]
  have hr : 0 ≤ r := (abs_nonneg _).trans (hx ⟨0, hm⟩)
  rw [EuclideanSpace.norm_eq]
  rw [show Real.sqrt m * r = Real.sqrt (m * r ^ 2) by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hr]]
  apply Real.sqrt_le_sqrt
  calc
    ∑ j, ‖x j‖ ^ 2 ≤ ∑ _j : Fin m, r ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hx j) 2
    _ = m * r ^ 2 := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]

/-- At an integral reference slope, row membership bounds the offset in `[0,w)` coordinatewise. -/
theorem rowCube_coord_bounds {m n w : ℕ} (hw : 0 < w)
    {y₀ : Fin m → ℤ} {t : EuclideanSpace ℝ (Fin m)}
    (hnt : (n : ℝ) • t = transversePoint y₀) {i : ℤ} {j : Fin m → ℤ} {u : Vertex m}
    (hu : u ∈ rowCube n w t i j) (c : Fin m) :
    0 ≤ (u.2 c : ℝ) - i * y₀ c - w * j c ∧
      (u.2 c : ℝ) - i * y₀ c - w * j c < w := by
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw
  have hnc : (n : ℝ) * t c = (y₀ c : ℝ) := by
    change ((n : ℝ) • t) c = transversePoint y₀ c
    rw [hnt]
  have hprod : (i : ℝ) * n * t c = ((i * y₀ c : ℤ) : ℝ) := by
    rw [Int.cast_mul, mul_assoc, hnc]
  have hf := congrFun hu.2 c
  change ⌊((u.2 c : ℝ) - ⌊(i : ℝ) * n * t c⌋) / w⌋ = j c at hf
  rw [hprod, Int.floor_intCast] at hf
  have hlow := Int.floor_le (((u.2 c : ℝ) - ((i * y₀ c : ℤ) : ℝ)) / w)
  have hhigh := Int.lt_floor_add_one (((u.2 c : ℝ) - ((i * y₀ c : ℤ) : ℝ)) / w)
  rw [hf, le_div_iff₀ hwpos] at hlow
  rw [hf, div_lt_iff₀ hwpos] at hhigh
  push_cast at hlow hhigh
  constructor <;> nlinarith only [hlow, hhigh]

/-- Consecutive row points have displacement `y₀ + w(k-j)` up to `√m w` in Euclidean norm. -/
theorem row_jump_norm_bounds {m n w : ℕ} (hw : 0 < w)
    {y₀ : Fin m → ℤ} {t : EuclideanSpace ℝ (Fin m)}
    (hnt : (n : ℝ) • t = transversePoint y₀) {i : ℤ} {j k : Fin m → ℤ}
    {u v : Vertex m} (hu : u ∈ rowCube n w t i j)
    (hv : v ∈ rowCube n w t (i + 1) k) :
    (w : ℝ) * ‖transversePoint (k - j)‖ - Real.sqrt m * w ≤
        ‖transversePoint (v.2 - u.2 - y₀)‖ ∧
      ‖transversePoint (v.2 - u.2 - y₀)‖ ≤
        (w : ℝ) * ‖transversePoint (k - j)‖ + Real.sqrt m * w := by
  let E := transversePoint (v.2 - u.2 - y₀) - (w : ℝ) • transversePoint (k - j)
  have hEc : ∀ c, |E c| ≤ w := by
    intro c
    have h1 := rowCube_coord_bounds hw hnt hu c
    have h2 := rowCube_coord_bounds hw hnt hv c
    push_cast at h2
    dsimp only [E]
    simp only [PiLp.sub_apply, PiLp.smul_apply, transversePoint_apply, Pi.sub_apply, smul_eq_mul]
    push_cast
    rw [abs_le]
    constructor <;> nlinarith only [h1.1, h1.2, h2.1, h2.2]
  have hE := norm_le_sqrt_mul_of_coord_le hEc
  have hwT : ‖(w : ℝ) • transversePoint (k - j)‖ = (w : ℝ) * ‖transversePoint (k - j)‖ := by
    rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  constructor
  · have heq : (w : ℝ) • transversePoint (k - j) = transversePoint (v.2 - u.2 - y₀) - E := by
      dsimp only [E]
      abel
    have hh := norm_sub_le (transversePoint (v.2 - u.2 - y₀)) E
    rw [← heq, hwT] at hh
    linarith only [hh, hE]
  · have heq : transversePoint (v.2 - u.2 - y₀) = (w : ℝ) • transversePoint (k - j) + E := by
      dsimp only [E]
      abel
    rw [heq]
    exact (norm_add_le _ _).trans (by rw [hwT]; linarith only [hE])

end CurvatureVariance.Paper.Mean
