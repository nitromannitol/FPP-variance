/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.FALocalize
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The number of fine pairs

An elementary ingredient of the finite approximation, equation `eq:labelprofile`, in the proof of
Lemma `lem:labels`: the number of fine cubes of the subcube of a block is at most `(L + 1)^m`, so
the number of pairs is at most `(L + 1)^{2m}` (`card_rowBox_le`, `card_finePairs_le`).
-/

@[expose] public section

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-- The subcube of a block has at most `(L + 1)^m` fine cubes. -/
theorem card_rowBox_le (L : ℕ) (o g : Fin m → ℤ) : (rowBox L o g).card ≤ (L + 1) ^ m := by
  unfold rowBox
  rw [Fintype.card_piFinset]
  calc ∏ k, (Finset.Icc ((L : ℤ) * g k + o k + ⌈Real.sqrt L⌉₊)
        ((L : ℤ) * g k + o k + L - ⌈Real.sqrt L⌉₊)).card
      ≤ ∏ _k : Fin m, (L + 1) := by
        refine Finset.prod_le_prod fun k _ => ?_
        rw [Int.card_Icc]
        have h0 : (0 : ℤ) ≤ (⌈Real.sqrt L⌉₊ : ℤ) := Int.natCast_nonneg _
        omega
    _ = (L + 1) ^ m := by simp

/-- The pairs of fine cubes of the subcube of a block number at most `(L + 1)^{2m}`. -/
theorem card_finePairs_le (L : ℕ) (o g : Fin m → ℤ) :
    ((finePairs L o g).card : ℝ) ≤ ((L : ℝ) + 1) ^ (2 * m) := by
  unfold finePairs
  rw [Finset.card_product]
  have h := card_rowBox_le L o g
  have h' : ((rowBox L o g).card : ℝ) ≤ ((L : ℝ) + 1) ^ m := by exact_mod_cast h
  push_cast
  rw [two_mul, pow_add]
  exact mul_le_mul h' h' (by positivity) (by positivity)

end CurvatureVariance.Paper.Gain
