/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.SelectedArrays
public import IsotropicVariance.Paper.Proofs.Responses.GaussianSum
import IsotropicVariance.Paper.Proofs.Profiles.GridGeometry
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Linarith
import IsotropicVariance.Paper.Proofs.SmallMean.ChainSum

/-!
# The norm of an integer vector

`zNorm_eq_zero_or_one_le`, `sqNorm_cast_eq_zNorm_sq`: two facts on the norm of an integer vector,
used by the array estimates in the proof of Lemma `lem:blocks`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

lemma zNorm_eq_zero_or_one_le {m : ℕ} (z : Fin m → ℤ) : zNorm z = 0 ∨ 1 ≤ zNorm z := by
  classical
  by_cases hz : z = 0
  · left
    simp [hz, zNorm]
  · right
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      apply hz
      push Not at h
      exact funext h
    have h1 : (1 : ℝ) ≤ |(z i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
    rw [← norm_transverseIntegerPoint]
    exact h1.trans (PiLp.norm_apply_le (transverseIntegerPoint z) i)

lemma sqNorm_cast_eq_zNorm_sq {m : ℕ} (z : Fin m → ℤ) :
    (Infra.Arrays.sqNorm z : ℝ) = zNorm z ^ 2 := by
  rw [SmallMean.zNorm_sq]
  simp [Infra.Arrays.sqNorm]

end IsotropicVariance.Paper.Proofs.Responses
