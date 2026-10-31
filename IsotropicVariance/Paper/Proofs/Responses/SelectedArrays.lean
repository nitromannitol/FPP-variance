/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Arrays.Basic

/-!
# The path through selected rows

`pathPt_rows`: the path `pathPt` through the rows `J_1, …, J_K`, started at `J_0 = 0`, visits the
rows. It connects the rows of the proof of Lemma `lem:blocks` to Lemma `lem:polynomialarray`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

open Infra.Arrays

variable {m K : ℕ}

/-- The path `pathPt` through the rows `J_1, …, J_K`, started at `J_0 = 0`, passes through all
rows. -/
theorem pathPt_rows (J : Fin (K + 1) → Fin m → ℤ) (hJ : J 0 = 0) {i : ℕ} (hi : i ≤ K) :
    pathPt 0 (fun i : Fin K => J i.succ) i = J ⟨i, Nat.lt_succ_of_le hi⟩ := by
  cases i with
  | zero => simpa [pathPt] using hJ.symm
  | succ i =>
    have hi' : i < K := Nat.lt_of_succ_le hi
    simp only [pathPt, hi', dite_true]
    rfl

end IsotropicVariance.Paper.Proofs.Responses
