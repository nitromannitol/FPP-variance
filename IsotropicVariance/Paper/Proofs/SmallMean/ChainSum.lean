/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry
public import IsotropicVariance.Infra.Arrays.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The square of the norm of an integer vector
-/

@[expose] public section

open Finset
open IsotropicVariance.Infra.Slab

namespace IsotropicVariance.Paper.Proofs.SmallMean

variable {m : ℕ}

lemma zNorm_sq (J : Fin m → ℤ) : zNorm J ^ 2 = ∑ l, ((J l : ℤ) : ℝ) ^ 2 := by
  unfold zNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun l _ => sq_nonneg _)

end IsotropicVariance.Paper.Proofs.SmallMean
