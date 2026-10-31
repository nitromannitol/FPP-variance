/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Inputs
import CurvatureVariance.Infra.Entropy.ModifiedPoincareAtoms

/-!
# [AB26, Proposition 1.3]: the contract

In the continuum library the proof is at this level (`IsotropicVariance.Paper.Proofs.Modified`).
Here it is in `Infra`, as `Infra.Entropy.variance_mul_log_le_of_atoms`, from the cited
`CurvatureVariance.variance_mul_log_le_of_entropy_le` and the elementary entropy bound; this file
reads it as `ModifiedPoincareStatement`.
-/

@[expose] public section

universe u v

namespace CurvatureVariance.Paper.Proofs.Modified

/-- **[AB26, Proposition 1.3]**, with the logarithmic Sobolev inequality of each coordinate from
the sentence after it. -/
theorem modifiedPoincareStatement_holds : Contracts.ModifiedPoincareStatement.{u, v} :=
  fun μ _ _ hα hα1 hatom _ hfm hf hA =>
    Infra.Entropy.variance_mul_log_le_of_atoms μ hα hα1 hatom hfm hf hA

end CurvatureVariance.Paper.Proofs.Modified
