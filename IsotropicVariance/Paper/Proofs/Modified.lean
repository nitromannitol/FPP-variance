/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Cited
import IsotropicVariance.Statements.Cited.VarianceMulLogLeOfEntropyLe
import IsotropicVariance.Infra.Entropy.Atoms

/-!
# Proposition `prop:BR`: the modified Poincaré inequality

Proposition `prop:BR` is [BR, Proposition 2.1], whose hypothesis is the
logarithmic Sobolev inequality `Ent[g²] ≤ (4/α) Var[g]` for the functions `g` of each coordinate.
The paper proves that inequality in one sentence after the proposition, which is
`Infra.Entropy.entropy_sq_le_four_div_mul_variance_of_atoms`. The proposition then follows from the
cited instance `Cited.variance_mul_log_le_of_entropy_le` of [BR, Proposition 2.1] with
`c = 4/α`.
-/

@[expose] public section

universe u v

namespace IsotropicVariance.Paper.Proofs.Modified

/-- **Proposition `prop:BR`** ([BR, Proposition 2.1]), with the logarithmic Sobolev inequality of
each coordinate from the sentence after the proposition. -/
theorem modifiedPoincareStatement_holds : Contracts.ModifiedPoincareStatement.{u, v} :=
  fun μ _ _ hα _ hatom _ hfm hf hA =>
    Cited.variance_mul_log_le_of_entropy_le μ (div_pos four_pos hα).le
      (fun i g => Infra.Entropy.entropy_sq_le_four_div_mul_variance_of_atoms (μ i) hα (hatom i) g)
      hfm hf hA

end IsotropicVariance.Paper.Proofs.Modified
