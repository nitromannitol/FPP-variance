/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Classical
public import IsotropicVariance.Paper.Proofs.Classical.AssemblyConstant
public import IsotropicVariance.Paper.Proofs.Classical.Mean

/-! # Lemma `lem:classical`: the classical concentration and mean bounds

In the paper's proof, both tails of the first bound come from [BLM03, Corollary 3] and
[BLM03, Theorem 7], and the second bound from the first as in [HN, Lemmas 4.1 and 4.2]. The cited
statement `Cited.hn_lemma4_2` gives the second bound for large `t`, and the Lean adds the other
`t ≥ 1`, which the paper leaves as standard.
-/

@[expose] public section
namespace IsotropicVariance.Paper.Proofs.Classical
universe u

/-- **Lemma `lem:classical`**: the exact classical-bounds contract, with both halves proved
outright. -/
theorem classicalBoundsStatement_holds : Contracts.ClassicalBoundsStatement.{u} := by
  intro m hm X hX
  exact exists_common_classical_constant X
    (meanBound_of_concentration hm X hX (classicalConcentration_holds X))

end IsotropicVariance.Paper.Proofs.Classical
