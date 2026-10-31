/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Proofs.Moments.ExpArray

/-!
# Lemma `lem:rowenergy`, equation `eq:rowenergy`

`expArrayStatement`: `ExpArrayStatement` from `ProfilesShortStatement` (Proposition `prop:profiles`
for `s ≤ N/2`), `SupportStatement` (equation `eq:support`) and `ScalesStatement` (equation
`eq:scales`, for the width margin), with the premise `ChainsExistStatement` of the implication, by
`expArray_of`.

* The clause `r₁ ≤ r₀/2` of `SupportStatement` is not used.
* The upper bound on `F` of `expArray_of` is the chain of the rounded points `(is, ist)`
  (`floorPt` of the module `Moments.ExpArraySlabs`), whose increments are within `√m` of `s(1,t)`
  (`norm_floorPt_sub_le`). This is the content of the second clause of `ChainsExistStatement`
  for that chain, proved directly, so the premise `ChainsExistStatement` is not used.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Moments

variable {m : ℕ}

/-- **Lemma `lem:rowenergy`** from Proposition
`prop:profiles` for `s ≤ N/2` and equations `eq:support` and `eq:scales`. -/
theorem expArrayStatement (hShort : Contracts.ProfilesShortStatement m)
    (hSupport : Contracts.SupportStatement m) (hScales : Contracts.ScalesStatement m)
    (_hChains : Contracts.ChainsExistStatement m) : Contracts.ExpArrayStatement m :=
  expArray_of hShort hSupport hScales

end CurvatureVariance.Paper.Moments
