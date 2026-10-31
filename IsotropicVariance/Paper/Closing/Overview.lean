/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Closing.Main
import IsotropicVariance.Paper.Proofs.Localization.Main
import IsotropicVariance.Paper.Proofs.Profiles.TreeBound

/-!
# The display `eq:transverse` of the overview

`overviewTransverseStatement_holds`: display `eq:transverse`, for the cubes of Step 1 with `s = n`,
with no hypothesis. Lemma `lem:localization` has `|y| ≤ n/2`, and no proof of the paper uses the
range `n/2 < |y| ≤ n`, so this file is not on the path of the main theorems.
-/

public section

universe u

namespace IsotropicVariance.Paper.Closing

/-- **Display `eq:transverse` of the overview**: the instance `κ = 1` of the proof of Lemma
`lem:localization`, from the results that prove that lemma. -/
theorem overviewTransverseStatement_holds : Contracts.OverviewTransverseStatement.{u} :=
  Proofs.Localization.overviewTransverseStatement_of Proofs.Profiles.treeStatement_holds
    profilesStatement_holds parentStatement_holds

end IsotropicVariance.Paper.Closing
