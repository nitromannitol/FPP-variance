/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.ModulusCore
import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.Linarith
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry

/-!
# Assembly of the continuity estimate at fixed parameters (Lemma `lem:modulus`)

For fixed `N`, `A`, `ℓ` and a pair of transverse cubes `I`, `I'`, the bound of equation `eq:modulus`
in `L^{8d}` (the proof of Lemma `lem:modulus`) from: the existence of geodesics; the bounds of
Proposition `prop:profiles` on the transverse boxes at longitudinal distance `L` from the endpoints
(`Y₁`, `Y₂`) and on `I × I'` (`X_i`); the variation `D` of the excess `μ − P_t·` under moves of one
endpoint; and the moment bound on the radius `R` of Lemma `lem:localization`. On `{R ≤ 1/g}` the
geodesics pass through the boxes, and the comparison through intermediate points applies; on
`{R > 1/g}`, Hölder's inequality with the crude bound.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Localization.Modulus

variable {m : ℕ}

/-- The `L^p` norm of a nonnegative constant under a probability measure. -/
theorem eLpNorm_const_of_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {c : ℝ} (hc : 0 ≤ c) {p : ℕ} (hp : 1 ≤ p) :
    eLpNorm (fun _ : Ω => c) p P = ENNReal.ofReal c := by
  rw [eLpNorm_const c (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hp))
    (IsProbabilityMeasure.ne_zero P), measure_univ, ENNReal.one_rpow, mul_one,
    Real.enorm_of_nonneg hc]

end CurvatureVariance.Paper.Localization.Modulus
