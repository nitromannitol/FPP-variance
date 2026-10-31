/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Localization.LocalSteps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The transverse radius of the curves

`tubeRadius n c' H`: the transverse radius `Y = √(n H₊/c')` of the proof of equation
`eq:localization`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Localization

variable {m : ℕ}

/-- The transverse radius `Y = √(n H₊/c')` of the curves. -/
noncomputable def tubeRadius (n c' H : ℝ) : ℝ := Real.sqrt (n * max H 0 / c')

lemma tubeRadius_nonneg (n c' H : ℝ) : 0 ≤ tubeRadius n c' H := Real.sqrt_nonneg _

end IsotropicVariance.Paper.Proofs.Localization
