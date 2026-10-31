/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Targets
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scale comparisons for equation `eq:fixedcomparison`

A polynomial good-event error with exponent below `1/4`, together with a decaying exceptional
error, is negligible compared with `Q_n`. All thresholds may depend on the fixed `K`.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- The power scale used in the slab event eventually dominates `log N`. -/
theorem eventually_log_le_rpow {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, Real.log N ≤ (N : ℝ) ^ a := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop ha).bound one_pos)] with N hN
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) a)] using hN)

end CurvatureVariance.Paper.Responses
