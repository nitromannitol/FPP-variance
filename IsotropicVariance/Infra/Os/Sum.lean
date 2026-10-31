/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.Power
public import IsotropicVariance.Infra.Os.Convex

/-!
# The constant in the sum rule

AKM Lemma A.4, p. 457. The convex shift gives a constant depending only on the exponent; convexity
without a shift gives constant one for `s ≥ 1`. The rule itself is proved for integrals in
`IsotropicVariance.Infra.Os.Integral`; finite sums are in `IsotropicVariance.Infra.Os.SumRule`.
-/

@[expose] public section

namespace IsotropicVariance.Infra.Os

/-- The constant in AKM A.4. For `s < 1`, this is the explicit choice
`σ^(-1/s)` with `σ = log 2 / (log 2 + (1-s)/s)` in its proof. -/
noncomputable def sumConstant (s : ℝ) : ℝ :=
  if 1 ≤ s then 1 else (1 + ((1 - s) / s) / Real.log 2) ^ (1 / s)

end IsotropicVariance.Infra.Os
