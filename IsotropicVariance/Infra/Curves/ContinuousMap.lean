/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Congr
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Continuous-map presentation of rectifiable curves

The function presentation used for calculus agrees with the literal continuous-map carrier
on the unit interval. These conversions do not require any chosen values off the interval.
-/

@[expose] public section
open Set

namespace IsotropicVariance.RectifiableCurve
variable {E : Type*} [PseudoMetricSpace E]

/-- Restrict a rectifiable curve to a continuous map on the unit interval. -/
def toContinuousMap (γ : RectifiableCurve E) : C(unitInterval, E) :=
  ⟨fun t => γ.toFun t, (continuousOn_iff_continuous_domRestrict.mp γ.continuousOn)⟩

end IsotropicVariance.RectifiableCurve
