/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.SlabPaths
public import CurvatureVariance.Paper.Proofs.Geometry.TurningExcess

/-!
# Restriction to a slab: the lower bound

`passageTime_le_slabTime`: the slab passage time is at least the passage time, the lower bound of
Lemma `lem:slabs` (1). The surgery of the proof of Lemma `lem:slabs`, which
gives the upper bound, is `slabTime_le_of_interior_slabTime` (`Proofs.Geometry.SlabsFirstPart`).
-/

@[expose] public section

open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- The slab passage time is at least the passage time. -/
theorem passageTime_le_slabTime (ω : Config m) (p q : ℤ) (u v : Vertex m) :
    (passageTime ω u v : ℝ≥0∞) ≤ slabTime ω p q u v :=
  le_iInf₂ fun γ _ => ENNReal.coe_le_coe.2 (Infra.FPP.passageTime_le_walkCost ω γ)

end CurvatureVariance.Paper.Proofs.Geometry
