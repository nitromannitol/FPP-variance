/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.SupportAngular

/-!
# Lemma `lem:support` with `r₁ ∈ (0, r₀/2]`

`supportStatement`: the contract `SupportStatement`, Lemma `lem:support` and its proof. The two
equations are proved in `Proofs.Geometry.SupportQuadratic` and `Proofs.Geometry.SupportAngular`,
along the paper's proof. The bound `r₁ ≤ r₀/2` costs nothing: both equations weaken as `r₁`
decreases, and the paper's "Taking `r₁` small" includes it.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

/-- **Lemma `lem:support`**, with its proof. -/
theorem supportStatement (m : ℕ) : SupportStatement m := by
  intro bd hbd
  obtain ⟨c, C, r₁, hc, hC, hr₁, h⟩ := exists_support_bounds m bd hbd
  have hr : 0 < bd.rrem / 2 := half_pos hbd.rrem_pos
  refine ⟨c, C, min r₁ (bd.rrem / 2), hc, hC, lt_min hr₁ hr, min_le_right _ _,
    fun M hM hfit => ⟨fun t k ht hk p hp => ?_, fun t ht p hp z hz => ?_⟩⟩
  · exact (h M hM hfit).1 t k (ht.trans (min_le_left _ _)) (hk.trans (min_le_left _ _)) p hp
  · exact (h M hM hfit).2 t (ht.trans (min_le_left _ _)) p hp z hz

end CurvatureVariance.Paper.Proofs.Geometry
