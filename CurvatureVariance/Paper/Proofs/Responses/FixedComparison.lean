/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Contracts.Responses
import CurvatureVariance.Paper.Proofs.Responses.UniformFourth
import CurvatureVariance.Paper.Proofs.Responses.Exceptional
import CurvatureVariance.Paper.Proofs.Responses.ComparisonAsymptotics
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed comparison, equation `eq:fixedcomparison`

Lemma `lem:slabs` (2) and fixed coordinate-path moments imply equation `eq:fixedcomparison`,
with no induction premise. Constants and thresholds are chosen from the common bounds and law
before the model.
We use the admissible polynomial choice `S = N^(δ/1000)` instead of `log N`: its good-event
error is still negligible compared with `Q_n`, while a high moment of the `O₂` indicator
absorbs the polynomial fourth-moment bound. A nonempty good event supplies a deterministic
admissible tuple, so no separate rounding construction is needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- A sandwich of extended passage times gives the corresponding real absolute difference. -/
theorem norm_target_difference_le_of_sandwich {M : Model m} {ω : Config m}
    {n K ℓ : ℕ} {y : Fin m → ℤ} {D : ℝ} (hD : 0 ≤ D)
    (hlo : (passageTime ω 0 ((ℓ : ℤ), y) : ℝ≥0∞) ≤
      slabMin M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y))
    (hhi : slabMin M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) ≤
      (passageTime ω 0 ((ℓ : ℤ), y) : ℝ≥0∞) + ENNReal.ofReal D) :
    ‖targetMin M ω n K ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)‖ ≤ D := by
  have hf := ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.ofReal_ne_top⟩) hhi
  have hl := ENNReal.toReal_mono hf hlo
  have hu := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.ofReal_ne_top⟩) hhi
  rw [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hD] at hu
  simp only [ENNReal.coe_toReal] at hl hu
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by dsimp only [targetMin, passageTimeReal]; linarith only [hl, hD],
    by dsimp only [targetMin, passageTimeReal]; linarith only [hu]⟩

end CurvatureVariance.Paper.Responses
