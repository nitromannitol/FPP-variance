/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Closing
public import CurvatureVariance.Paper.Contracts.Gain
import CurvatureVariance.Infra.Os.Moments
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds

/-!
# The closing: two elementary facts

`Q_pos` (`0 < Q` on a standing model) and `IsAbsOs.mono_scale` (monotonicity of the `O₁` bound in the
scale).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Closing

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

/-- `Q_s > 0` for `A ≥ 1` and `s > 0`. -/
theorem Q_pos {m : ℕ} (M : Model m) (K : ℕ) {A s : ℝ} (hA : 1 ≤ A) (hs : 0 < s) :
    0 < Q M K A s :=
  mul_pos (by linarith) (Real.rpow_pos_of_pos hs _)

/-- `|X| ≤ O_s(θ)` is weakened by increasing `θ`. -/
theorem IsAbsOs.mono_scale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {s θ η : ℝ}
    {X : Ω → ℝ} (h : IsAbsOs P s θ X) (hs : 0 ≤ s) (hθ : 0 < θ) (hθη : θ ≤ η) :
    IsAbsOs P s η X :=
  ⟨h.1, CurvatureVariance.IsOs.mono_scale h.2 hs hθ hθη⟩

end CurvatureVariance.Paper.Closing
