/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Induction.Exponential
public import IsotropicVariance.Paper.Contracts.Induction
public import IsotropicVariance.Paper.Contracts.Profiles
public import IsotropicVariance.Paper.Contracts.Gain
public import IsotropicVariance.Paper.Contracts.Classical
public import IsotropicVariance.Infra.TimeConstant.Limit
import Mathlib.Analysis.Complex.ExponentialBounds
public import IsotropicVariance.Paper.Proofs.Profiles.Scales

/-!
# Tools of the improvement, equation `eq:improvement`

Three elementary facts used by the proof of the improvement,
`IsotropicVariance.Paper.Proofs.Induction.improvementStatement_of_contracts`:
`isOs_abs_sub_of_parts` and `evariance_div_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

open IsotropicVariance.Paper.Proofs.Profiles (Q_pos)
namespace IsotropicVariance.Paper.Proofs.Induction

open Infra.TimeConstant

/-- **The last step of equation `eq:improvement`**: `|T − E T| ≤ O_1(θ/4)` and
`0 ≤ E T − N ≤ (θ/4) log 2` give `|T − N| ≤ O_1(θ/2)`, by the sum rule. -/
theorem isOs_abs_sub_of_parts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : AEMeasurable Y P) {N θ : ℝ} (hθ : 0 < θ)
    (h₁ : Cited.IsOs P 1 (θ / 4) (fun ω => |Y ω - ∫ ω', Y ω' ∂P|))
    (h₂ : 0 ≤ (∫ ω, Y ω ∂P) - N) (h₃ : (∫ ω, Y ω ∂P) - N ≤ θ / 4 * Real.log 2) :
    Cited.IsOs P 1 (θ / 2) (fun ω => |Y ω - N|) := by
  have hc : Cited.IsOs P 1 (θ / 4) (fun _ => (∫ ω, Y ω ∂P) - N) :=
    isOs_one_of_le aemeasurable_const (by positivity) (Eventually.of_forall fun _ => h₃)
  have hsum := isOs_one_add (by positivity) (by positivity) h₁ hc
  rw [show θ / 4 + θ / 4 = θ / 2 by ring] at hsum
  refine Cited.IsOs.mono hsum zero_le_one (by positivity)
    (continuous_abs.measurable.comp_aemeasurable (hY.sub_const N))
    (Eventually.of_forall fun ω => ?_)
  calc |Y ω - N| = |(Y ω - ∫ ω', Y ω' ∂P) + ((∫ ω', Y ω' ∂P) - N)| := by ring_nf
    _ ≤ |Y ω - ∫ ω', Y ω' ∂P| + |(∫ ω', Y ω' ∂P) - N| := abs_add_le _ _
    _ = |Y ω - ∫ ω', Y ω' ∂P| + ((∫ ω', Y ω' ∂P) - N) := by rw [abs_of_nonneg h₂]

/-- `Var(T/Q) = Var T / Q²`, bounded by the bound on `Var T`. -/
theorem evariance_div_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ}
    {q v : ℝ} (hq : 0 < q) (h : evariance Y P ≤ ENNReal.ofReal (v * q ^ 2)) :
    evariance (fun ω => Y ω / q) P ≤ ENNReal.ofReal v := by
  have heq : (fun ω => Y ω / q) = fun ω => q⁻¹ * Y ω := by
    funext ω
    rw [div_eq_inv_mul]
  rw [heq, evariance_mul]
  calc ENNReal.ofReal (q⁻¹ ^ 2) * evariance Y P
      ≤ ENNReal.ofReal (q⁻¹ ^ 2) * ENNReal.ofReal (v * q ^ 2) := by gcongr
    _ = ENNReal.ofReal (q⁻¹ ^ 2 * (v * q ^ 2)) := (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal v := by
        congr 1
        field_simp

end IsotropicVariance.Paper.Proofs.Induction
