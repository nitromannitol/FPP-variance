/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CurvatureVariance.Infra.FPP.Model
import Mathlib.Tactic.FieldSimp

/-!
# Translation of the centered passage-time norms

The pointwise variance hypothesis of Lemma `lem:smallmean` applies to every translated pair with the
same displacement. All identities refer to the actual IID law and passage times.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

/-- An extended-variance bound gives exactly the corresponding centered second-moment norm. -/
theorem eLpNorm_centered_le_of_evariance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : AEMeasurable X P) {B : ℝ} (hB : 0 ≤ B)
    (hv : evariance X P ≤ ENNReal.ofReal (B ^ 2)) :
    eLpNorm (fun ω => X ω - ∫ ω', X ω' ∂P) 2 P ≤ ENNReal.ofReal B := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (hX.sub_const _).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  change (evariance X P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal B
  apply (ENNReal.rpow_le_rpow hv (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq
  rw [ENNReal.ofReal_pow hB, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

/-- The law of a translated passage time depends only on the displacement. -/
theorem identDistrib_passageTime_sub {m : ℕ} {M : Model m} (hM : M.Standing)
    (u v : Vertex m) :
    IdentDistrib (fun ω => passageTimeReal ω u v)
      (fun ω => passageTimeReal ω 0 (v - u)) M.P M.P := by
  let : IsProbabilityMeasure M.F := hM.probF
  have hh := (identDistrib_passageTime_add
    (IsIIDWeights.measurePreserving_translate hM.iid u) 0 (v - u)).comp
      measurable_coe_nnreal_real
  simpa only [zero_add, sub_add_cancel, Function.comp_def, passageTimeReal] using hh

/-- The mean of a translated pair is the mean at the same displacement from zero. -/
theorem integral_passageTime_sub {m : ℕ} {M : Model m} (hM : M.Standing)
    (u v : Vertex m) :
    (∫ ω, passageTimeReal ω u v ∂M.P) =
      ∫ ω, passageTimeReal ω 0 (v - u) ∂M.P :=
  (identDistrib_passageTime_sub hM u v).integral_eq

/-- Every finite moment about a fixed deterministic center is translation invariant. -/
theorem eLpNorm_passageTime_sub_const_eq {m : ℕ} {M : Model m} (hM : M.Standing)
    (u v : Vertex m) (c : ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun ω => passageTimeReal ω u v - c) p M.P =
      eLpNorm (fun ω => passageTimeReal ω 0 (v - u) - c) p M.P := by
  simpa only [Function.comp_def, id_eq] using
    ((identDistrib_passageTime_sub hM u v).comp (measurable_id.sub_const c)).eLpNorm_eq p

/-- Centering by the expectation also commutes with translation of both endpoints. -/
theorem eLpNorm_passageTime_centered_eq {m : ℕ} {M : Model m} (hM : M.Standing)
    (u v : Vertex m) (p : ℝ≥0∞) :
    eLpNorm (fun ω => passageTimeReal ω u v - ∫ ω', passageTimeReal ω' u v ∂M.P) p M.P =
      eLpNorm (fun ω => passageTimeReal ω 0 (v - u) -
        ∫ ω', passageTimeReal ω' 0 (v - u) ∂M.P) p M.P := by
  rw [integral_passageTime_sub hM u v]
  exact eLpNorm_passageTime_sub_const_eq hM u v _ p

end CurvatureVariance.Paper.Mean
