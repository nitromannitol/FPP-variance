/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Cubes
public import CurvatureVariance.Infra.Os.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import CurvatureVariance.Infra.Os.Moments
import CurvatureVariance.Infra.FPP.Walks
import CurvatureVariance.Paper.Proofs.Responses.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Responses.SlabArrays

/-!
# Analytic lemmas for the proof of Lemma `lem:labels`

Generic estimates for the finite approximation, equation `eq:labelprofile`:

* `eLpNorm_le_ofReal_of_lintegral_le`: an `L^p` bound from a bound on the `p`-th moment;
* `lintegral_indicator_le_sqrt_mul`: Cauchy–Schwarz with an indicator
  `E 1_E f ≤ P(E)^{1/2} (E f²)^{1/2}` (Hölder in the localization step).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Moments -/

/-- An `L^p` bound (`p ≥ 1` an integer) from a bound on the `p`-th moment. -/
theorem eLpNorm_le_ofReal_of_lintegral_le {P : Measure Ω} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) {p : ℕ} (hp : 1 ≤ p) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂P ≤ ENNReal.ofReal (c ^ p)) :
    eLpNorm f p P ≤ ENNReal.ofReal c := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast (by omega : p ≠ 0))
    (ENNReal.natCast_ne_top p) hf, ENNReal.toReal_natCast]
  have heq : ∀ ω, ‖f ω‖ₑ ^ (p : ℝ) = ENNReal.ofReal (|f ω| ^ p) := by
    intro ω
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_natCast, ENNReal.ofReal_pow (abs_nonneg _)]
  simp_rw [heq]
  calc (∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂P) ^ (1 / (p : ℝ))
      ≤ ENNReal.ofReal (c ^ p) ^ (1 / (p : ℝ)) := ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal c := by
      rw [ENNReal.ofReal_pow hc, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-- **Cauchy–Schwarz with an indicator**: `∫ 1_E f ≤ P(E)^{1/2} (∫ f²)^{1/2}`. -/
theorem lintegral_indicator_le_sqrt_mul {P : Measure Ω} {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P)
    {E : Set Ω} (hE : MeasurableSet E) :
    ∫⁻ ω, E.indicator f ω ∂P ≤ P E ^ (1 / 2 : ℝ) * (∫⁻ ω, f ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
  have hind : E.indicator f = E.indicator (1 : Ω → ℝ≥0∞) * f := by
    funext ω
    by_cases h : ω ∈ E <;> simp [h]
  have hm : AEMeasurable (E.indicator (1 : Ω → ℝ≥0∞)) P :=
    (aemeasurable_const.indicator hE)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hm hf
  rw [hind]
  refine h.trans_eq ?_
  congr 2
  have hsq : ∀ ω, E.indicator (1 : Ω → ℝ≥0∞) ω ^ (2 : ℝ) = E.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ E <;> simp [hω]
  simp_rw [hsq]
  exact lintegral_indicator_one hE

/-! ### Measurability of the localization radius -/

variable {m : ℕ}

end CurvatureVariance.Paper.Gain
