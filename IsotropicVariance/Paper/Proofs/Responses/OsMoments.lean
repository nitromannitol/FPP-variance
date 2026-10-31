/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.MomentTools
public import IsotropicVariance.Infra.Os.Moments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fixed moments of profile errors

The conversion from the `O_1` profile estimate to every fixed response moment used for Lemma
`lem:blocks` and in its proof.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The dimension-free coefficient for the `p`-th norm of an `O_1(θ)` variable. -/
noncomputable def osMomentConst (p : ℝ) : ℝ :=
  (2 * (1 + ((Nat.ceil p).factorial : ℝ))) ^ (1 / p)

lemma osMomentConst_pos (p : ℝ) : 0 < osMomentConst p := by
  unfold osMomentConst
  positivity

/-- An `O_1` bound supplies every positive fixed moment of the nonnegative profile error. -/
theorem eLpNorm_ofReal_le_of_isOs {p θ : ℝ} (hp : 0 < p) (hθ : 0 < θ) {f : Ω → ℝ}
    (hf : Cited.IsOs P 1 θ f) (h0 : ∀ ω, 0 ≤ f ω) :
    eLpNorm (fun ω => ENNReal.ofReal (f ω)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (osMomentConst p * θ) := by
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (f ω)) P := hf.1.ennreal_ofReal
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
    hm.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  have h1 := Cited.IsOs.lintegral_pos_rpow_le hf zero_lt_one hθ hp.le
  simp only [div_one] at h1
  have h2 : (∫⁻ ω, ‖ENNReal.ofReal (f ω)‖ₑ ^ p ∂P) ≤
      ENNReal.ofReal (2 * (1 + ((Nat.ceil p).factorial : ℝ)) * θ ^ p) := by
    convert h1 using 1
    apply lintegral_congr
    intro ω
    rw [enorm_eq_self, ENNReal.ofReal_rpow_of_nonneg (h0 ω) hp.le, max_eq_left (h0 ω)]
  refine (ENNReal.rpow_le_rpow h2 (by positivity : 0 ≤ 1 / p)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hθ.le,
    mul_one_div_cancel hp.ne', Real.rpow_one]
  rfl

end IsotropicVariance.Paper.Proofs.Responses
