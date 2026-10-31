/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.OsTools

/-! # Adding deterministic floors to the sub-Gaussian scale -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Cited Infra.Os
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A deterministic variable has a sub-Gaussian bound at the exact elementary scale. -/
lemma isOs_two_const {θ c : ℝ} (hθ : 0 < θ) (hc : c ≤ θ * Real.sqrt (Real.log 2)) :
    IsOs P 2 θ (fun _ => c) := by
  refine ⟨aemeasurable_const, ?_⟩
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmax : max c 0 / θ ≤ Real.sqrt (Real.log 2) := by
    rw [div_le_iff₀ hθ]
    exact max_le (hc.trans_eq (mul_comm _ _)) (by positivity)
  have hsq : (max c 0 / θ) ^ (2 : ℝ) ≤ Real.log 2 := by
    rw [Real.rpow_two]
    nlinarith [Real.sq_sqrt hl.le, div_nonneg (le_max_right c 0) hθ.le]
  have he : Real.exp ((max c 0 / θ) ^ (2 : ℝ)) ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hsq
  simp only [lintegral_const, measure_univ, mul_one]
  exact (ENNReal.ofReal_le_ofReal he).trans_eq (by norm_num)

/-- A deterministic nonnegative floor can be added with its exact sub-Gaussian scale. -/
lemma isOs_two_add_const {θ c : ℝ} {X : Ω → ℝ} (hX : IsOs P 2 θ X)
    (hθ : 0 < θ) (hc : 0 ≤ c) :
    IsOs P 2 (θ + (c + 1) / Real.sqrt (Real.log 2)) (fun ω => X ω + c) := by
  have hl : 0 < Real.sqrt (Real.log (2 : ℝ)) :=
    Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  refine Profiles.isOs_add_of_one_le (by norm_num) hX (isOs_two_const (by positivity) ?_) hθ
    (by positivity)
  rw [div_mul_cancel₀ _ hl.ne']
  linarith

end IsotropicVariance.Paper.Proofs.SlabComparison
