/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Resampling.Sigma
public import Mathlib.Probability.ConditionalExpectation

/-! # Independent information keeps its original law under conditional refresh -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.Resampling

/-- An event independent of the retained information has its original
probability under the conditional refresh kernel, almost surely. -/
theorem sigmaKernel_apply_eq_of_indep {Ω : Type*} [M : MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {G H : MeasurableSpace Ω} (hG : G ≤ M) (hH : H ≤ M) (hInd : Indep H G P)
    {B : Set Ω} (hB : MeasurableSet[H] B) :
    ∀ᵐ ω ∂P, sigmaKernel (mΩ := M) G P ω B = P B := by
  let _ : MeasurableSpace Ω := M
  have : IsMarkovKernel (sigmaKernel (mΩ := M) G P) := by
    unfold sigmaKernel
    infer_instance
  let F : Ω → ℝ := B.indicator (fun _ => 1)
  have hBm : @MeasurableSet Ω M B := hH _ hB
  have hFi : Integrable F P := (integrable_const (1 : ℝ)).indicator hBm
  have hFs : StronglyMeasurable[H] F := by
    let _ : MeasurableSpace Ω := H
    exact stronglyMeasurable_const.indicator hB
  have hCond := condExp_indep_eq hH hG hFs hInd
  have hKernel := sigmaKernel_condExp G P hG hFi
  filter_upwards [hCond, hKernel] with ω hω hκ
  have hh : (sigmaKernel (mΩ := M) G P ω).real B = P.real B := by
    have hEq := hκ.symm.trans hω
    change (∫ x, B.indicator (1 : Ω → ℝ) x ∂sigmaKernel (mΩ := M) G P ω) =
      ∫ x, B.indicator (1 : Ω → ℝ) x ∂P at hEq
    simpa only [integral_indicator_one hBm] using hEq
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hh

end IsotropicVariance.Paper.Proofs.Classical
