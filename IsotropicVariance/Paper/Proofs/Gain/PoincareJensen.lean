/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.EfronStein.Conditional
public import IsotropicVariance.Infra.Entropy.Martingale
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Two norms in integrals

`eLpNorm_two_sq` and `eLpNorm_one_eq`: the `L²` and `L¹` norms of a function, written as integrals
in `[0, ∞]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Gain.Poincare

open Infra.EfronStein Infra.Entropy

theorem eLpNorm_two_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) :
    eLpNorm f 2 P ^ 2 = ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num) hf
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  simpa only [enorm_sq_eq_ofReal_sq] using h

theorem eLpNorm_one_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) :
    eLpNorm f 1 P = ∫⁻ ω, ENNReal.ofReal |f ω| ∂P := by
  rw [eLpNorm_one_eq_lintegral_enorm hf]
  exact lintegral_congr fun ω => Real.enorm_eq_ofReal_abs _

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
  {Λ : ι → Type*} [∀ i, Fintype (Λ i)] [∀ i, MeasurableSpace (Λ i)]
  [∀ i, MeasurableSingletonClass (Λ i)] {ℓ : ∀ i, X i → Λ i}

end IsotropicVariance.Paper.Proofs.Gain.Poincare
