/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Entropy.Tensorization
public import Mathlib.Probability.Moments.MGFAnalytic
public import IsotropicVariance.Statements.Cited.VPlus
public import IsotropicVariance.Statements.Cited.VMinus
import Mathlib.Tactic.Ring

/-! # The BLM conditional positive and negative variance proxies

The proxies are the definitions `IsotropicVariance.Cited.vPlus` and
`IsotropicVariance.Cited.vMinus`, from Boucheron, Lugosi and Massart (2003), p. 1585. The
independent coordinate copy is integrated out; the proxies take values in `[0,∞]`. They are
exported into this namespace, so that `vPlus` and `vMinus` here are these definitions.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
namespace IsotropicVariance.Infra.Concentration

export IsotropicVariance.Cited (vPlus vMinus)

/-- Changing sign exchanges the two proxies. -/
theorem vPlus_neg {n : ℕ} {A : Type*} [MeasurableSpace A] (μ : Fin n → Measure A)
    (f : (Fin n → A) → ℝ) (x : Fin n → A) :
    vPlus μ (fun x => -f x) x = vMinus μ f x := by
  simp only [vPlus, vMinus, neg_sub_neg]

end IsotropicVariance.Infra.Concentration
