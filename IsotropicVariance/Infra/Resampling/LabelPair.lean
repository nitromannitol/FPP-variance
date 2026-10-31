/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Resampling a standard Borel variable within its label

The pair law mixes two independent draws from the conditional distribution over
one common label. Its marginals are the original law, and it is invariant under
swapping the draws. This module concerns one group only.
-/

@[expose] public section

namespace IsotropicVariance.Infra.Resampling

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

variable {E Λ : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
  [MeasurableSpace Λ] (μ : Measure E) [IsProbabilityMeasure μ] (π : E → Λ)

/-- The conditional group law at a label. -/
noncomputable def labelKernel : Kernel Λ E := condDistrib id π μ

/-- Joint law of the old and new group, sampled independently given one label. -/
noncomputable def labelPairLaw : Measure (E × E) :=
  (labelKernel μ π ×ₖ labelKernel μ π) ∘ₘ (μ.map π)

instance : IsMarkovKernel (labelKernel μ π) := by
  unfold labelKernel
  infer_instance

/-- The old and new groups form an exchangeable pair. -/
theorem labelPairLaw_map_swap :
    (labelPairLaw μ π).map Prod.swap = labelPairLaw μ π := by
  rw [labelPairLaw, Measure.map_comp _ _ measurable_swap, Kernel.map_prod_swap]

end IsotropicVariance.Infra.Resampling
