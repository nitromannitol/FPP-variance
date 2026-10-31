/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.Analytic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Tactic.FunProp

/-!
# Measurability of projected Borel sets and infima

A Borel subset of a product of standard Borel spaces has a universally measurable projection.
Consequently the infimum of a Borel cost over a Borel family of sections is null measurable,
and has a measurable version. Empty sections have infimum `⊤`; unbounded-below sections have
infimum `⊥`. No continuity of the cost or compactness of its sublevels is assumed. Polish
parameter spaces, in particular compact metrizable spaces with their Borel sigma algebra,
are special cases of the standard Borel parameter spaces used here.
-/

@[expose] public section

open MeasureTheory Set

namespace IsotropicVariance.Infra.Measurability

variable {K Ω : Type*} [MeasurableSpace K] [StandardBorelSpace K]
  [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The projection of a Borel subset of a product is measurable for the completed measure. -/
theorem nullMeasurableSet_projection (μ : Measure Ω) [SFinite μ]
    {B : Set (K × Ω)} (hB : MeasurableSet B) :
    NullMeasurableSet (Prod.snd '' B) μ := by
  let := upgradeStandardBorel Ω
  exact (hB.analyticSet_image measurable_snd).nullMeasurableSet μ

end IsotropicVariance.Infra.Measurability
