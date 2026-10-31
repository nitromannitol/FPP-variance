/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.Projection
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Tactic.FunProp

/-!
# Measurability of projected Borel sets and infima

A Borel subset of a product of standard Borel spaces has a universally measurable projection.
Consequently the infimum of a Borel cost over a Borel family of sections is null measurable,
and has a measurable version. Empty sections have infimum `⊤`. No continuity of the cost or
compactness of its sublevels is assumed. Polish parameter spaces, in particular compact
metrizable spaces with their Borel sigma algebra, are special cases of the standard Borel
parameter spaces used here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace IsotropicVariance.Infra.Measurability

variable {K Ω : Type*} [MeasurableSpace K] [StandardBorelSpace K]
  [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Infimum of the cost over the section of a Borel family, in the complete ordered codomain. -/
noncomputable def sectionInfENNReal (B : Set (K × Ω)) (c : K × Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ⨅ k : K, ⨅ (_ : (k, ω) ∈ B), c (k, ω)

/-- A section infimum is null measurable, with no continuity or compactness hypothesis. -/
theorem nullMeasurable_sectionInfENNReal (μ : Measure Ω) [SFinite μ]
    {B : Set (K × Ω)} (hB : MeasurableSet B) {c : K × Ω → ℝ≥0∞} (hc : Measurable c) :
    NullMeasurable (sectionInfENNReal B c) μ := by
  have hlevel (a : ℝ≥0∞) :
      NullMeasurableSet (sectionInfENNReal B c ⁻¹' Iio a) μ := by
    have heq : sectionInfENNReal B c ⁻¹' Iio a =
        Prod.snd '' (B ∩ {p | c p < a}) := by
      ext ω
      simp only [mem_preimage, mem_Iio, sectionInfENNReal, iInf_lt_iff]
      constructor
      · rintro ⟨k, hk, hcost⟩
        exact ⟨(k, ω), ⟨hk, hcost⟩, rfl⟩
      · rintro ⟨⟨k, ω'⟩, ⟨hk, hcost⟩, rfl⟩
        exact ⟨k, hk, hcost⟩
    rw [heq]
    exact nullMeasurableSet_projection μ (hB.inter
      (measurableSet_lt hc measurable_const))
  have h : @Measurable (NullMeasurableSpace Ω μ) ℝ≥0∞ inferInstance inferInstance
      (sectionInfENNReal B c) := measurable_of_Iio hlevel
  exact fun _ hs => h hs

end IsotropicVariance.Infra.Measurability
