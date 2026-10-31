/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoiseProps.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Regional information modulo null events

The almost-sure saturation of a sub-sigma-algebra uses null events of the ambient probability.
This expresses precisely the union law required by `Paper.NoiseModel.union_ae`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace IsotropicVariance.Infra.WhiteNoiseProps

/-- Events equal almost everywhere to events of a given sigma-algebra. -/
@[instance_reducible]
def aeInfo {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (m : MeasurableSpace Ω) :
    MeasurableSpace Ω where
  MeasurableSet' A := ∃ B : Set Ω, MeasurableSet[m] B ∧ A =ᵐ[P] B
  measurableSet_empty := ⟨∅, MeasurableSet.empty, Filter.EventuallyEq.rfl⟩
  measurableSet_compl := by
    rintro A ⟨B, hB, hAB⟩
    exact ⟨Bᶜ, hB.compl, ae_eq_set_compl_compl.mpr hAB⟩
  measurableSet_iUnion := by
    intro A hA
    choose B hB hAB using hA
    refine ⟨⋃ n, B n, MeasurableSet.iUnion hB, ?_⟩
    filter_upwards [ae_all_iff.mpr hAB] with ω hω
    simp only [Set.mem_iUnion]
    exact propext (exists_congr (fun n => (hω n).to_iff))

/-- An event in the saturated information has a representative with zero symmetric difference. -/
theorem aeInfo_representative {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {m : MeasurableSpace Ω} {A : Set Ω} (hA : MeasurableSet[@aeInfo Ω mΩ P m] A) :
    ∃ B : Set Ω, MeasurableSet[m] B ∧ P (symmDiff A B) = 0 := by
  obtain ⟨B, hB, hAB⟩ := hA
  exact ⟨B, hB, measure_symmDiff_eq_zero_iff.mpr hAB⟩

/-- An almost-surely equal measurable representative is measurable for the saturated information. -/
theorem measurable_aeInfo_of_ae_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {m : MeasurableSpace Ω} {f g : Ω → ℝ} (hg : Measurable[m] g) (hfg : f =ᵐ[P] g) :
    Measurable[@aeInfo Ω mΩ P m] f := by
  intro A hA
  refine ⟨g ⁻¹' A, hg hA, ?_⟩
  filter_upwards [hfg] with ω hω
  simp only [Set.mem_preimage, hω]

/-- Limits in probability of functions measurable for a sub-sigma-algebra have measurable
representatives for that sigma-algebra, with equality almost everywhere under the ambient law. -/
theorem exists_measurable_of_tendstoInMeasure {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {m : MeasurableSpace Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Measurable[m] (f n)) (hlim : TendstoInMeasure P f atTop g) :
    ∃ g' : Ω → ℝ, Measurable[m] g' ∧ g =ᵐ[P] g' := by
  obtain ⟨ns, _hns, hseq⟩ := hlim.exists_seq_tendsto_ae
  refine ⟨fun ω => liminf (fun n => f (ns n) ω) atTop, Measurable.liminf (fun n => hf (ns n)), ?_⟩
  filter_upwards [hseq] with ω hω
  exact hω.liminf_eq.symm

end IsotropicVariance.Infra.WhiteNoiseProps
