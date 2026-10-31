/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoiseProps.Union
public import IsotropicVariance.Infra.WhiteNoiseProps.Motion
public import IsotropicVariance.Paper.Defs.Model

/-!
# White-noise information adapters for the paper interface

The paper definitions and the white-noise infrastructure use the same white-noise predicate
`IsotropicVariance.IsWhiteNoise`. These adapters restate the white-noise properties with
`Paper.Noise.info` and the null-boundary hypothesis order of the paper interface. They do not
assume or construct a `NoiseModel` action.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal Distributions

namespace IsotropicVariance.Infra.WhiteNoiseProps

/-- The paper and infrastructure white-noise predicates are the same predicate
`IsotropicVariance.IsWhiteNoise`. -/
theorem paper_isWhiteNoise_iff {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [MeasurableSpace Ω] (W : Ω → IsotropicVariance.WhiteNoiseConfig E)
    (P : Measure Ω) : IsotropicVariance.IsWhiteNoise W P ↔ IsotropicVariance.IsWhiteNoise W P := Iff.rfl

/-- Pulling back paper configuration information gives the regional sample information. -/
theorem paper_info_comap_eq {m : ℕ} {Ω : Type*}
    (W : Ω → IsotropicVariance.WhiteNoiseConfig (IsotropicVariance.Pt m))
    (S : Set (IsotropicVariance.Pt m)) :
    (Paper.Noise.info Paper.Noise.white S).comap W = info W S := by
  simpa only [Paper.Noise.info] using (info_eq_comap W S).symm

/-- The white-noise proof supplies the independence field of the setting, with null boundaries
before pairwise disjoint interiors, using the paper's information sigma-algebras. -/
theorem paper_iIndep_info {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {W : Ω → IsotropicVariance.WhiteNoiseConfig (IsotropicVariance.Pt m)} {P : Measure Ω}
    (h : IsotropicVariance.IsWhiteNoise W P) (ι : Type) [Countable ι]
    (S : ι → Set (IsotropicVariance.Pt m)) (_hB : ∀ i, MeasurableSet (S i))
    (_hb : ∀ i, volume (frontier (S i)) = 0)
    (hd : Pairwise (fun i j => Disjoint (interior (S i)) (interior (S j)))) :
    iIndep (fun i => (Paper.Noise.info Paper.Noise.white (S i)).comap W) P := by
  simp only [paper_info_comap_eq]
  exact iIndep_info ((paper_isWhiteNoise_iff W P).mp h) S hd

/-- The white-noise union law in the exact paper-information form used by `NoiseModel.union_ae`. -/
theorem paper_union_ae {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {W : Ω → IsotropicVariance.WhiteNoiseConfig (IsotropicVariance.Pt m)} {P : Measure Ω}
    (h : IsotropicVariance.IsWhiteNoise W P) (S : ℕ → Set (IsotropicVariance.Pt m))
    (_hB : ∀ i, MeasurableSet (S i)) (hb : ∀ i, volume (frontier (S i)) = 0)
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (A : Set Ω)
    (hA : MeasurableSet[(Paper.Noise.info Paper.Noise.white (⋃ i, S i)).comap W] A) :
    ∃ B : Set Ω, MeasurableSet[⨆ i, (Paper.Noise.info Paper.Noise.white (S i)).comap W] B ∧
      P (symmDiff A B) = 0 := by
  have hA' : MeasurableSet[info W (⋃ i, S i)] A :=
    Eq.mp (congrArg (fun mΩ : MeasurableSpace Ω => MeasurableSet[mΩ] A)
      (paper_info_comap_eq W (⋃ i, S i))) hA
  obtain ⟨B, hB, hnull⟩ := union_ae ((paper_isWhiteNoise_iff W P).mp h) S hb hd A hA'
  have hsup : (⨆ i, (Paper.Noise.info Paper.Noise.white (S i)).comap W) =
      ⨆ i, info W (S i) := iSup_congr fun i => paper_info_comap_eq W (S i)
  exact ⟨B, Eq.mpr (congrArg (fun mΩ : MeasurableSpace Ω => MeasurableSet[mΩ] B) hsup) hB, hnull⟩

end IsotropicVariance.Infra.WhiteNoiseProps
