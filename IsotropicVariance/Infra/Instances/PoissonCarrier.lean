/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonConfigurations

/-! # The standard Borel Poisson carrier in the paper's ambient space -/

@[expose] public section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace IsotropicVariance.Infra.Instances

/-- The canonical carrier is independent of intensity and of the original realization. -/
abbrev PoissonCarrier (m : ℕ) := PoissonConfiguration (Module.finrank ℝ (Pt m))

/-- Decode a canonical configuration in the paper's physical coordinates. -/
noncomputable def poissonCarrierDecode {m : ℕ} (c : PoissonCarrier m) : Measure (Pt m) :=
  (poissonConfigurationMeasure c).map (poissonCoordinates m).symm

lemma measurable_poissonCarrierDecode {m : ℕ} :
    Measurable (poissonCarrierDecode : PoissonCarrier m → Measure (Pt m)) :=
  (Measure.measurable_map _ (poissonCoordinates m).symm.continuous.measurable).comp
    measurable_poissonConfigurationMeasure

/-- Every decoded configuration has natural finite counts on bounded Borel sets. -/
theorem poissonCarrierDecode_counting {m : ℕ} (c : PoissonCarrier m) (B : Set (Pt m))
    (hB : MeasurableSet B) (hb : Bornology.IsBounded B) :
    ∃ n : ℕ, poissonCarrierDecode c B = n := by
  obtain ⟨n, hn⟩ := (poissonConfigurationMeasure_counting c).2
    ((poissonCoordinates m).symm ⁻¹' B)
    (hB.preimage (poissonCoordinates m).symm.continuous.measurable)
    ((poissonCoordinates m).symm.isometry.antilipschitzWith.isBounded_preimage hb)
  exact ⟨n, by rwa [poissonCarrierDecode, Measure.map_apply
    (poissonCoordinates m).symm.continuous.measurable hB]⟩

lemma poissonCarrierDecode_finite_ball {m : ℕ} (c : PoissonCarrier m) (n : ℕ) :
    poissonCarrierDecode c (Metric.closedBall 0 n) < ⊤ := by
  obtain ⟨k, hk⟩ := poissonCarrierDecode_counting c (Metric.closedBall 0 n)
    Metric.isClosed_closedBall.measurableSet Metric.isBounded_closedBall
  rw [hk]
  exact ENNReal.natCast_lt_top k

lemma poissonCarrierDecode_injective {m : ℕ} :
    Function.Injective (poissonCarrierDecode : PoissonCarrier m → Measure (Pt m)) := by
  intro c c' h
  apply poissonConfigurationMeasure_injective
  exact (poissonCoordinates m).symm.toHomeomorph.measurableEmbedding.map_injective h

/-- The physical decoder is a measurable embedding, proved via bounded count coding. -/
theorem measurableEmbedding_poissonCarrierDecode {m : ℕ} :
    MeasurableEmbedding (poissonCarrierDecode : PoissonCarrier m → Measure (Pt m)) := by
  let f : PoissonCarrier m → ℕ × Finset ℕ → ℝ≥0∞ := fun c => poissonCountCode (poissonCarrierDecode c)
  have hf : Measurable f := measurable_poissonCountCode.comp measurable_poissonCarrierDecode
  have hi : Function.Injective f := by
    intro c c' h
    apply poissonCarrierDecode_injective
    exact poissonCountCode_ext (poissonCarrierDecode_finite_ball c) h
  have he := hf.measurableEmbedding hi
  refine ⟨poissonCarrierDecode_injective, measurable_poissonCarrierDecode, fun A hA => ?_⟩
  have himage := he.measurableSet_image.mpr hA
  have heq : poissonCarrierDecode '' A = poissonCountCode ⁻¹' (f '' A) := by
    ext μ
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, hcode⟩
      exact ⟨c, hc, poissonCountCode_ext (poissonCarrierDecode_finite_ball c) hcode⟩
  rw [heq]
  exact measurable_poissonCountCode himage

end IsotropicVariance.Infra.Instances
