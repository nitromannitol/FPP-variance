/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonAction
public import IsotropicVariance.Infra.Instances.PoissonLawTransfer
public import IsotropicVariance.Infra.Poisson.Joint

/-! # The homogeneous Poisson law on the canonical configuration carrier -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace IsotropicVariance.Infra.Instances

/-- A process satisfying `Poisson.IsPoissonProcess` satisfies the literal finite-family predicate
`IsotropicVariance.IsPoissonProcess`. -/
lemma isPoissonProcess_of_infra {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {lam : ℝ≥0}
    {η : Ω → Measure (Poisson.E d)} {P : Measure Ω} (h : Poisson.IsPoissonProcess lam η P) :
    IsotropicVariance.IsPoissonProcess lam η P :=
  ⟨h.measurable, fun ω => (h.counting ω).2,
    fun k B hB hb hd => ⟨h.independent k B hB hb hd, fun i => h.count_law _ (hB i) (hb i)⟩⟩

/-- The explicit cube process has a canonical representative for every sample. -/
theorem exists_poissonCarrier_of_process (m : ℕ)
    (w : Poisson.ProcessSample (Module.finrank ℝ (Pt m))) :
    ∃ c : PoissonCarrier m, poissonCarrierDecode c =
      (Poisson.process w).map (poissonCoordinates m).symm := by
  classical
  choose c hc using fun z => exists_poissonFiniteCloud_of_tuple
    (fun i : Fin (w z).1 => (w z).2 i)
  refine ⟨c, ?_⟩
  unfold poissonCarrierDecode
  congr 1
  unfold poissonConfigurationMeasure Poisson.process
  congr 1
  funext z
  change (poissonFiniteCloudMeasure _ (c z)).map Subtype.val =
    (Poisson.cloud (w z)).map Subtype.val
  rw [hc z]
  rfl

/-- Remove all unused infinite mark tails by canonical re-encoding. -/
noncomputable def poissonProcessEncode (m : ℕ)
    (w : Poisson.ProcessSample (Module.finrank ℝ (Pt m))) : PoissonCarrier m :=
  Classical.choose (exists_poissonCarrier_of_process m w)

@[simp] lemma poissonCarrierDecode_processEncode (m : ℕ)
    (w : Poisson.ProcessSample (Module.finrank ℝ (Pt m))) :
    poissonCarrierDecode (poissonProcessEncode m w) =
      (Poisson.process w).map (poissonCoordinates m).symm :=
  Classical.choose_spec (exists_poissonCarrier_of_process m w)

lemma measurable_poissonProcessEncode (m : ℕ) : Measurable (poissonProcessEncode m) := by
  apply measurableEmbedding_poissonCarrierDecode.measurable_comp_iff.mp
  have heq : poissonCarrierDecode ∘ poissonProcessEncode m =
      fun w => (Poisson.process w).map (poissonCoordinates m).symm :=
    funext (poissonCarrierDecode_processEncode m)
  rw [heq]
  exact (Measure.measurable_map _ (poissonCoordinates m).symm.continuous.measurable).comp
    Poisson.measurable_process

/-- The Poisson probability on the standard Borel canonical carrier. -/
noncomputable def poissonCanonicalLaw (m : ℕ) (lam : ℝ≥0) : Measure (PoissonCarrier m) :=
  (Poisson.processLaw (Module.finrank ℝ (Pt m)) lam).map (poissonProcessEncode m)

instance (m : ℕ) (lam : ℝ≥0) : IsProbabilityMeasure (poissonCanonicalLaw m lam) := by
  unfold poissonCanonicalLaw
  infer_instance

/-- Canonical decoding has exactly the explicit process law. -/
lemma poissonCanonicalLaw_map_decode (m : ℕ) (lam : ℝ≥0) :
    (poissonCanonicalLaw m lam).map poissonCarrierDecode =
      (Poisson.processLaw (Module.finrank ℝ (Pt m)) lam).map
        (fun w => (Poisson.process w).map (poissonCoordinates m).symm) := by
  rw [poissonCanonicalLaw, Measure.map_map measurable_poissonCarrierDecode (measurable_poissonProcessEncode m)]
  congr 1
  exact funext (poissonCarrierDecode_processEncode m)

/-- The canonical decoder satisfies every field of the Poisson predicate. -/
theorem isPoissonProcess_poissonCarrierDecode (m : ℕ) (lam : ℝ≥0) :
    IsotropicVariance.IsPoissonProcess lam poissonCarrierDecode (poissonCanonicalLaw m lam) := by
  have hs := isPoissonProcess_map
    (isPoissonProcess_of_infra (Poisson.isPoissonProcess_process (Module.finrank ℝ (Pt m)) lam))
    (poissonCoordinates m).symm.measurePreserving
    (fun _ hb => (poissonCoordinates m).symm.isometry.antilipschitzWith.isBounded_preimage hb)
  exact isPoissonProcess_of_config_law hs measurable_poissonCarrierDecode poissonCarrierDecode_counting
    (poissonCanonicalLaw_map_decode m lam).symm

/-- The actual Poisson noise instance; all information, independence, union and action fields
are proved, and the sample space is the canonical standard Borel configuration carrier. -/
noncomputable def poissonNoiseModel (m : ℕ) (lam : ℝ≥0) : Paper.NoiseModel m :=
  poissonNoiseModelOfEmbedding measurableEmbedding_poissonCarrierDecode
    (isPoissonProcess_poissonCarrierDecode m lam) poissonCarrierAction poissonCarrierDecode_action

end IsotropicVariance.Infra.Instances
