/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonNullBoundary

/-! # Transporting the Poisson information interface to a canonical configuration carrier

This module assembles the interface from a measurable configuration embedding and an exact
pushforward action. The canonical carrier construction supplies those deterministic data.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace IsotropicVariance.Infra.Instances

variable {m : ℕ} {C : Type*} [MeasurableSpace C] [StandardBorelSpace C]
    {Q : Measure C} [IsProbabilityMeasure Q] {lam : ℝ≥0}
    {decode : C → Measure (Pt m)}

omit [StandardBorelSpace C] in
/-- An exact pushforward action is measurable because the decoder is a measurable embedding. -/
lemma measurable_poissonAction (he : MeasurableEmbedding decode)
    (act : (Pt m ≃ᵃⁱ[ℝ] Pt m) → C → C)
    (hact : ∀ g c, decode (act g c) = (decode c).map g) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) :
    Measurable (act g) := by
  apply he.measurable_comp_iff.mp
  have heq : decode ∘ act g = (fun μ : Measure (Pt m) => μ.map g) ∘ decode :=
    funext (hact g)
  rw [heq]
  exact (Measure.measurable_map _ g.continuous.measurable).comp he.measurable

omit [StandardBorelSpace C] [IsProbabilityMeasure Q] in
/-- The Poisson law on a canonical carrier is invariant under its exact pushforward action. -/
lemma measurePreserving_poissonAction (he : MeasurableEmbedding decode)
    (hP : IsotropicVariance.IsPoissonProcess lam decode Q)
    (act : (Pt m ≃ᵃⁱ[ℝ] Pt m) → C → C)
    (hact : ∀ g c, decode (act g c) = (decode c).map g) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) :
    MeasurePreserving (act g) Q Q := by
  have hm := measurable_poissonAction he act hact g
  refine ⟨hm, ?_⟩
  apply he.map_injective
  rw [Measure.map_map he.measurable hm]
  have heq : decode ∘ act g = fun c => (decode c).map g := funext (hact g)
  rw [heq]
  exact isPoissonProcess_rigidMotion_law hP g

omit [MeasurableSpace C] [StandardBorelSpace C] in
/-- Exact pushforward pulls regional information back to the original region. -/
lemma poisson_comap_info_action
    (act : (Pt m ≃ᵃⁱ[ℝ] Pt m) → C → C)
    (hact : ∀ g c, decode (act g c) = (decode c).map g)
    (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (S : Set (Pt m)) :
    ((Paper.Noise.info (Paper.Noise.poisson lam) (g '' S)).comap decode).comap (act g) =
      (Paper.Noise.info (Paper.Noise.poisson lam) S).comap decode := by
  rw [MeasurableSpace.comap_comp]
  have heq : decode ∘ act g = (fun μ : Measure (Pt m) => μ.map g) ∘ decode := funext (hact g)
  rw [heq, ← MeasurableSpace.comap_comp, poisson_info_comap_motion]

/-- The full noise interface on any canonical carrier supplied with its exact decoded action. -/
noncomputable def poissonNoiseModelOfEmbedding (he : MeasurableEmbedding decode)
    (hP : IsotropicVariance.IsPoissonProcess lam decode Q)
    (act : (Pt m ≃ᵃⁱ[ℝ] Pt m) → C → C)
    (hact : ∀ g c, decode (act g c) = (decode c).map g) : Paper.NoiseModel m where
  Ω := C
  measurableSpace := inferInstance
  standardBorelSpace := inferInstance
  P := Q
  isProbabilityMeasure := inferInstance
  info S := (Paper.Noise.info (Paper.Noise.poisson lam) S).comap decode
  info_le S := (MeasurableSpace.comap_mono (poisson_info_le S)).trans he.measurable.comap_le
  info_mono := by
    intro S T hST
    exact MeasurableSpace.comap_mono (poisson_info_mono hST)
  iIndep_info _ _ S hS hb hd := isPoissonProcess_iIndep_info hP S hS hb hd
  union_ae S hS _hb hd A hA := by
    have heq : ((Paper.Noise.info (Paper.Noise.poisson lam) (⋃ k, S k)).comap decode) =
        ⨆ k, (Paper.Noise.info (Paper.Noise.poisson lam) (S k)).comap decode := by
      rw [poisson_info_union S hS hd, MeasurableSpace.comap_iSup]
    refine ⟨A, heq ▸ hA, ?_⟩
    simp
  act := act
  measurePreserving_act g _hg := measurePreserving_poissonAction he hP act hact g
  comap_info_act g _hg S := poisson_comap_info_action act hact g S

end IsotropicVariance.Infra.Instances
