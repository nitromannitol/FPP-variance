/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Model
public import IsotropicVariance.Infra.Poisson.BoundedLaw
import IsotropicVariance.Infra.WhiteNoiseProps.Motion

/-!
# The Poisson predicate of the model and the construction interface

The predicate `IsotropicVariance.IsPoissonProcess` omits a redundant locally-finite class field.
Its literal bounded natural counts supply that field, and its finite joint axiom supplies the
marginal and independence API.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace IsotropicVariance.Infra.Instances

/-- Extract a marginal from the finite-family Poisson law. -/
theorem isPoissonProcess_count_law {E Ω : Type*} [PseudoMetricSpace E] [MeasureSpace E]
    [MeasurableSpace Ω] {lam : ℝ≥0} {η : Ω → Measure E} {P : Measure Ω}
    (h : IsotropicVariance.IsPoissonProcess lam η P) {B : Set E}
    (hB : MeasurableSet B) (hb : Bornology.IsBounded B) :
    HasLaw (fun ω => η ω B) (Poisson.poissonCountLaw (lam * (volume B).toNNReal)) P := by
  have hh := h.2.2 1 (fun _ => B) (fun _ => hB) (fun _ => hb)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim)
  exact hh.2 0

/-- The predicate `IsotropicVariance.IsPoissonProcess` supplies the full interface
`Poisson.IsPoissonProcess` on Euclidean coordinate space. -/
theorem isPoissonProcess_to_infra {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {lam : ℝ≥0} {η : Ω → Measure (Poisson.E d)} {P : Measure Ω}
    (h : IsotropicVariance.IsPoissonProcess lam η P) : Poisson.IsPoissonProcess lam η P := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro ω
    exact Poisson.isLocallyFiniteCountingMeasure_of_counts (h.2.1 ω)
  · intro B hB hb
    exact isPoissonProcess_count_law h hB hb
  · intro k B hB hb hd
    exact (h.2.2 k B hB hb hd).1

/-- Volume-preserving maps with bounded preimages preserve the Poisson predicate. -/
theorem isPoissonProcess_map {E F Ω : Type*} [PseudoMetricSpace E] [MeasureSpace E]
    [PseudoMetricSpace F] [MeasureSpace F] [MeasurableSpace Ω]
    {lam : ℝ≥0} {η : Ω → Measure E} {P : Measure Ω}
    (h : IsotropicVariance.IsPoissonProcess lam η P) {g : E → F}
    (hg : MeasurePreserving g volume volume)
    (hb : ∀ B : Set F, Bornology.IsBounded B → Bornology.IsBounded (g ⁻¹' B)) :
    IsotropicVariance.IsPoissonProcess lam (fun ω => (η ω).map g) P := by
  refine ⟨(Measure.measurable_map g hg.measurable).comp h.1, ?_, ?_⟩
  · intro ω B hB hbounded
    obtain ⟨n, hn⟩ := h.2.1 ω (g ⁻¹' B) (hg.measurable hB) (hb B hbounded)
    exact ⟨n, by rwa [Measure.map_apply hg.measurable hB]⟩
  · intro k B hB hbounded hd
    have hh := h.2.2 k (fun i => g ⁻¹' B i) (fun i => hg.measurable (hB i))
      (fun i => hb (B i) (hbounded i)) (fun i j hij => (hd hij).preimage g)
    have heq : (fun i ω => (η ω).map g (B i)) = (fun i ω => η ω (g ⁻¹' B i)) := by
      funext i ω
      exact Measure.map_apply hg.measurable (hB i)
    refine ⟨heq.symm ▸ hh.1, ?_⟩
    intro i
    have hv := hg.measure_preimage (hB i).nullMeasurableSet
    simpa only [Measure.map_apply hg.measurable (hB i), hv] using hh.2 i

/-- Euclidean coordinates of the paper's ambient space, as a volume-preserving linear isometry. -/
noncomputable def poissonCoordinates (m : ℕ) :
    Pt m ≃ₗᵢ[ℝ] Poisson.E (Module.finrank ℝ (Pt m)) := (stdOrthonormalBasis ℝ (Pt m)).repr

/-- A Poisson process in the paper's space satisfies `Poisson.IsPoissonProcess` after changing
coordinates. -/
theorem isPoissonProcess_coordinates {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {lam : ℝ≥0} {η : Ω → Measure (Pt m)} {P : Measure Ω}
    (h : IsotropicVariance.IsPoissonProcess lam η P) :
    Poisson.IsPoissonProcess lam (fun ω => (η ω).map (poissonCoordinates m)) P :=
  isPoissonProcess_to_infra (isPoissonProcess_map h (poissonCoordinates m).measurePreserving
    (fun _ hb => (poissonCoordinates m).isometry.antilipschitzWith.isBounded_preimage hb))

/-- The coordinate change induces a measurable equivalence on measure configurations. -/
noncomputable def poissonMeasureCoordinates (m : ℕ) :
    Measure (Pt m) ≃ᵐ Measure (Poisson.E (Module.finrank ℝ (Pt m))) where
  toFun μ := μ.map (poissonCoordinates m)
  invFun μ := μ.map (poissonCoordinates m).symm
  left_inv μ := by
    change (μ.map (poissonCoordinates m)).map (poissonCoordinates m).symm = μ
    rw [Measure.map_map (poissonCoordinates m).symm.continuous.measurable
      (poissonCoordinates m).continuous.measurable]
    have heq : (poissonCoordinates m).symm ∘ poissonCoordinates m = id := by
      funext x
      exact (poissonCoordinates m).symm_apply_apply x
    rw [heq, Measure.map_id]
  right_inv μ := by
    change (μ.map (poissonCoordinates m).symm).map (poissonCoordinates m) = μ
    rw [Measure.map_map (poissonCoordinates m).continuous.measurable
      (poissonCoordinates m).symm.continuous.measurable]
    have heq : poissonCoordinates m ∘ (poissonCoordinates m).symm = id := by
      funext x
      exact (poissonCoordinates m).apply_symm_apply x
    rw [heq, Measure.map_id]
  measurable_toFun := Measure.measurable_map _ (poissonCoordinates m).continuous.measurable
  measurable_invFun := Measure.measurable_map _ (poissonCoordinates m).symm.continuous.measurable

/-- The Poisson predicate determines the full configuration law on the paper's space. -/
theorem isPoissonProcess_law_eq {m : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {lam : ℝ≥0} {η : Ω → Measure (Pt m)} {ξ : Ω' → Measure (Pt m)} {P : Measure Ω} {Q : Measure Ω'}
    (hη : IsotropicVariance.IsPoissonProcess lam η P)
    (hξ : IsotropicVariance.IsPoissonProcess lam ξ Q) : P.map η = Q.map ξ := by
  apply (poissonMeasureCoordinates m).measurableEmbedding.map_injective
  rw [Measure.map_map (poissonMeasureCoordinates m).measurable hη.1,
    Measure.map_map (poissonMeasureCoordinates m).measurable hξ.1]
  change P.map (fun ω => (η ω).map (poissonCoordinates m)) =
    Q.map (fun ω => (ξ ω).map (poissonCoordinates m))
  exact (isPoissonProcess_coordinates hη).law_eq (isPoissonProcess_coordinates hξ)

/-- Proper rigid motions preserve the Poisson predicate (in fact all rigid motions do). -/
theorem isPoissonProcess_rigidMotion {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {lam : ℝ≥0} {η : Ω → Measure (Pt m)} {P : Measure Ω}
    (h : IsotropicVariance.IsPoissonProcess lam η P) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) :
    IsotropicVariance.IsPoissonProcess lam (fun ω => (η ω).map g) P :=
  isPoissonProcess_map h (WhiteNoiseProps.measurePreserving_rigidMotion g)
    (fun _ hb => g.isometry.antilipschitzWith.isBounded_preimage hb)

/-- Rigid-motion invariance as an equality of Poisson configuration laws. -/
theorem isPoissonProcess_rigidMotion_law {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {lam : ℝ≥0} {η : Ω → Measure (Pt m)} {P : Measure Ω}
    (h : IsotropicVariance.IsPoissonProcess lam η P) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) :
    P.map (fun ω => (η ω).map g) = P.map η :=
  isPoissonProcess_law_eq (isPoissonProcess_rigidMotion h g) h

end IsotropicVariance.Infra.Instances
