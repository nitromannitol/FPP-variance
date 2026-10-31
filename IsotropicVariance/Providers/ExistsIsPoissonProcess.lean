/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import IsotropicVariance.Statements.Noise.IsPoissonProcess
public import IsotropicVariance.Statements.Space.Pt
import IsotropicVariance.Infra.Poisson.Joint

/-!
# Proof of `IsotropicVariance.exists_isPoissonProcess`

Proves `IsotropicVariance.Providers.exists_isPoissonProcess`, with exactly the type of the theorem
`IsotropicVariance.exists_isPoissonProcess` stated in
`IsotropicVariance.Statements.Companions.ExistsIsPoissonProcess`. The statement module proves its
theorem from this one and is not imported here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance.Providers

/-- The homogeneous Poisson process of every intensity exists on a standard Borel probability
space (non-vacuity of `IsPoissonProcess`; uncited). -/
theorem exists_isPoissonProcess (m : ℕ) (lam : ℝ≥0) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
      (η : Ω → Measure (Pt m)), IsProbabilityMeasure P ∧ IsPoissonProcess lam η P :=
  by
  -- transport the infrastructure process on `EuclideanSpace ℝ (Fin d)` by a linear isometry
  let e := (stdOrthonormalBasis ℝ (Pt m)).repr
  obtain ⟨Ω, _, hΩ, P, hP, η, hη⟩ :=
    Infra.Poisson.exists_standardBorel (Module.finrank ℝ (Pt m)) lam
  have hem : Measurable e.symm := e.symm.continuous.measurable
  have hvol : MeasurePreserving e.symm := e.symm.measurePreserving
  have hpre (B : Set (Pt m)) (hb : Bornology.IsBounded B) :
      Bornology.IsBounded (e.symm ⁻¹' B) := by
    rw [← e.image_eq_preimage_symm]
    exact e.lipschitzWith.isBounded_image hb
  refine ⟨Ω, _, hΩ, P, fun ω => (η ω).map e.symm, hP,
    (Measure.measurable_map _ hem).comp hη.measurable, ?_, ?_⟩
  · intro ω B hB hb
    rw [Measure.map_apply hem hB]
    exact (hη.counting ω).2 _ (hem hB) (hpre B hb)
  · intro k B hB hb hd
    have hmap (i : Fin k) :
        (fun ω => (η ω).map e.symm (B i)) = fun ω => η ω (e.symm ⁻¹' B i) := by
      funext ω
      exact Measure.map_apply hem (hB i)
    refine ⟨?_, fun i => ?_⟩
    · rw [show (fun i ω => (η ω).map e.symm (B i)) = fun i ω => η ω (e.symm ⁻¹' B i) from
        funext hmap]
      exact hη.independent k (fun i => e.symm ⁻¹' B i) (fun i => hem (hB i))
        (fun i => hpre _ (hb i)) (fun i j hij => (hd hij).preimage _)
    · rw [hmap i, ← hvol.measure_preimage (hB i).nullMeasurableSet]
      exact hη.count_law _ (hem (hB i)) (hpre _ (hb i))

end IsotropicVariance.Providers
