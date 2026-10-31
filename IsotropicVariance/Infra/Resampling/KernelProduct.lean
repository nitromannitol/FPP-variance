/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Independence.Integration

/-!
# Products of probability kernels

Coordinatewise products of Markov kernels are measurable. Pairing each input
coordinate with its output commutes with forming their independent product.
-/

@[expose] public section

namespace IsotropicVariance.Infra.Resampling

open MeasureTheory ProbabilityTheory Set MeasurableSpace
open scoped MeasureTheory ENNReal

variable {ι : Type*} {A E : ι → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (E i)]
  (κ : ∀ i, Kernel (A i) (E i)) [∀ i, IsMarkovKernel (κ i)]

/-- Independent output coordinates, each drawn using its corresponding input coordinate. -/
noncomputable def coordinateProductKernel : Kernel (∀ i, A i) (∀ i, E i) where
  toFun a := Measure.infinitePi (fun i => κ i (a i))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    refine MeasurableSpace.induction_on_inter
      (C := fun s _ => Measurable fun a : ∀ i, A i =>
        Measure.infinitePi (fun i => κ i (a i)) s)
      generateFrom_squareCylinders.symm
      (isPiSystem_squareCylinders (fun _ => isPiSystem_measurableSet) (by simp))
      (by simp) ?_ ?_ ?_
    · rintro s ⟨t, u, hu, rfl⟩
      have hmu : ∀ i, MeasurableSet (u i) := fun i => hu i (mem_univ i)
      simp_rw [Measure.infinitePi_pi _ (fun i _ => hmu i)]
      exact Finset.measurable_prod _ fun i _ =>
        (Kernel.measurable_coe (κ i) (hmu i)).comp (measurable_pi_apply i)
    · intro s hs hm
      simpa only [measure_compl hs (measure_ne_top _ _), measure_univ] using hm.const_sub 1
    · intro f hd hf hm
      simp_rw [measure_iUnion hd hf]
      exact Measurable.tsum hm

instance : IsMarkovKernel (coordinateProductKernel κ) :=
  ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))⟩

end IsotropicVariance.Infra.Resampling
