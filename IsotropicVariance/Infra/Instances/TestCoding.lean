/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Countable topology on compactly supported test-function blocks

The derivatives are bounded continuous functions supported in a fixed compact set. Restricting
such functions to that compact set is isometric, giving a second-countable coding target.
-/

@[expose] public section

open Set TopologicalSpace Topology
open scoped Distributions BoundedContinuousFunction

namespace IsotropicVariance.Infra.Instances

/-- Bounded continuous functions vanishing outside a specified compact set. -/
abbrev SupportedBounded (E F : Type*) [TopologicalSpace E] [MetricSpace F] [Zero F]
    (K : Compacts E) := {f : E →ᵇ F // Set.EqOn f 0 (K : Set E)ᶜ}

/-- Restriction of a supported bounded continuous function to its compact carrier. -/
def restrictSupported {E F : Type*} [TopologicalSpace E] [MetricSpace F] [Zero F]
    (K : Compacts E) (f : SupportedBounded E F K) : C(K, F) :=
  ⟨fun x => f.val x.val, f.val.continuous.comp continuous_subtype_val⟩

/-- Compact restriction loses no supremum distance for functions zero outside the carrier. -/
theorem isometry_restrictSupported {E F : Type*} [TopologicalSpace E] [MetricSpace F] [Zero F]
    (K : Compacts E) : Isometry (restrictSupported (F := F) K) := by
  apply isometry_iff_dist_eq.mpr
  intro f g
  apply le_antisymm
  · apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro x
    exact BoundedContinuousFunction.dist_coe_le_dist x.val
  · apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
    intro x
    by_cases hx : x ∈ (K : Set E)
    · exact ContinuousMap.dist_apply_le_dist (f := restrictSupported K f) (g := restrictSupported K g) ⟨x, hx⟩
    · rw [f.property hx, g.property hx, dist_self]
      exact dist_nonneg

/-- Supported bounded functions are second countable when the compact carrier and target are. -/
theorem secondCountable_supportedBounded {E F : Type*} [TopologicalSpace E] [T2Space E]
    [SecondCountableTopology E] [MetricSpace F] [Zero F] [SecondCountableTopology F]
    (K : Compacts E) : SecondCountableTopology (SupportedBounded E F K) := by
  have : SecondCountableTopology K := secondCountableTopology_induced K E Subtype.val
  have : SecondCountableTopology C(K, F) := ContinuousMap.instSecondCountableTopology
  exact (isometry_restrictSupported (F := F) K).isEmbedding.secondCountableTopology

/-- The countable derivative code of a smooth test-function block. -/
noncomputable def testDerivativeCode {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Compacts E) (φ : 𝓓_{K}(E, ℝ)) :
    (i : ℕ) → SupportedBounded E (E [×i]→L[ℝ] ℝ) K := fun i =>
  ⟨ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i φ, by
    intro x hx
    rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
    exact φ.iteratedFDeriv_zero_on_compl hx⟩

/-- The derivative-code topology is exactly the usual test-block topology. -/
theorem isInducing_testDerivativeCode {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Compacts E) : IsInducing (testDerivativeCode K) := by
  constructor
  simp only [Pi.topologicalSpace, induced_iInf, induced_compose, instTopologicalSpaceSubtype,
    Function.comp_def, testDerivativeCode, ContDiffMapSupportedIn.topologicalSpace,
    ContDiffMapSupportedIn.structureMapCLM]
  rfl

/-- A compactly supported smooth test-function block is second countable in finite dimensions. -/
theorem secondCountable_testBlock {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Compacts E) : SecondCountableTopology 𝓓_{K}(E, ℝ) := by
  have (i : ℕ) : FiniteDimensional ℝ (E [×i]→L[ℝ] ℝ) :=
    FiniteDimensional.of_injective
      (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
      ContinuousMultilinearMap.toMultilinearMap_injective
  have (i : ℕ) : SecondCountableTopology (SupportedBounded E (E [×i]→L[ℝ] ℝ) K) :=
    secondCountable_supportedBounded K
  exact (isInducing_testDerivativeCode K).secondCountableTopology

end IsotropicVariance.Infra.Instances
