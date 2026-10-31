/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Compactness.Lindelof

/-!
# Joint measurability from local measurable representatives

A second-countable spatial variable permits a countable subcover. The other variable needs
only a measurable structure, so the lemma applies to regional information sigma-algebras.
-/

@[expose] public section

open MeasureTheory Set

namespace IsotropicVariance.Infra.Instances

/-- A function locally equal, in its spatial variable, to jointly measurable functions is jointly
measurable when the spatial domain is second countable. -/
theorem measurable_of_locally_eq {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] {f : Ω × X → ℝ}
    (h : ∀ x : X, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∃ g : Ω × X → ℝ, Measurable g ∧ ∀ ω y, y ∈ V → f (ω, y) = g (ω, y)) :
    Measurable f := by
  classical
  choose V hV hx g hg heq using h
  obtain ⟨T, hT, hcover⟩ := isLindelof_univ.elim_countable_subcover V hV
    (show (Set.univ : Set X) ⊆ ⋃ x, V x from fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  have : Countable T := hT.to_subtype
  intro B hB
  have hrepr : f ⁻¹' B = ⋃ x : T, (Prod.snd ⁻¹' V x.val) ∩ (g x.val ⁻¹' B) := by
    ext p
    rcases p with ⟨ω, y⟩
    constructor
    · intro hp
      obtain ⟨x, hxT, hpx⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ y))
      apply Set.mem_iUnion.mpr
      refine ⟨⟨x, hxT⟩, hpx, ?_⟩
      change g x (ω, y) ∈ B
      rw [← heq x ω y hpx]
      exact hp
    · intro hp
      obtain ⟨x, hpx, hpB⟩ := Set.mem_iUnion.mp hp
      change f (ω, y) ∈ B
      rw [heq x.val ω y hpx]
      exact hpB
  rw [hrepr]
  exact MeasurableSet.iUnion fun x =>
    ((hV x.val).measurableSet.preimage measurable_snd).inter (hg x.val hB)

end IsotropicVariance.Infra.Instances
