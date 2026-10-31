/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.BorelCoding
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-! # Standard Borel countable sums for finite-cloud configuration coding -/

@[expose] public section
open MeasureTheory Set
namespace IsotropicVariance.Infra.Instances

/-- Measurability from the canonical sigma-algebra on a dependent sum. -/
lemma poisson_measurable_sigma {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {Y : Type*} [MeasurableSpace Y] {f : (Σ i, X i) → Y}
    (hf : ∀ i, Measurable (fun x : X i => f ⟨i, x⟩)) : Measurable f := by
  intro A hA
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro i
  exact hf i hA

/-- Countable sums of standard Borel spaces are standard Borel. -/
theorem poisson_standardBorel_sigma (X : ℕ → Type*) [∀ i, MeasurableSpace (X i)]
    [∀ i, StandardBorelSpace (X i)] : StandardBorelSpace (Σ i, X i) := by
  let f : (Σ i, X i) → ℕ × ℝ := fun x => (x.1, embeddingReal (X x.1) x.2)
  have hf : Measurable f := poisson_measurable_sigma fun i =>
    measurable_const.prodMk (measurable_embeddingReal (X i))
  have hi : Function.Injective f := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hij : i = j := congrArg Prod.fst h
    subst j
    have hxy := (measurableEmbedding_embeddingReal (X i)).injective (congrArg Prod.snd h)
    exact congrArg (Sigma.mk i) hxy
  have he : MeasurableEmbedding f := by
    refine ⟨hi, hf, fun A hA => ?_⟩
    have hAi (i : ℕ) : MeasurableSet (Sigma.mk i ⁻¹' A) := (MeasurableSpace.measurableSet_iInf.mp hA) i
    have heq : f '' A = ⋃ i : ℕ, ({i} : Set ℕ) ×ˢ
        (embeddingReal (X i) '' (Sigma.mk i ⁻¹' A)) := by
      ext p
      constructor
      · rintro ⟨⟨i, x⟩, hx, rfl⟩
        exact mem_iUnion.mpr ⟨i, ⟨rfl, x, hx, rfl⟩⟩
      · intro hp
        obtain ⟨i, hp, x, hx, hxp⟩ := mem_iUnion.mp hp
        exact ⟨⟨i, x⟩, hx, Prod.ext hp.symm hxp⟩
    rw [heq]
    exact MeasurableSet.iUnion fun i => (measurableSet_singleton i).prod
      ((measurableEmbedding_embeddingReal (X i)).measurableSet_image.mpr (hAi i))
  exact standardBorel_of_measurableEmbedding he

end IsotropicVariance.Infra.Instances
