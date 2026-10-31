/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Standard Borel coding by countably many separating observables

Continuous injections from compactly covered spaces into a Polish coding space are measurable
embeddings. This provides a coding tool for canonical noise carriers, without postulating
standard Borel structure on arbitrary measure spaces or distribution spaces.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace

namespace IsotropicVariance.Infra.Instances

/-- A measurable embedding into a standard Borel space transports standard Borel structure. -/
theorem standardBorel_of_measurableEmbedding {X Y : Type*} [mX : MeasurableSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] {f : X → Y} (hf : MeasurableEmbedding f) :
    StandardBorelSpace X := by
  have : StandardBorelSpace (Set.range f) := hf.measurableSet_range.standardBorel
  let e := hf.equivRange
  let up := upgradeStandardBorel (Set.range f)
  let : TopologicalSpace (Set.range f) := up.toTopologicalSpace
  have : BorelSpace (Set.range f) := up.toBorelSpace
  have : PolishSpace (Set.range f) := up.toPolishSpace
  let : TopologicalSpace X := (inferInstance : TopologicalSpace (Set.range f)).induced e
  have hb : BorelSpace X := by
    constructor
    rw [borel_comap, ← BorelSpace.measurable_eq]
    exact e.measurableEmbedding.comap_eq.symm
  have hp : PolishSpace X := e.toEquiv.polishSpace_induced
  exact ⟨⟨inferInstance, hb, hp⟩⟩

/-- A continuous injection on a countable compact cover is a measurable embedding into a
Polish space; the original topology need not itself be Polish or metrizable. -/
theorem measurableEmbedding_of_compact_cover {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (K : ℕ → Set X) (hK : ∀ n, IsCompact (K n))
    (hcover : (⋃ n, K n) = Set.univ) {f : X → Y} (hf : Continuous f) (hinj : Function.Injective f) :
    MeasurableEmbedding f := by
  refine ⟨hinj, hf.measurable, ?_⟩
  intro A hA
  have hm (n) : MeasurableSet (f '' (A ∩ K n)) := by
    have : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    have hc : Continuous (fun x : K n => f x.val) := hf.comp continuous_subtype_val
    have hi : Function.Injective (fun x : K n => f x.val) := hinj.comp Subtype.val_injective
    have hemb := hc.isClosedEmbedding hi
    have : PolishSpace (K n) := hemb.polishSpace
    have he := hc.measurableEmbedding hi
    have hpre : MeasurableSet (Subtype.val ⁻¹' A : Set (K n)) := hA.preimage measurable_subtype_coe
    have himage : (fun x : K n => f x.val) '' (Subtype.val ⁻¹' A) = f '' (A ∩ K n) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.val, ⟨hx, x.property⟩, rfl⟩
      · rintro ⟨x, ⟨hxA, hxK⟩, rfl⟩
        exact ⟨⟨x, hxK⟩, hxA, rfl⟩
    rw [← himage]
    exact he.measurableSet_image.mpr hpre
  have heq : f '' A = ⋃ n, f '' (A ∩ K n) := by
    rw [← image_iUnion, ← inter_iUnion, hcover, inter_univ]
  rw [heq]
  exact MeasurableSet.iUnion hm

end IsotropicVariance.Infra.Instances
