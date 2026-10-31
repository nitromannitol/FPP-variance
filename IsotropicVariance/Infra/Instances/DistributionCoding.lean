/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.DistributionBlocks

/-!
# Standard Borel coding of distributions

The canonical distribution cylinder sigma-algebra is coded by compatible
weak-dual restrictions along a compact exhaustion. Each block dual is standard
Borel, and compatibility is tested on countable dense sequences.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace Topology
open scoped Distributions

namespace IsotropicVariance.Infra.Instances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Borel sigma-algebra of the weak topology on a compact test-block dual. -/
noncomputable instance testBlockDualMeasurableSpace (K : Compacts E) :
    MeasurableSpace (WeakDual ℝ 𝓓_{K}(E, ℝ)) := borel _

instance testBlockDualBorelSpace (K : Compacts E) : BorelSpace (WeakDual ℝ 𝓓_{K}(E, ℝ)) :=
  ⟨rfl⟩

instance testBlockDualStandardBorelSpace [FiniteDimensional ℝ E] (K : Compacts E) :
    StandardBorelSpace (WeakDual ℝ 𝓓_{K}(E, ℝ)) := standardBorel_testBlockDual K

/-- Every test-block evaluation is measurable. -/
theorem measurable_testBlockDual_eval {K : Compacts E} (φ : 𝓓_{K}(E, ℝ)) :
    Measurable (fun f : WeakDual ℝ 𝓓_{K}(E, ℝ) => f φ) :=
  (WeakDual.eval_continuous φ).measurable

/-- Compact block restriction is measurable for the cylinder sigma-algebra. -/
theorem measurable_distributionBlocks [FiniteDimensional ℝ E] (K : CompactExhaustion E) :
    Measurable (distributionBlocks K) := by
  apply Measurable.of_eval
  intro n
  have : SecondCountableTopology 𝓓_{exhaustionCompact K n}(E, ℝ) :=
    secondCountable_testBlock _
  apply (measurableEmbedding_dualEvaluationCode _
    (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ (exhaustionCompact K n))).measurable_comp_iff.mp
  apply Measurable.of_eval
  intro j
  change Measurable (fun ν : WhiteNoiseConfig E =>
    ν (TestFunction.ofSupportedIn (Set.subset_univ _)
      (denseSeq 𝓓_{exhaustionCompact K n}(E, ℝ) j)))
  apply Measurable.of_comap_le
  exact le_iSup_of_le _ le_rfl

/-- Compatibility of block functionals is a measurable condition. -/
theorem measurableSet_compatibleTestBlocks [FiniteDimensional ℝ E]
    (K : CompactExhaustion E) : MeasurableSet {F : TestBlockDualFamily K | CompatibleTestBlocks K F} := by
  have hsc (n : ℕ) : SecondCountableTopology 𝓓_{exhaustionCompact K n}(E, ℝ) :=
    secondCountable_testBlock _
  have hiff (F : TestBlockDualFamily K) : CompatibleTestBlocks K F ↔
      ∀ n m, n ≤ m → ∀ j : ℕ,
        F m (ContDiffMapSupportedIn.monoCLM ℝ
          (denseSeq 𝓓_{exhaustionCompact K n}(E, ℝ) j)) =
        F n (denseSeq 𝓓_{exhaustionCompact K n}(E, ℝ) j) := by
    constructor
    · intro h n m hnm j
      exact h n m hnm _
    · intro h n m hnm
      have hc := ((F m).toStrongDual.continuous.comp
        (ContDiffMapSupportedIn.monoCLM ℝ :
          𝓓_{exhaustionCompact K n}(E, ℝ) →L[ℝ] 𝓓_{exhaustionCompact K m}(E, ℝ)).continuous).ext_on
        (denseRange_denseSeq 𝓓_{exhaustionCompact K n}(E, ℝ))
        (F n).toStrongDual.continuous (Set.eqOn_range.mpr (funext (h n m hnm)))
      exact congrFun hc
  simp_rw [hiff, ofPred_forall]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun m =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun j => ?_
  exact measurableSet_eq_fun
    ((measurable_testBlockDual_eval _).comp (measurable_pi_apply m))
    ((measurable_testBlockDual_eval _).comp (measurable_pi_apply n))

/-- Glued distribution evaluations are measurable in the compatible block family. -/
theorem measurable_glueTestBlocks (K : CompactExhaustion E) :
    Measurable (fun F : {F : TestBlockDualFamily K // CompatibleTestBlocks K F} =>
      glueTestBlocks K F.val F.property) := by
  apply Measurable.of_comap_le
  rw [WhiteNoiseConfig.instMeasurableSpace, MeasurableSpace.comap_iSup]
  apply iSup_le
  intro φ
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap
    (fun F : {F : TestBlockDualFamily K // CompatibleTestBlocks K F} =>
      F.val (testBlockIndex K φ) (testInChosenBlock K φ)) inferInstance ≤ _
  exact ((measurable_testBlockDual_eval (testInChosenBlock K φ)).comp
    ((measurable_pi_apply (testBlockIndex K φ)).comp measurable_subtype_coe)).comap_le

/-- The configuration cylinder space is measurably equivalent to compatible block duals. -/
noncomputable def distributionBlocksEquiv [FiniteDimensional ℝ E] (K : CompactExhaustion E) :
    WhiteNoiseConfig E ≃ᵐ {F : TestBlockDualFamily K // CompatibleTestBlocks K F} where
  toFun ν := ⟨distributionBlocks K ν, compatible_distributionBlocks K ν⟩
  invFun F := glueTestBlocks K F.val F.property
  left_inv ν := by
    apply distributionBlocks_injective K
    exact distributionBlocks_glueTestBlocks K _ _
  right_inv F := Subtype.ext (distributionBlocks_glueTestBlocks K F.val F.property)
  measurable_toFun := (measurable_distributionBlocks K).subtype_mk
  measurable_invFun := measurable_glueTestBlocks K

/-- The cylinder sigma-algebra on distributions is standard Borel. -/
theorem standardBorel_whiteNoiseConfig [FiniteDimensional ℝ E] :
    StandardBorelSpace (WhiteNoiseConfig E) := by
  let K : CompactExhaustion E := CompactExhaustion.choice E
  have : StandardBorelSpace {F : TestBlockDualFamily K // CompatibleTestBlocks K F} :=
    (measurableSet_compatibleTestBlocks K).standardBorel
  exact standardBorel_of_measurableEmbedding (distributionBlocksEquiv K).measurableEmbedding

end IsotropicVariance.Infra.Instances
