/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.TestDual
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfigInstMeasurableSpace

/-!
# Distributions as compatible compact test-block duals

Restrictions to a compact exhaustion determine every distribution. Conversely,
compatible continuous linear forms on the blocks glue to a distribution by the
universal property of the test-function topology.
-/

@[expose] public section

open Set TopologicalSpace Topology MeasureTheory
open scoped Distributions

namespace IsotropicVariance.Infra.Instances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A compact exhaustion, with its compactness bundled. -/
def exhaustionCompact (K : CompactExhaustion E) (n : ℕ) : Compacts E :=
  ⟨K n, K.isCompact n⟩

/-- The weak-dual blocks attached to an exhaustion. -/
abbrev TestBlockDualFamily (K : CompactExhaustion E) :=
  (n : ℕ) → WeakDual ℝ 𝓓_{exhaustionCompact K n}(E, ℝ)

/-- Enlargement of a test's compact support preserves its underlying function. -/
theorem coe_mono_testBlock {K L : Compacts E} (h : K ≤ L) (φ : 𝓓_{K}(E, ℝ)) :
    ⇑(ContDiffMapSupportedIn.monoCLM ℝ φ : 𝓓_{L}(E, ℝ)) = φ := by
  simp only [ContDiffMapSupportedIn.monoCLM_apply, le_refl, h, and_self, ite_true]

/-- Compatibility means that enlarging a test's support does not change its evaluation. -/
def CompatibleTestBlocks (K : CompactExhaustion E) (F : TestBlockDualFamily K) : Prop :=
  ∀ n m, n ≤ m → ∀ φ : 𝓓_{exhaustionCompact K n}(E, ℝ),
    F m (ContDiffMapSupportedIn.monoCLM ℝ φ) = F n φ

/-- Compatible block functionals agree on tests represented in two different blocks. -/
theorem compatibleTestBlocks_eval_eq {K : CompactExhaustion E} {F : TestBlockDualFamily K}
    (hF : CompatibleTestBlocks K F) {n m : ℕ}
    (φ : 𝓓_{exhaustionCompact K n}(E, ℝ)) (ψ : 𝓓_{exhaustionCompact K m}(E, ℝ))
    (h : (φ : E → ℝ) = ψ) : F n φ = F m ψ := by
  have hn : exhaustionCompact K n ≤ exhaustionCompact K (max n m) := K.subset (le_max_left _ _)
  have hm : exhaustionCompact K m ≤ exhaustionCompact K (max n m) := K.subset (le_max_right _ _)
  rw [← hF n (max n m) (le_max_left _ _) φ, ← hF m (max n m) (le_max_right _ _) ψ]
  congr 1
  apply DFunLike.ext'
  rw [coe_mono_testBlock hn, coe_mono_testBlock hm, h]

/-- One block containing the support of a given global test. -/
noncomputable def testBlockIndex (K : CompactExhaustion E) (φ : 𝓓((⊤ : Opens E), ℝ)) : ℕ :=
  (K.exists_superset_of_isCompact φ.hasCompactSupport).choose

/-- The global test regarded as a member of its chosen block. -/
noncomputable def testInChosenBlock (K : CompactExhaustion E) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    𝓓_{exhaustionCompact K (testBlockIndex K φ)}(E, ℝ) :=
  .of_support_subset φ.contDiff
    (subset_closure.trans (K.exists_superset_of_isCompact φ.hasCompactSupport).choose_spec)

/-- The evaluation defined by compatible block functionals. -/
noncomputable def gluedBlockValue (K : CompactExhaustion E) (F : TestBlockDualFamily K)
    (φ : 𝓓((⊤ : Opens E), ℝ)) : ℝ := F (testBlockIndex K φ) (testInChosenBlock K φ)

/-- Glued evaluation agrees with every representative, not only the chosen one. -/
theorem gluedBlockValue_ofSupportedIn {K : CompactExhaustion E} {F : TestBlockDualFamily K}
    (hF : CompatibleTestBlocks K F) {L : Compacts E} (φ : 𝓓_{L}(E, ℝ))
    {n : ℕ} (hL : L ≤ exhaustionCompact K n) :
    gluedBlockValue K F (TestFunction.ofSupportedIn (Set.subset_univ _) φ) =
      F n (ContDiffMapSupportedIn.monoCLM ℝ φ) := by
  apply compatibleTestBlocks_eval_eq hF
  exact (coe_mono_testBlock hL φ).symm

/-- Glue compatible blocks to an everywhere defined distribution. -/
noncomputable def glueTestBlocks (K : CompactExhaustion E) (F : TestBlockDualFamily K)
    (hF : CompatibleTestBlocks K F) : WhiteNoiseConfig E :=
  TestFunction.limitCLM ℝ (gluedBlockValue K F)
    (fun L _ =>
      let n := (K.exists_superset_of_isCompact L.isCompact).choose
      (F n).toStrongDual.comp (ContDiffMapSupportedIn.monoCLM ℝ))
    (fun L _ φ => gluedBlockValue_ofSupportedIn hF φ
      (K.exists_superset_of_isCompact L.isCompact).choose_spec)

/-- Restrict a distribution to all compact test blocks. -/
noncomputable def distributionBlocks (K : CompactExhaustion E) (ν : WhiteNoiseConfig E) :
    TestBlockDualFamily K := fun n =>
  ν.comp (TestFunction.ofSupportedInCLM ℝ (show (exhaustionCompact K n : Set E) ⊆ (⊤ : Opens E) from Set.subset_univ _))

/-- Restrictions of a distribution are compatible. -/
theorem compatible_distributionBlocks (K : CompactExhaustion E) (ν : WhiteNoiseConfig E) :
    CompatibleTestBlocks K (distributionBlocks K ν) := by
  intro n m hnm φ
  change ν (TestFunction.ofSupportedIn (Set.subset_univ _) (ContDiffMapSupportedIn.monoCLM ℝ φ)) =
    ν (TestFunction.ofSupportedIn (Set.subset_univ _) φ)
  congr 1
  apply DFunLike.ext'
  exact coe_mono_testBlock (K.subset hnm) φ

/-- Gluing recovers each member of a compatible family. -/
theorem distributionBlocks_glueTestBlocks (K : CompactExhaustion E) (F : TestBlockDualFamily K)
    (hF : CompatibleTestBlocks K F) : distributionBlocks K (glueTestBlocks K F hF) = F := by
  funext n
  apply DFunLike.ext
  intro φ
  change gluedBlockValue K F (TestFunction.ofSupportedIn (Set.subset_univ _) φ) = F n φ
  rw [gluedBlockValue_ofSupportedIn hF φ (le_refl (exhaustionCompact K n))]
  congr 1
  apply DFunLike.ext'
  exact coe_mono_testBlock le_rfl φ

/-- Block restrictions distinguish distributions. -/
theorem distributionBlocks_injective (K : CompactExhaustion E) :
    Function.Injective (distributionBlocks K) := by
  intro ν μ h
  apply DFunLike.ext
  intro φ
  have hn := congrFun h (testBlockIndex K φ)
  have hv := DFunLike.congr_fun hn (testInChosenBlock K φ)
  change ν (TestFunction.ofSupportedIn (Set.subset_univ _) (testInChosenBlock K φ)) =
    μ (TestFunction.ofSupportedIn (Set.subset_univ _) (testInChosenBlock K φ)) at hv
  have heq : TestFunction.ofSupportedIn (Set.subset_univ _) (testInChosenBlock K φ) = φ := by
    ext x
    rfl
  simpa only [heq] using hv

end IsotropicVariance.Infra.Instances
