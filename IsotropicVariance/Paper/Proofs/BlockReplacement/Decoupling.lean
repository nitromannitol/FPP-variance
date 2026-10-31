/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.BlockReplacement.SlabIndep
public import IsotropicVariance.Paper.Proofs.BlockReplacement.CondJensen
public import IsotropicVariance.Paper.Proofs.BlockReplacement.GainVersion
public import IsotropicVariance.Paper.Proofs.BlockReplacement.IndexVersion

/-!
# Conditional rewards: independent arrays on the noise

The proof of Lemma `lem:blocks` bounds `E Σ_i Y_i(J_{i−1}, J_i)` by the penalized-array lemma,
Lemma `lem:polynomialarray`, which needs arrays independent over the slabs. The rewards `Y_i` of
couplings glued over one old outcome need not be: a coupling may use randomness of the outcome
outside the noise. So we condition each block gain on the old information of its slab.

For the couplings of the blocks of each slab `i` on one probability space (a
`BlockCouplingFamily`), `LabelResidual.exists_conditional_rewards_info` gives arrays `y_i(j, k)` on
the noise, from the conditional gains `exists_condGain` of this file:
- measurable for the information of the slab `i`, hence independent over `i`;
- with moments at most those of `Y_i(j, k)` (conditional Jensen,
  `lintegral_pow_le_of_setLIntegral_eq`);
- with `Σ_i E Y_i(J_{i−1}, J_i) = E Σ_i y_i(J_{i−1}, J_i)`, because the indices `J` are functions of
  the information of the slabs (`exists_chainInfo_measurable_J`) and each block gain, given the
  old information of its slab, is independent of the old information of the other slabs
  (`IsBlockCoupling.indep_slab`, `exists_setLIntegral_eq_of_indep`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.BlockReplacement

variable {m : ℕ}

/-! ### The slabs -/

/-- The information of a slab of the chain is independent of that of the other slabs. -/
theorem indep_info_otherSlabsInfo (X : Setting m) {s : ℝ} (hs : 0 < s) {K : ℕ} (i : Fin K) :
    Indep (X.info (chainSlab s 0 i).set) (otherSlabsInfo X s i) X.P := by
  have hind := X.iIndep_info (Fin K) (fun r => (chainSlab s 0 r).set)
    (fun r => Infra.Slab.measurableSet_slab_set _) (fun r => Infra.Slab.volume_frontier_slab_set _)
    (Infra.Slab.pairwise_disjoint_interior_chainSlab hs 0 K)
  have h := indep_iSup_of_disjoint (fun r => X.info_le _) hind
    (S := {i}) (T := {r | r ≠ i}) (by simp)
  rw [iSup_singleton] at h
  convert h using 1
  rw [otherSlabsInfo, iSup_subtype']
  rfl

/-- The information of the chain lies in that of a slab and of the other slabs. -/
theorem chainInfo_le_sup (X : Setting m) (s : ℝ) {K : ℕ} (i : Fin K) :
    chainInfo X s K ≤ X.info (chainSlab s 0 i).set ⊔ otherSlabsInfo X s i := by
  refine iSup_le fun r => ?_
  by_cases h : r = i
  · subst h
    exact le_sup_left
  · exact (le_iSup (fun r : {r : Fin K // r ≠ i} => X.info (chainSlab s 0 r).set) ⟨r, h⟩).trans
      le_sup_right

theorem otherSlabsInfo_le (X : Setting m) (s : ℝ) {K : ℕ} (i : Fin K) :
    otherSlabsInfo X s i ≤ X.measurableSpace :=
  iSup_le fun _ => X.info_le _

/-! ### One block -/

/-- The squared normalized gain of a block replacement, in `[0, ∞]`. -/
noncomputable def sqGain (X : Setting m) (b s W Qn : ℝ) (i : ℕ) (j k : Fin m → ℤ) (c c' : X.Ω) :
    ℝ≥0∞ :=
  ENNReal.ofReal ((X.blockGain b s W i j k c c' / Qn) ^ 2)

/-- The squared gain is almost everywhere measurable. -/
theorem aemeasurable_sqGain (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {s W : ℝ} (hs : 0 < s)
    (hW : 0 < W) (Qn : ℝ) (i : ℕ) (j k : Fin m → ℤ) {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} {old new : Ω' → X.Ω} (hold : MeasurePreserving old P' X.P)
    (hnew : MeasurePreserving new P' X.P) :
    AEMeasurable (fun ω => sqGain X b s W Qn i j k (old ω) (new ω)) P' := by
  obtain ⟨g, hg, hae⟩ := exists_measurable_blockGain_ae X hb hs hW i j k hold hnew
  have hg' : Measurable g := hg.mono
    (sup_le ((MeasurableSpace.comap_mono (X.info_le _)).trans hold.measurable.comap_le)
      ((MeasurableSpace.comap_mono (X.info_le _)).trans hnew.measurable.comap_le)) le_rfl
  refine ⟨fun ω => ENNReal.ofReal ((g ω / Qn) ^ 2), ?_, ?_⟩
  · exact ENNReal.measurable_ofReal.comp ((hg'.div_const Qn).pow_const 2)
  · filter_upwards [hae] with ω hω
    simp only [sqGain, hω]

/-- **The conditional gain of one block**: given the old information of its slab, which is also
its conditional expectation given the old information of all the slabs. -/
theorem exists_condGain (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {s W : ℝ} (hs : 0 < s)
    (hW : 0 < W) (Qn : ℝ) {L K : ℕ} (i : Fin K) {z : Fin m → ℤ} (j k : Fin m → ℤ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {old new : Ω' → X.Ω} (hcpl : X.IsBlockCoupling (block s W L i z) P' old new)
    (hfin : ∫⁻ ω, sqGain X b s W Qn i j k (old ω) (new ω) ∂P' ≠ ∞) :
    ∃ φ : X.Ω → ℝ≥0∞, Measurable[X.info (chainSlab s 0 i).set] φ ∧
      ∀ A : Set X.Ω, MeasurableSet[X.info (chainSlab s 0 i).set ⊔ otherSlabsInfo X s i] A →
        ∫⁻ x in A, φ x ∂X.P = ∫⁻ ω in old ⁻¹' A, sqGain X b s W Qn i j k (old ω) (new ω) ∂P' := by
  have hold := hcpl.measurePreserving_old
  have hnew := hcpl.measurePreserving_new
  obtain ⟨g, hg, hae⟩ := exists_measurable_blockGain_ae X hb hs hW i j k hold hnew
  set G : Ω' → ℝ≥0∞ := fun ω => ENNReal.ofReal ((g ω / Qn) ^ 2) with hGdef
  have hGae : (fun ω => sqGain X b s W Qn i j k (old ω) (new ω)) =ᵐ[P'] G := by
    filter_upwards [hae] with ω hω
    simp only [sqGain, hGdef, hω]
  have hGm : Measurable[(X.info (chainSlab s 0 i).set).comap old ⊔
      (X.info (chainSlab s 0 i).set).comap new] G :=
    ENNReal.measurable_ofReal.comp ((hg.div_const Qn).pow_const 2)
  have h𝒜 : (X.info (chainSlab s 0 i).set).comap old ⊔ (X.info (chainSlab s 0 i).set).comap new ≤
      ‹MeasurableSpace Ω'› :=
    sup_le ((MeasurableSpace.comap_mono (X.info_le _)).trans hold.measurable.comap_le)
      ((MeasurableSpace.comap_mono (X.info_le _)).trans hnew.measurable.comap_le)
  obtain ⟨φ, hφ, hid⟩ := exists_setLIntegral_eq_of_indep hold (X.info_le _)
    (otherSlabsInfo_le X s i) (indep_info_otherSlabsInfo X hs i) h𝒜 le_sup_left
    (IsBlockCoupling.indep_slab hs i hcpl) hGm (by rwa [← lintegral_congr_ae hGae])
  refine ⟨φ, hφ, fun A hA => ?_⟩
  rw [hid A hA]
  exact (lintegral_congr_ae (ae_restrict_of_ae hGae)).symm

end IsotropicVariance.Paper.Proofs.BlockReplacement
