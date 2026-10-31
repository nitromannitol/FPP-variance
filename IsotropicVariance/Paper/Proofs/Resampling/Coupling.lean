/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Labels
public import IsotropicVariance.Paper.Proofs.Resampling.Law
import IsotropicVariance.Paper.Proofs.Gain.BridgeGeometry

/-!
# The resampling as a coupling of a block

The concrete resampling is an instance of the abstract couplings of `Paper.Defs.Blocks` and
`Paper.Defs.Labels`, over which the earlier lemmas are stated.

* `Setting.isBlockCoupling_resamplingLaw`, `Setting.isBlockCoupling_blockResampling`: the old noise
  and the new noise of a block form an `IsBlockCoupling`.
* `Setting.isLabelResampling_blockResampling`: for `σ = Λ.sigma`, they form an `IsLabelResampling`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper

open Proofs.Resampling Proofs.Gain.Bridge

namespace Setting

variable {m : ℕ} (X : Setting.{u} m)

/-- **The resampling of `G i` is a coupling of `G i`**, for `G i` Borel with null frontier and
`σ i ≤ info (G i)`. The pair in `G i` is independent of the noise off `G i`: the group of the old
and new noise of `i`, read in `G i`, and the old noise off `G i`, are independent. -/
theorem isBlockCoupling_resamplingLaw {ι : Type*} {G : ι → Set (Pt m)}
    {σ : ι → MeasurableSpace X.Ω} {i : ι} (hG : MeasurableSet (G i))
    (hGfr : volume (frontier (G i)) = 0) (hσ : σ i ≤ X.info (G i)) :
    letI := X.measurableSpace
    X.IsBlockCoupling (G i) (X.resamplingLaw G σ) Prod.fst fun p => p.2 i := by
  let := X.measurableSpace
  have hσle := hσ.trans (X.info_le _)
  refine ⟨X.measurePreserving_old G σ, X.measurePreserving_new hσle,
    X.exchangeable_resamplingLaw hσle, fun A hA => X.ae_mem_iff_new_of_compl hσle hA, ?_⟩
  have hind : iIndep (fun b : Bool => X.info (bif b then G i else (G i)ᶜ)) X.P :=
    X.iIndep_info Bool _ (fun b => by cases b <;> simp [hG, hG.compl])
      (fun b => by cases b <;> simp [hGfr, frontier_compl]) (by
        have hd : Disjoint (interior (G i)) (interior (G i)ᶜ) :=
          disjoint_compl_right.mono interior_subset interior_subset
        rintro (_ | _) (_ | _) hij
        · exact absurd rfl hij
        · exact hd.symm
        · exact hd
        · exact absurd rfl hij)
  have hgroup := iIndep_groupSigma (κ := fun c => X.resampleKernel (G c) (σ c))
    (X.resamplingKernel_apply G σ) hind (fun b => X.info_le _)
    (I := fun b : Bool => bif b then {i} else ∅)
    (by
      rintro (_ | _) (_ | _) hij
      · exact absurd rfl hij
      · exact empty_disjoint _
      · exact disjoint_empty _
      · exact absurd rfl hij)
    (by
      rintro (_ | _) c hc B hB
      · exact absurd hc (notMem_empty c)
      · obtain rfl : c = i := hc
        exact ⟨fun ω => condExpKernel X.P (σ c) ω B,
          (measurable_condExpKernel (X.info_le _ B hB)).mono hσ le_rfl,
          X.resampleKernel_ae_eq hG hGfr hσ hB⟩)
  have h := hgroup.indep (i := true) (j := false) (by decide)
  simp only [Bool.cond_true, Bool.cond_false, groupSigma_singleton, groupSigma_empty] at h
  exact h

/-- **The resampling of a block is a coupling of the block.** -/
theorem isBlockCoupling_blockResampling (n W : ℝ) (L : ℕ) {σ : BlockIdx m → MeasurableSpace X.Ω}
    (i : ℕ) (z : Fin m → ℤ) (hσ : σ (i, z) ≤ X.info (block n W L i z)) :
    letI := X.measurableSpace
    X.IsBlockCoupling (block n W L i z) (X.blockResampling n W L σ) Prod.fst
      fun p => p.2 (i, z) := by
  let := X.measurableSpace
  exact X.isBlockCoupling_resamplingLaw (G := fun p : BlockIdx m => block n W L p.1 p.2)
    (i := (i, z)) (measurableSet_block n W L i z) (volume_frontier_block n W L i z) hσ

/-- **The resampling of a block given its label is a label resampling**: the label is unchanged,
and given each value of the label the old and new noise in the block are independent with the
same law. -/
theorem isLabelResampling_blockResampling (Λ : X.LabelFamily) {n W : ℝ} {L : ℕ}
    (hdet : Λ.IsDetermined n W L) (i : ℕ) (z : Fin m → ℤ) :
    X.IsLabelResampling Λ n W L i z (X.blockResampling n W L fun c => Λ.sigma c.1 c.2) Prod.fst
      fun p => p.2 (i, z) := by
  have hσ : Λ.sigma i z ≤ X.info (block n W L i z) := Λ.sigma_le hdet i z
  have hσle : Λ.sigma i z ≤ X.measurableSpace := hσ.trans (X.info_le _)
  have hcpl := X.isBlockCoupling_blockResampling n W L (σ := fun c => Λ.sigma c.1 c.2) i z hσ
  have hold := hcpl.measurePreserving_old
  refine ⟨hcpl, ?_, fun A B hA hB v => ?_⟩
  · have h : ∀ v, ∀ᵐ p ∂(X.blockResampling n W L fun c => Λ.sigma c.1 c.2),
        (p.1 ∈ Λ.label i z ⁻¹' {v} ↔ p.2 (i, z) ∈ Λ.label i z ⁻¹' {v}) := fun v =>
      X.ae_mem_iff_new_of_sigma (i := (i, z)) hσle ⟨{v}, MeasurableSpace.measurableSet_top, rfl⟩
    filter_upwards [ae_all_iff.2 h] with p hp
    exact ((hp (Λ.label i z p.1)).1 rfl)
  · have hA' := X.info_le _ A hA
    have hB' := X.info_le _ B hB
    have hY : MeasurableSet (Λ.label i z ⁻¹' {v}) :=
      hσle _ ⟨{v}, MeasurableSpace.measurableSet_top, rfl⟩
    have hκ := X.resampleKernel_ae_eq (measurableSet_block n W L i z)
      (volume_frontier_block n W L i z) hσ hB
    have hmain := setLIntegral_mul_measure_fiber (P := X.P) (ℓ := Λ.label i z) hσle
      (κ := X.resampleKernel (block n W L i z) (Λ.sigma i z)) hA' hB' hκ v
    have hE₁ : X.blockResampling n W L (fun c => Λ.sigma c.1 c.2)
        {p | p.1 ∈ A ∧ p.2 (i, z) ∈ B ∧ Λ.label i z p.1 = v} =
        ∫⁻ ω in A ∩ Λ.label i z ⁻¹' {v},
          X.resampleKernel (block n W L i z) (Λ.sigma i z) ω B ∂X.P := by
      have h := X.resamplingLaw_old_new_pi (fun p : BlockIdx m => block n W L p.1 p.2)
        (fun c => Λ.sigma c.1 c.2) {(i, z)} (C := A ∩ Λ.label i z ⁻¹' {v}) (hA'.inter hY)
        (A := fun _ => B) fun _ _ => hB'
      simp only [Finset.mem_singleton, forall_eq, Finset.prod_singleton] at h
      refine (congrArg _ ?_).trans h
      ext p
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
      tauto
    have hset : ∀ D : Set X.Ω, MeasurableSet D →
        X.blockResampling n W L (fun c => Λ.sigma c.1 c.2) {p | p.1 ∈ D ∧ Λ.label i z p.1 = v} =
          X.P (D ∩ Λ.label i z ⁻¹' {v}) := fun D hD =>
      hold.measure_preimage (hD.inter hY).nullMeasurableSet
    have hY' : X.blockResampling n W L (fun c => Λ.sigma c.1 c.2) {p | Λ.label i z p.1 = v} =
        X.P (Λ.label i z ⁻¹' {v}) := hold.measure_preimage hY.nullMeasurableSet
    rw [hE₁, hY', hset A hA', hset B hB']
    exact hmain

end Setting

end IsotropicVariance.Paper
