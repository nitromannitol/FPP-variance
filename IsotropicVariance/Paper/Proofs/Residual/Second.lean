/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.EfronStein.AllLabels
public import IsotropicVariance.Paper.Proofs.Gain.Bridge
public import IsotropicVariance.Paper.Proofs.Gain.GainVariance
public import IsotropicVariance.Paper.Proofs.Residual.First
public import IsotropicVariance.Paper.Proofs.Residual.Uniqueness
import IsotropicVariance.Paper.Proofs.Gain.BridgeGeometry

/-!
# Lemma `lem:residual`: the conditional variance of `F̄`

The last paragraph of the proof of Lemma `lem:residual`. Given `(X_G)_G`, the noise in distinct
blocks is conditionally independent and its resampling in `G` is a conditionally independent copy.
The Efron–Stein inequality, applied conditionally to `F̄`, with Jensen's inequality over `m`, gives
`E[Var[F̄ | (X_G)_G]] ≤ (2⌈K^{2/3}⌉)⁻¹ Σ_{m, G} E[(F_m^G − F_m)²]`. Translations by multiples of
`L(nQ_n)^{1/2} e₂` map blocks to blocks and the `X_G` of a block to that of the translated block, so
by stationarity the sum over `G` is the same for every `m`, and equation `eq:residual` bounds the
right side.

* `lintegral_sub_condExp_allSigma_le`: the conditional Efron–Stein step, on the block coordinates
  of the noise (`Bridge.regionMap`, in which the noise is the product of the block laws), from
  `Infra.EfronStein.lintegral_sub_condExp_allLabelSigma_le`. On the coordinates, the conditional
  independence of the paper is the product form of the fibers.
* `lintegral_sub_condExp_averagedMin_le`: the bound, at given offsets, by half the left side of
  equation `eq:residual`. Jensen's inequality over `m` and the translations are
  `Gain.labelCouplingEnergy_averagedMin_le`, for the resamplings `Bridge.bridgeResampling` of the
  blocks. A translate of a resampling is a resampling of the translated block
  (`Gain.shiftResamplings`), and `lintegral_labelResampling_eq` identifies its energy with that of
  the concrete resampling.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Residual

open Gain Gain.Bridge Infra.EfronStein

/-- Conditional expectations pull back along a measure-preserving map. -/
theorem condExp_comp_ae_eq {Ω Ω' : Type*} {m : MeasurableSpace Ω'} {mΩ : MeasurableSpace Ω}
    {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (hm : m ≤ mΩ') {Φ : Ω → Ω'} (hΦ : MeasurePreserving Φ P Q)
    {f : Ω' → ℝ} (hf : Integrable f Q) : P[f ∘ Φ | m.comap Φ] =ᵐ[P] Q[f | m] ∘ Φ := by
  have hle : m.comap Φ ≤ mΩ := (MeasurableSpace.comap_mono hm).trans hΦ.measurable.comap_le
  have hfc : Integrable (f ∘ Φ) P := hΦ.integrable_comp_of_integrable hf
  have hgc : Integrable (Q[f | m] ∘ Φ) P := hΦ.integrable_comp_of_integrable integrable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hfc (fun s _ _ => hgc.integrableOn) ?_
    (stronglyMeasurable_condExp.comp_measurable (comap_measurable Φ)).aestronglyMeasurable).symm
  rintro _ ⟨t, ht, rfl⟩ _
  have key : ∀ g : Ω' → ℝ, AEStronglyMeasurable g Q →
      ∫ x in Φ ⁻¹' t, g (Φ x) ∂P = ∫ y in t, g y ∂Q := fun g hg => by
    rw [← setIntegral_map (hm t ht) (by rwa [hΦ.map_eq]) hΦ.aemeasurable, hΦ.map_eq]
  change ∫ x in Φ ⁻¹' t, Q[f | m] (Φ x) ∂P = ∫ x in Φ ⁻¹' t, f (Φ x) ∂P
  rw [key _ integrable_condExp.aestronglyMeasurable, key _ hf.aestronglyMeasurable,
    setIntegral_condExp hm hf ht]

variable {m L K : ℕ}

/-- **Efron–Stein given all the labels, on the noise** (proof of Lemma `lem:residual`): for `Z`
square integrable and determined by the noise in the `K` slabs up to a null set,
`E[Var[Z | (X_G)_G]] ≤ ½ Σ_G E[(Z^G − Z)²]`, the sum over the blocks of the offsets `o`, for the
resamplings `Bridge.bridgeResampling` of the blocks given their labels. -/
theorem lintegral_sub_condExp_allSigma_le (X : Setting.{u} m) {n W : ℝ} (hn : 0 < n) (hW : 0 < W)
    (hL : 1 ≤ L) (hK : 1 ≤ K) (Λ : X.LabelFamily) (hdet : Λ.IsDetermined n W L)
    (o : Fin K → Fin m → Fin L) {Z Z' : X.Ω → ℝ} (hZ : MemLp Z 2 X.P)
    (hZ'm : Measurable[X.info {x | 0 ≤ Pt.lon x ∧ Pt.lon x ≤ K * n}] Z') (hZZ' : Z =ᵐ[X.P] Z') :
    ∫⁻ ω, ENNReal.ofReal ((Z ω - X.P[Z | Λ.allSigma K o] ω) ^ 2) ∂X.P ≤
      labelCouplingEnergy X n W L K Λ o (fun i z => bridgeResampling X Λ hdet i z) Z := by
  obtain ⟨Zt, hZtm, hZZt⟩ := exists_blockVersion X hn hW hL hK o hZ hZ'm hZZ'
  have hmap := map_regionMap X.toNoiseModel (S := blockOf (o := o) n W)
    (fun c => measurableSet_block n W L _ _) (fun c => volume_frontier_block n W L _ _)
    (disjoint_interior_blockOf (o := o) hn.le hW)
  have hΦ := measurable_regionMap X.toNoiseModel (blockOf (o := o) n W)
  have hMP : MeasurePreserving (regionMap X.toNoiseModel (blockOf (o := o) n W)) X.P
      (Measure.infinitePi (regionLaw X.toNoiseModel (blockOf n W))) := ⟨hΦ, hmap⟩
  let _ : MeasurableSpace Λ.V := ⊤
  have _ : MeasurableSingletonClass Λ.V := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hℓ : ∀ c : Gain.Bridge.BlockIdx L K o,
      Measurable (regionLabel X.toNoiseModel (blockOf n W c) (Λ.label c.1 c.2)) :=
    fun c => measurable_top_of_fibers (hdet c.1 c.2)
  have hZtL : MemLp Zt 2 (Measure.infinitePi (regionLaw X.toNoiseModel (blockOf n W))) := by
    rw [← hmap]
    exact (memLp_map_measure_iff hZtm.aestronglyMeasurable hΦ.aemeasurable).2 (hZ.ae_eq hZZt)
  have hES := lintegral_sub_condExp_allLabelSigma_le (regionLaw X.toNoiseModel (blockOf n W)) hℓ
    hZtm hZtL
  have hσ : Λ.allSigma K o = MeasurableSpace.comap (regionMap X.toNoiseModel (blockOf (o := o) n W))
      (allLabelSigma fun c : Gain.Bridge.BlockIdx L K o =>
        regionLabel X.toNoiseModel (blockOf n W c) (Λ.label c.1 c.2)) := by
    rw [allLabelSigma, MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp]
    refine le_antisymm (iSup₂_le fun i z => iSup_le fun hz => ?_) (iSup_le fun c => ?_)
    · exact le_iSup_of_le (⟨i, ⟨z, hz⟩⟩ : Gain.Bridge.BlockIdx L K o) le_rfl
    · exact le_iSup₂_of_le c.1 c.2 (le_iSup_of_le c.2.2 le_rfl)
  set E := (Measure.infinitePi (regionLaw X.toNoiseModel (blockOf n W)))[Zt | allLabelSigma
    fun c : Gain.Bridge.BlockIdx L K o =>
      regionLabel X.toNoiseModel (blockOf n W c) (Λ.label c.1 c.2)] with hE
  have hcond : X.P[Z | Λ.allSigma K o] =ᵐ[X.P]
      E ∘ regionMap X.toNoiseModel (blockOf (o := o) n W) := by
    rw [hσ]
    exact (condExp_congr_ae hZZt).trans (condExp_comp_ae_eq (allLabelSigma_le hℓ) hMP
      (hZtL.integrable one_le_two))
  have hEm : Measurable E := (stronglyMeasurable_condExp.mono (allLabelSigma_le hℓ)).measurable
  have hg : Measurable fun x => ENNReal.ofReal ((Zt x - E x) ^ 2) :=
    ((hZtm.sub hEm).pow_const 2).ennreal_ofReal
  calc ∫⁻ ω, ENNReal.ofReal ((Z ω - X.P[Z | Λ.allSigma K o] ω) ^ 2) ∂X.P
      = ∫⁻ ω, ENNReal.ofReal ((Zt (regionMap X.toNoiseModel (blockOf (o := o) n W) ω) -
          E (regionMap X.toNoiseModel (blockOf (o := o) n W) ω)) ^ 2) ∂X.P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hZZt, hcond] with ω h1 h2
        rw [h1, h2]
        rfl
    _ = ∫⁻ x, ENNReal.ofReal ((Zt x - E x) ^ 2)
          ∂Measure.infinitePi (regionLaw X.toNoiseModel (blockOf n W)) := hMP.lintegral_comp hg
    _ ≤ labelReplacementEnergy (regionLaw X.toNoiseModel (blockOf n W))
          (fun c => regionLabel X.toNoiseModel (blockOf n W c) (Λ.label c.1 c.2)) Zt := hES
    _ = _ := labelReplacementEnergy_eq_labelCouplingEnergy X hn hW hZtm hZZt Λ hdet

/-- **The second bound of Lemma `lem:residual` at given offsets**:
`E[Var[F̄ | (X_G)_G]] ≤ (2⌈K^{2/3}⌉)⁻¹ Σ_{m, G} E[(F_m^G − F_m)²] = ½ Σ_G E[(F^G − F)²]`. -/
theorem lintegral_sub_condExp_averagedMin_le (hm : 1 ≤ m) (X : Setting.{u} m) {b n W : ℝ}
    (hb : X.IsUpperBound b) (hn : 0 < n) (hW : 0 < W) (hL : 1 ≤ L) (hK : 1 ≤ K)
    {Λ : X.LabelFamily} (hdet : Λ.IsDetermined n W L) (hcov : IsCovariantAE Λ n W L)
    (o : Fin K → Fin m → Fin L) :
    ∫⁻ ω, ENNReal.ofReal ((averagedMin X b K n W L ω -
        X.P[averagedMin X b K n W L | Λ.allSigma K o] ω) ^ 2) ∂X.P ≤
      (1 / 2 : ℝ≥0∞) * residualEnergy X b K n W L Λ o := by
  obtain ⟨hL2, Z', hZ'm, hae⟩ := averagedMin_regular X hb K hn.le W L
  have hM : 1 ≤ colCount K := by
    unfold colCount
    rw [Nat.one_le_ceil_iff]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hK) _
  have hM0 : (colCount K : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show colCount K ≠ 0 by omega)
  have h₁ := lintegral_sub_condExp_allSigma_le X hn hW hL hK Λ hdet o hL2 hZ'm hae
  have h₂ := labelCouplingEnergy_averagedMin_le X hm hb hM hn.le W L hcov o
    fun i z => bridgeResampling X Λ hdet i z
  -- the version of `F`
  obtain ⟨G, hGm, hGae⟩ := exists_F_version X hb K hn.le (τ := (0 : Pt m)) Pt.lon_zero
  have hGi : Integrable G X.P := by
    have hbd : ∀ ω, ‖X.F b K n 0 ω‖ ≤ K * b * n := fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (F_nonneg X b K n 0 ω)]
      exact F_le X hb K hn.le 0 ω
    exact Integrable.of_bound (hGm.mono (X.info_le _) le_rfl).aestronglyMeasurable (K * b * n)
      (hGae.mono fun ω h => h ▸ hbd ω)
  -- stationarity: every translate has the energy of the concrete resampling
  have h₃ : ∀ j, labelCouplingEnergy X n W L K Λ o
      (shiftResamplings X hcov hm j fun i z => bridgeResampling X Λ hdet i z) (X.F b K n 0) =
      (1 / 2 : ℝ≥0∞) * residualEnergy X b K n W L Λ o := fun j => by
    unfold labelCouplingEnergy residualEnergy
    congr 1
    refine Finset.sum_congr rfl fun i _ => tsum_congr fun z => ?_
    exact lintegral_labelResampling_eq hdet
      (shiftResamplings X hcov hm j (fun i z => bridgeResampling X Λ hdet i z)
        i z).isLabelResampling
      (X.isLabelResampling_blockResampling Λ hdet i z) hGm hGi hGae
  rw [Finset.sum_congr rfl fun j _ => h₃ j, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel hM0 (ENNReal.natCast_ne_top _), one_mul] at h₂
  exact h₁.trans h₂

end IsotropicVariance.Paper.Proofs.Residual
