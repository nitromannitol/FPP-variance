/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.Steps
public import IsotropicVariance.Paper.Proofs.Gain.PoincareDefs
public import IsotropicVariance.Paper.Proofs.Gain.BridgeCoordinates
public import IsotropicVariance.Paper.Proofs.Gain.BridgeCoupling
import IsotropicVariance.Paper.Proofs.Gain.BridgeInfo
import IsotropicVariance.Paper.Proofs.Gain.BridgeGeometry

/-!
# Section `sec:gain`: the block coordinates of the noise

The tools that carry the product-space energies to the noise.

* The resampling of a block given the noise off it and its label is `bridgeResampling`.
* For offsets `o`, the coordinates are the blocks `BlockIdx L K o` of the `K` slabs, the coordinate
  of a block being the noise with the information of the block (`regionMap`); they are
  independent (`map_regionMap`).
* `Z` is almost surely a measurable function `Zt` of the coordinates (`exists_blockVersion`):
  the union law over the pieces of the strip (`exists_stronglyMeasurable_iSup_ae_eq`) and
  Doob–Dynkin.
* The label energy of `Z` is the coordinate energy of `Zt`
  (`labelReplacementEnergy_eq_labelCouplingEnergy`), by `lintegral_pairLaw_regionMap`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper

universe u

namespace Bridge

section Energies

variable {m : ℕ} (X : Setting.{u} m) {n W : ℝ} (hn : 0 < n) (hW : 0 < W) {L K : ℕ}
  {o : Fin K → Fin m → Fin L}
  {Zt : (∀ c : BlockIdx L K o, RegionCoord X.toNoiseModel (blockOf n W c)) → ℝ}
  (hZt : Measurable Zt) {Z : X.Ω → ℝ}
  (hZ : Z =ᵐ[X.P] Zt ∘ regionMap X.toNoiseModel (blockOf n W))

include hn hW hZt hZ

/-- The square energy of the resampling of a block given its label is the square label
resampling energy of its coordinate. -/
theorem lintegral_bridgeResampling_sq (Λ : X.LabelFamily) (hdet : Λ.IsDetermined n W L)
    (c : BlockIdx L K o) :
    ∫⁻ ω, ENNReal.ofReal ((Z ((bridgeResampling X Λ hdet c.1 c.2).new ω) -
        Z ((bridgeResampling X Λ hdet c.1 c.2).old ω)) ^ 2)
        ∂(bridgeResampling X Λ hdet c.1 c.2).P' =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((Zt x - Zt (Function.update x c y)) ^ 2)
        ∂(regionLaw X.toNoiseModel (blockOf n W) c)[|regionLabel X.toNoiseModel (blockOf n W c)
          (Λ.label c.1 c.2) ⁻¹' {(regionLabel X.toNoiseModel (blockOf n W c)
            (Λ.label c.1 c.2) (x c))}]
        ∂Measure.infinitePi (regionLaw X.toNoiseModel (blockOf n W)) := by
  have hℓ := hdet c.1 c.2
  have h1 := lintegral_realLaw_pairDecode X
    (pairLaw X.toNoiseModel (blockOf n W c) (Λ.label c.1 c.2)) (pairLaw_map_fst hℓ)
    (pairLaw_map_snd hℓ) (hZt.comp (measurable_regionMap _ _)) hZ
    (F := fun q => ENNReal.ofReal ((q.2 - q.1) ^ 2))
    ((measurable_snd.sub measurable_fst).pow_const 2).ennreal_ofReal
  have h2 := lintegral_pairLaw_regionMap X.toNoiseModel (S := blockOf (o := o) n W)
    (fun d => measurableSet_block n W L _ _) (fun d => volume_frontier_block n W L _ _)
    (fun d d' hdd => volume_blockOf_inter hn.le hW hdd) c (Λ.label c.1 c.2) hℓ
    (f := fun q => ENNReal.ofReal ((Zt q.2 - Zt q.1) ^ 2))
    (((hZt.comp measurable_snd).sub (hZt.comp measurable_fst)).pow_const 2).ennreal_ofReal
  refine h1.trans (h2.trans (lintegral_congr fun x => lintegral_congr fun y => ?_))
  rw [← neg_sub, neg_sq]

/-- The label energy of the coordinates is the label energy of the resamplings of the blocks. -/
theorem labelReplacementEnergy_eq_labelCouplingEnergy (Λ : X.LabelFamily)
    (hdet : Λ.IsDetermined n W L) :
    labelReplacementEnergy (regionLaw X.toNoiseModel (blockOf n W))
        (fun c => regionLabel X.toNoiseModel (blockOf n W c) (Λ.label c.1 c.2)) Zt =
      labelCouplingEnergy X n W L K Λ o (fun i z => bridgeResampling X Λ hdet i z) Z := by
  rw [labelReplacementEnergy, labelCouplingEnergy, tsum_blockIdx, one_div,
    ENNReal.div_eq_inv_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => tsum_congr fun z =>
    (lintegral_bridgeResampling_sq X hn hW hZt hZ Λ hdet ⟨i, z⟩).symm

end Energies

/-- **The block version.** A square-integrable `Z` determined by the noise in the strip
`[0, Kn] × ℝ^m` is almost surely a measurable function of the block coordinates. -/
theorem exists_blockVersion {m : ℕ} (X : Setting.{u} m) {n W : ℝ} (hn : 0 < n) (hW : 0 < W)
    {L K : ℕ} (hL : 1 ≤ L) (hK : 1 ≤ K) (o : Fin K → Fin m → Fin L) {Z Z' : X.Ω → ℝ}
    (hZ : MemLp Z 2 X.P)
    (hZ'm : Measurable[X.info {x | 0 ≤ Pt.lon x ∧ Pt.lon x ≤ K * n}] Z') (hZZ' : Z =ᵐ[X.P] Z') :
    ∃ Zt : (∀ c : BlockIdx L K o, RegionCoord X.toNoiseModel (blockOf n W c)) → ℝ,
      Measurable Zt ∧ Z =ᵐ[X.P] Zt ∘ regionMap X.toNoiseModel (blockOf n W) := by
  have hZi : Integrable Z' X.P := (hZ.integrable one_le_two).congr hZZ'
  let _ : Encodable (BlockIdx L K o) := Encodable.ofCountable _
  set T : ℕ → Set (Pt m) := fun k => ⋃ c ∈ Encodable.decode₂ (BlockIdx L K o) k, piece n W c
    with hTdef
  have hT : ∀ k, MeasurableSet (T k) := fun k =>
    show MeasurableSet (⋃ c ∈ Encodable.decode₂ (BlockIdx L K o) k, piece n W c) from
      Encodable.iUnion_decode₂_cases MeasurableSet.empty (measurableSet_piece n W)
  have hTfr : ∀ k, volume (frontier (T k)) = 0 := fun k =>
    show volume (frontier (⋃ c ∈ Encodable.decode₂ (BlockIdx L K o) k, piece n W c)) = 0 from
      Encodable.iUnion_decode₂_cases (by simp) (volume_frontier_piece n W)
  have hTd : Pairwise (Function.onFun Disjoint T) :=
    Encodable.iUnion_decode₂_disjoint_on (pairwise_disjoint_piece hn.le hW)
  have hU : {x : Pt m | 0 ≤ Pt.lon x ∧ Pt.lon x ≤ K * n} ⊆ ⋃ k, T k := by
    show _ ⊆ ⋃ k, ⋃ c ∈ Encodable.decode₂ (BlockIdx L K o) k, piece n W c
    rw [Encodable.iUnion_decode₂]
    intro x hx
    obtain ⟨c, hc⟩ := exists_mem_piece (o := o) hn hW hL hK hx.1 hx.2
    exact mem_iUnion.2 ⟨c, hc⟩
  obtain ⟨Z'', hZ''m, hZ'Z''⟩ :=
    exists_stronglyMeasurable_iSup_ae_eq X.toNoiseModel hT hTfr hTd hU hZ'm hZi
  -- a block of the strip
  have c₀ : BlockIdx L K o :=
    ⟨⟨0, hK⟩, ⟨fun k => ((o ⟨0, hK⟩ k : ℕ) : ℤ), by intro k; simp⟩⟩
  have hMle : (⨆ k, X.info (T k)) ≤ ⨆ c : BlockIdx L K o, X.info (blockOf n W c) := by
    refine iSup_le fun k => ?_
    show X.info (⋃ c ∈ Encodable.decode₂ (BlockIdx L K o) k, piece n W c) ≤ _
    refine Encodable.iUnion_decode₂_cases
      (C := fun s => X.info s ≤ ⨆ c : BlockIdx L K o, X.info (blockOf n W c)) ?_ ?_
    · exact (X.info_mono (empty_subset _)).trans
        (le_iSup (fun c : BlockIdx L K o => X.info (blockOf n W c)) c₀)
    · intro c
      exact (X.info_mono (piece_subset n W c)).trans
        (le_iSup (fun c : BlockIdx L K o => X.info (blockOf n W c)) c)
  have hZ''Φ : Measurable[MeasurableSpace.comap
      (regionMap X.toNoiseModel (blockOf (o := o) n W)) MeasurableSpace.pi] Z'' := by
    rw [comap_regionMap]
    exact hZ''m.measurable.mono hMle le_rfl
  obtain ⟨Zt, hZtm, hZteq⟩ := hZ''Φ.exists_eq_measurable_comp
  exact ⟨Zt, hZtm, hZZ'.trans (hZ'Z''.trans (EventuallyEq.of_eq hZteq))⟩

end Bridge

open Bridge

end IsotropicVariance.Paper.Proofs.Gain
