/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.BridgeCoordinates
public import IsotropicVariance.Paper.Proofs.Gain.BridgeCoupling
import IsotropicVariance.Paper.Proofs.Gain.BridgeGeometry
import IsotropicVariance.Paper.Proofs.Gain.BridgeInfo

/-!
# The energy of a resampling given a label is determined

Translations do not carry the concrete resampling of a block to the concrete resampling of the
translated block (the kernels are conditional laws, chosen block by block). For the stationarity in
the last paragraph of the proof of Lemma `lem:residual`, and to identify `ω^G` with a draw from the
conditional law of the block given its label (same paragraph), this file shows that the law of the
pair `(ω, ω^G)`, read on the noise, is determined by the properties of a resampling given the label.

* `measure_rect`: for `A, B` in `G` and `C, D` off `G`, the probability that the old noise is in
  `A ∩ C` and the new noise in `B ∩ D` is `(Σ_v P(A, λ = v) P(B, λ = v) / P(λ = v)) P(C ∩ D)`:
  the new noise agrees with the old one off `G`, the pair in `G` is independent of the noise off
  `G`, and given the label the two are independent in `G`.
* `map_split_eq`: hence the pair of the noises read in `G` and off `G` has one law.
* `lintegral_labelResampling_eq`: hence `E (Z^G − Z)²` is the same for all the resamplings of `G`
  given its label, for `Z` determined by the noise up to a null set.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Residual

open Gain.Bridge

variable {m : ℕ} {X : Setting.{u} m} {Λ : X.LabelFamily} {n W : ℝ} {L i : ℕ} {z : Fin m → ℤ}

/-- **The law of a resampling on rectangles.** -/
theorem measure_rect {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (hdet : Λ.IsDetermined n W L) (h : X.IsLabelResampling Λ n W L i z P' old new)
    {A B C D : Set X.Ω} (hA : MeasurableSet[X.info (block n W L i z)] A)
    (hB : MeasurableSet[X.info (block n W L i z)] B)
    (hC : MeasurableSet[X.info (block n W L i z)ᶜ] C)
    (hD : MeasurableSet[X.info (block n W L i z)ᶜ] D) :
    P' (old ⁻¹' (A ∩ C) ∩ new ⁻¹' (B ∩ D)) =
      (∑ v, X.P (A ∩ Λ.label i z ⁻¹' {v}) * X.P (B ∩ Λ.label i z ⁻¹' {v}) *
        (X.P (Λ.label i z ⁻¹' {v}))⁻¹) * X.P (C ∩ D) := by
  have hc := h.isBlockCoupling
  have hold := hc.measurePreserving_old
  have hnew := hc.measurePreserving_new
  have hfib : ∀ v, MeasurableSet (Λ.label i z ⁻¹' {v}) := fun v => X.info_le _ _ (hdet i z v)
  have hA' := X.info_le _ A hA
  have hB' := X.info_le _ B hB
  have hCD' := X.info_le _ _ (hC.inter hD)
  have hae : (old ⁻¹' (A ∩ C) ∩ new ⁻¹' (B ∩ D) : Set Ω') =ᵐ[P']
      old ⁻¹' A ∩ new ⁻¹' B ∩ old ⁻¹' (C ∩ D) := by
    refine eventuallyEqSet_iff.mpr ?_
    filter_upwards [hc.agree_compl D hD] with ω hω
    simp only [mem_inter_iff, mem_preimage]
    tauto
  have hE : MeasurableSet (old ⁻¹' A ∩ new ⁻¹' B) :=
    (hold.measurable hA').inter (hnew.measurable hB')
  have hind := (Indep_iff _ _ _).1 hc.indep (old ⁻¹' A ∩ new ⁻¹' B) (old ⁻¹' (C ∩ D))
    ((le_sup_left (b := (X.info (block n W L i z)).comap new) _
      (MeasurableSpace.measurableSet_comap.2 ⟨A, hA, rfl⟩)).inter
      (le_sup_right (a := (X.info (block n W L i z)).comap old) _
        (MeasurableSpace.measurableSet_comap.2 ⟨B, hB, rfl⟩)))
    (MeasurableSpace.measurableSet_comap.2 ⟨C ∩ D, hC.inter hD, rfl⟩)
  rw [measure_congr hae, hind, hold.measure_preimage hCD'.nullMeasurableSet]
  congr 1
  rw [measure_eq_sum_fibers (ℓ := fun ω => Λ.label i z (old ω))
    (fun v => hold.measurable (hfib v)) P' hE]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hp : P' (old ⁻¹' (Λ.label i z ⁻¹' {v})) = X.P (Λ.label i z ⁻¹' {v}) :=
    hold.measure_preimage (hfib v).nullMeasurableSet
  have hci := h.condIndep A B hA hB v
  have e₁ : {ω | old ω ∈ A ∧ new ω ∈ B ∧ Λ.label i z (old ω) = v} =
      old ⁻¹' A ∩ new ⁻¹' B ∩ (fun ω => Λ.label i z (old ω)) ⁻¹' {v} := by
    ext ω
    simp [and_assoc]
  have e₂ : ∀ S : Set X.Ω, MeasurableSet S →
      P' {ω | old ω ∈ S ∧ Λ.label i z (old ω) = v} = X.P (S ∩ Λ.label i z ⁻¹' {v}) := fun S hS =>
    hold.measure_preimage (hS.inter (hfib v)).nullMeasurableSet
  rw [e₁, e₂ A hA', e₂ B hB', show P' {ω | Λ.label i z (old ω) = v} =
    X.P (Λ.label i z ⁻¹' {v}) from hp] at hci
  by_cases h0 : X.P (Λ.label i z ⁻¹' {v}) = 0
  · have hle : P' (old ⁻¹' A ∩ new ⁻¹' B ∩ (fun ω => Λ.label i z (old ω)) ⁻¹' {v}) ≤
        P' (old ⁻¹' (Λ.label i z ⁻¹' {v})) := measure_mono inter_subset_right
    rw [hp, h0] at hle
    have hA0 : X.P (A ∩ Λ.label i z ⁻¹' {v}) = 0 := measure_mono_null inter_subset_right h0
    rw [hA0, zero_mul, zero_mul]
    exact le_antisymm hle bot_le
  · rw [← hci, mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), mul_one]

section Split

variable (X) (G : Set (Pt m))

/-- The noise read in `G` and off `G`. -/
def splitMap : X.Ω → RegionCoord X.toNoiseModel G × RegionCoord X.toNoiseModel Gᶜ :=
  fun ω => (toRegion X.toNoiseModel G ω, toRegion X.toNoiseModel Gᶜ ω)

theorem measurable_splitMap : Measurable (splitMap X G) :=
  (measurable_toRegion X.toNoiseModel G).prodMk (measurable_toRegion X.toNoiseModel Gᶜ)

/-- The information of the two regions is read by `splitMap`. -/
theorem le_comap_splitMap :
    X.info G ⊔ X.info Gᶜ ≤ MeasurableSpace.comap (splitMap X G) inferInstance :=
  sup_le
    (fun A hA => MeasurableSpace.measurableSet_comap.2
      ⟨Prod.fst ⁻¹' (show Set (RegionCoord X.toNoiseModel G) from A), measurable_fst hA, rfl⟩)
    fun A hA => MeasurableSpace.measurableSet_comap.2
      ⟨Prod.snd ⁻¹' (show Set (RegionCoord X.toNoiseModel Gᶜ) from A), measurable_snd hA, rfl⟩

/-- An integral of `Z(old), Z(new)` as an integral against the law of the split pair. -/
theorem lintegral_eq_map_split {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {old new : Ω' → X.Ω} {Z : X.Ω → ℝ}
    {ζ : RegionCoord X.toNoiseModel G × RegionCoord X.toNoiseModel Gᶜ → ℝ} (hζ : Measurable ζ)
    (hZ : Z =ᵐ[X.P] ζ ∘ splitMap X G) (hold : MeasurePreserving old P' X.P)
    (hnew : MeasurePreserving new P' X.P) :
    ∫⁻ ω, ENNReal.ofReal ((Z (new ω) - Z (old ω)) ^ 2) ∂P' =
      ∫⁻ q, ENNReal.ofReal ((ζ q.2 - ζ q.1) ^ 2)
        ∂P'.map fun ω => (splitMap X G (old ω), splitMap X G (new ω)) := by
  have hS := measurable_splitMap X G
  have hf : Measurable fun q : _ × _ => ENNReal.ofReal ((ζ q.2 - ζ q.1) ^ 2) :=
    (((hζ.comp measurable_snd).sub (hζ.comp measurable_fst)).pow_const 2).ennreal_ofReal
  have hp : Measurable fun ω => (splitMap X G (old ω), splitMap X G (new ω)) :=
    (hS.comp hold.measurable).prodMk (hS.comp hnew.measurable)
  rw [lintegral_map hf hp]
  refine lintegral_congr_ae ?_
  filter_upwards [hold.quasiMeasurePreserving.ae hZ, hnew.quasiMeasurePreserving.ae hZ] with ω h1 h2
  rw [h1, h2]
  rfl

end Split

/-- **One law of the pair.** Two resamplings of a block given its label have one law, read on the
noise in the block and off it. -/
theorem map_split_eq {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {old₁ new₁ : Ω₁ → X.Ω}
    {old₂ new₂ : Ω₂ → X.Ω} (hdet : Λ.IsDetermined n W L)
    (h₁ : X.IsLabelResampling Λ n W L i z P₁ old₁ new₁)
    (h₂ : X.IsLabelResampling Λ n W L i z P₂ old₂ new₂) :
    P₁.map (fun ω => (splitMap X (block n W L i z) (old₁ ω), splitMap X (block n W L i z) (new₁ ω)))
      = P₂.map fun ω =>
        (splitMap X (block n W L i z) (old₂ ω), splitMap X (block n W L i z) (new₂ ω)) := by
  set G := block n W L i z with hG
  have hS := measurable_splitMap X G
  have hm₁ : Measurable fun ω => (splitMap X G (old₁ ω), splitMap X G (new₁ ω)) :=
    (hS.comp h₁.isBlockCoupling.measurePreserving_old.measurable).prodMk
      (hS.comp h₁.isBlockCoupling.measurePreserving_new.measurable)
  have hm₂ : Measurable fun ω => (splitMap X G (old₂ ω), splitMap X G (new₂ ω)) :=
    (hS.comp h₂.isBlockCoupling.measurePreserving_old.measurable).prodMk
      (hS.comp h₂.isBlockCoupling.measurePreserving_new.measurable)
  set R := RegionCoord X.toNoiseModel G × RegionCoord X.toNoiseModel Gᶜ
  set Rect : Set (Set R) := image2 (· ×ˢ ·) {s | MeasurableSet s} {t | MeasurableSet t} with hRect
  have huniv : univ ∈ Rect := ⟨univ, MeasurableSet.univ, univ, MeasurableSet.univ, by simp⟩
  have hspan : IsCountablySpanning Rect := ⟨fun _ => univ, fun _ => huniv, iUnion_const _⟩
  refine ext_of_generate_finite (image2 (· ×ˢ ·) Rect Rect)
    (generateFrom_eq_prod generateFrom_prod generateFrom_prod hspan hspan).symm
    (isPiSystem_prod.prod isPiSystem_prod) ?_ ?_
  · rintro _ ⟨_, ⟨A, hA, C, hC, rfl⟩, _, ⟨B, hB, D, hD, rfl⟩, rfl⟩
    rw [Measure.map_apply hm₁ ((MeasurableSet.prod hA hC).prod (MeasurableSet.prod hB hD)),
      Measure.map_apply hm₂ ((MeasurableSet.prod hA hC).prod (MeasurableSet.prod hB hD))]
    exact (measure_rect (A := A) (B := B) (C := C) (D := D) hdet h₁ hA hB hC hD).trans
      (measure_rect (A := A) (B := B) (C := C) (D := D) hdet h₂ hA hB hC hD).symm
  · rw [Measure.map_apply hm₁ MeasurableSet.univ, Measure.map_apply hm₂ MeasurableSet.univ]
    simp

/-- **`E (Z^G − Z)²` is determined**, for `Z` almost surely equal to an integrable function
determined by the noise in some set: it is the same for all the resamplings of a block given its
label. -/
theorem lintegral_labelResampling_eq {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {old₁ new₁ : Ω₁ → X.Ω} {old₂ new₂ : Ω₂ → X.Ω} (hdet : Λ.IsDetermined n W L)
    (h₁ : X.IsLabelResampling Λ n W L i z P₁ old₁ new₁)
    (h₂ : X.IsLabelResampling Λ n W L i z P₂ old₂ new₂) {U : Set (Pt m)} {Z Z' : X.Ω → ℝ}
    (hZ'm : Measurable[X.info U] Z') (hZi : Integrable Z' X.P) (hZZ' : Z =ᵐ[X.P] Z') :
    ∫⁻ ω, ENNReal.ofReal ((Z (new₁ ω) - Z (old₁ ω)) ^ 2) ∂P₁ =
      ∫⁻ ω, ENNReal.ofReal ((Z (new₂ ω) - Z (old₂ ω)) ^ 2) ∂P₂ := by
  set G := block n W L i z with hG
  have hGm : MeasurableSet G := measurableSet_block n W L i z
  have hGfr : volume (frontier G) = 0 := volume_frontier_block n W L i z
  -- the pieces `G`, `Gᶜ`
  let T : ℕ → Set (Pt m) := fun k => if k = 0 then G else if k = 1 then Gᶜ else ∅
  have hT : ∀ k, MeasurableSet (T k) := fun k => by
    simp only [T]
    split_ifs
    exacts [hGm, hGm.compl, MeasurableSet.empty]
  have hTfr : ∀ k, volume (frontier (T k)) = 0 := fun k => by
    simp only [T]
    split_ifs
    exacts [hGfr, by rwa [frontier_compl], by simp]
  have hTd : Pairwise (Function.onFun Disjoint T) := by
    have hc : ∀ {k : ℕ}, 2 ≤ k → T k = ∅ := fun {k} hk => by
      have h₀ : k ≠ 0 := by omega
      have h₁ : k ≠ 1 := by omega
      simp [T, h₀, h₁]
    rintro a b hab
    simp only [Function.onFun]
    match a, b, hab with
    | 0, 0, h => exact absurd rfl h
    | 0, 1, _ => simpa [T] using disjoint_compl_right
    | 1, 0, _ => simpa [T] using disjoint_compl_left
    | 1, 1, h => exact absurd rfl h
    | a + 2, _, _ => rw [hc (by omega)]; exact disjoint_bot_left
    | _, b + 2, _ => rw [hc (by omega : 2 ≤ b + 2)]; exact disjoint_bot_right
  have hU : U ⊆ ⋃ k, T k := fun x _ => by
    by_cases hx : x ∈ G
    · exact mem_iUnion.2 ⟨0, by simpa [T] using hx⟩
    · exact mem_iUnion.2 ⟨1, by simpa [T] using hx⟩
  obtain ⟨Z'', hZ''m, hZ'Z''⟩ :=
    exists_stronglyMeasurable_iSup_ae_eq X.toNoiseModel hT hTfr hTd hU hZ'm hZi
  have hMle : (⨆ k, X.info (T k)) ≤ X.info G ⊔ X.info Gᶜ := iSup_le fun k => by
    simp only [T]
    split_ifs
    · exact le_sup_left
    · exact le_sup_right
    · exact (X.info_mono (empty_subset _)).trans le_sup_left
  have hZ''S : Measurable[MeasurableSpace.comap (splitMap X G) inferInstance] Z'' :=
    hZ''m.measurable.mono (hMle.trans (le_comap_splitMap X G)) le_rfl
  obtain ⟨ζ, hζm, hζ⟩ := hZ''S.exists_eq_measurable_comp
  have hZζ : Z =ᵐ[X.P] ζ ∘ splitMap X G := hZZ'.trans (hZ'Z''.trans (EventuallyEq.of_eq hζ))
  rw [lintegral_eq_map_split X G hζm hZζ h₁.isBlockCoupling.measurePreserving_old
      h₁.isBlockCoupling.measurePreserving_new,
    lintegral_eq_map_split X G hζm hZζ h₂.isBlockCoupling.measurePreserving_old
      h₂.isBlockCoupling.measurePreserving_new, map_split_eq hdet h₁ h₂]

end IsotropicVariance.Paper.Proofs.Residual
