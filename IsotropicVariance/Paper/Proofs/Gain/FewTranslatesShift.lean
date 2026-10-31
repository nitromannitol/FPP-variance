/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.FewTranslatesJensen
public import IsotropicVariance.Paper.Proofs.Gain.Translation
public import IsotropicVariance.Infra.Measurability.MinimizerMeasurable

/-!
# Lemma `lem:fewtranslates`: stationarity of the resampling with `σ_G` constant

The proof of Lemma `lem:fewtranslates`: "the translation by `−mL(nQ_n)^{1/2}e₂` maps `F_m` to `F`
and `G` to such a translate", and "by stationarity, `eq:rewardmoment` holds also for `F_m`".

The joint law `Setting.blockResampling` of all the blocks is not moved to itself by a translation,
but the bound `eq:rewardmoment` only reads the pair of the old noise and of the new noise of one
block. With `σ_G` constant that pair has the law `P ⊗ P[· | info Gᶜ]`, and a proper rigid motion `g`
carries it to the law of the block `g '' G`.

* `NoiseModel.resampleKernel_act_ae_eq`: the conditional law moves with the noise.
* `NoiseModel.map_act_compProd_resampleKernel`: **the law of the pair moves with the noise.**
* `Setting.map_act_botResampling`: the same for the resamplings of two blocks.
* `lintegral_sq_act_botResampling`: the energy of `Z ∘ act g` for `G` is that of `Z` for `g '' G`.
* `tsum_lintegral_F_shift_bot`: **the sum over the blocks of the energies of `F_m` is that of `F`.**
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper

open Proofs.Resampling Proofs.Gain

variable {m : ℕ}

namespace NoiseModel

variable (N : NoiseModel.{u} m)

/-- **The conditional law moves with the noise**: for a proper rigid motion `g`,
`P[act g ∈ B | info Gᶜ](ω) = P[B | info (g '' G)ᶜ](act g ω)`. -/
theorem resampleKernel_act_ae_eq {g : Pt m ≃ᵃⁱ[ℝ] Pt m} (hg : IsProperRigidMotion g)
    (G : Set (Pt m)) {B : Set N.Ω} (hB : MeasurableSet B) :
    ∀ᵐ ω ∂N.P, N.resampleKernel G ⊥ ω (N.act g ⁻¹' B) =
      N.resampleKernel (g '' G) ⊥ (N.act g ω) B := by
  have hact := N.measurePreserving_act g hg
  have hle : N.info Gᶜ ⊔ ⊥ ≤ N.measurableSpace := N.info_compl_sup_le G bot_le
  have hle' : N.info (g '' G)ᶜ ⊔ ⊥ ≤ N.measurableSpace := N.info_compl_sup_le (g '' G) bot_le
  have hcomap : (N.info (g '' G)ᶜ ⊔ ⊥).comap (N.act g) = N.info Gᶜ ⊔ ⊥ := by
    rw [← image_compl_eq g.bijective, sup_bot_eq, sup_bot_eq, N.comap_info_act g hg]
  have hκ' : Measurable[N.info (g '' G)ᶜ ⊔ ⊥] fun ω => N.resampleKernel (g '' G) ⊥ ω B := by
    simp_rw [N.resampleKernel_apply (g '' G) (σ := ⊥) bot_le]
    exact measurable_condExpKernel hB
  have hm : Measurable[N.info Gᶜ ⊔ ⊥] fun ω => N.resampleKernel (g '' G) ⊥ (N.act g ω) B := by
    refine hκ'.comp (Measurable.of_comap_le ?_)
    exact hcomap.le
  have h := condExpKernel_ae_eq_of_setLIntegral (P := N.P) hle (hact.measurable hB) hm ?_
  · filter_upwards [h] with ω hω
    rw [N.resampleKernel_apply G bot_le, hω]
  · intro T hT
    rw [← hcomap] at hT
    obtain ⟨S, hS, rfl⟩ := hT
    have hS' := hle' S hS
    rw [hact.setLIntegral_comp_preimage hS' (hκ'.mono hle' le_rfl),
      ← preimage_inter, hact.measure_preimage (hS'.inter hB).nullMeasurableSet]
    exact setLIntegral_kernel hle' (N.resampleKernel_apply (g '' G) bot_le) hS hB

/-- **The law of the pair moves with the noise**: a proper rigid motion `g` carries the law
`P ⊗ P[· | info Gᶜ]` of the old and new noise of `G` to that of `g '' G`. -/
theorem map_act_compProd_resampleKernel {g : Pt m ≃ᵃⁱ[ℝ] Pt m} (hg : IsProperRigidMotion g)
    (G : Set (Pt m)) :
    (N.P ⊗ₘ N.resampleKernel G ⊥).map (Prod.map (N.act g) (N.act g)) =
      N.P ⊗ₘ N.resampleKernel (g '' G) ⊥ := by
  have hact := N.measurePreserving_act g hg
  have hpm : Measurable (Prod.map (N.act g) (N.act g)) := hact.measurable.prodMap hact.measurable
  refine Measure.ext_prod fun {A B} hA hB => ?_
  have e : Prod.map (N.act g) (N.act g) ⁻¹' (A ×ˢ B) = (N.act g ⁻¹' A) ×ˢ (N.act g ⁻¹' B) := rfl
  rw [Measure.map_apply hpm (hA.prod hB), e, Measure.compProd_apply_prod
    (hact.measurable hA) (hact.measurable hB), Measure.compProd_apply_prod hA hB,
    ← hact.setLIntegral_comp_preimage hA (Kernel.measurable_coe _ hB)]
  exact lintegral_congr_ae (ae_restrict_of_ae (N.resampleKernel_act_ae_eq hg G hB))

end NoiseModel

namespace Setting

variable (X : Setting.{u} m) (n W : ℝ) (L : ℕ)

/-- With `σ_G` constant, the pair of the old noise and the new noise of `c` has the law
`P ⊗ P[· | info Gᶜ]`. -/
theorem map_botResampling (c : BlockIdx m) :
    (X.botResampling n W L).map (fun p => (p.1, p.2 c)) =
      X.P ⊗ₘ X.resampleKernel (block n W L c.1 c.2) ⊥ :=
  X.map_old_new _ _ c

/-- **Stationarity of the resampling**: if a proper rigid motion `g` maps the block `c` onto the
block `c'`, it carries the old and new noise of `c` to the law of those of `c'`. -/
theorem map_act_botResampling {g : Pt m ≃ᵃⁱ[ℝ] Pt m} (hg : IsProperRigidMotion g)
    {c c' : BlockIdx m} (hG : g '' block n W L c.1 c.2 = block n W L c'.1 c'.2) :
    (X.botResampling n W L).map (fun p => (X.act g p.1, X.act g (p.2 c))) =
      (X.botResampling n W L).map (fun p => (p.1, p.2 c')) := by
  have hact := X.measurePreserving_act g hg
  have hm : Measurable fun p : X.Ω × (BlockIdx m → X.Ω) => (p.1, p.2 c) :=
    measurable_fst.prodMk ((measurable_pi_apply c).comp measurable_snd)
  have hpm : Measurable (Prod.map (X.act g) (X.act g)) := hact.measurable.prodMap hact.measurable
  have e : (fun p : X.Ω × (BlockIdx m → X.Ω) => (X.act g p.1, X.act g (p.2 c))) =
      Prod.map (X.act g) (X.act g) ∘ fun p => (p.1, p.2 c) := rfl
  rw [e, ← Measure.map_map hpm hm, X.map_botResampling, X.map_botResampling,
    X.map_act_compProd_resampleKernel hg, hG]

end Setting

namespace Proofs.Gain

variable (X : Setting.{u} m) {n W : ℝ} {L : ℕ}

/-- **The energy of a moved function**: if a proper rigid motion `g` maps the block `c` onto the
block `c'`, the energy of `Z ∘ act g` for `c` is that of `Z` for `c'`. -/
theorem lintegral_sq_act_botResampling {g : Pt m ≃ᵃⁱ[ℝ] Pt m} (hg : IsProperRigidMotion g)
    {c c' : BlockIdx m} (hG : g '' block n W L c.1 c.2 = block n W L c'.1 c'.2) {Z : X.Ω → ℝ}
    (hZ : AEMeasurable Z X.P) :
    ∫⁻ p, ENNReal.ofReal ((Z (X.act g (p.2 c)) - Z (X.act g p.1)) ^ 2) ∂X.botResampling n W L =
      ∫⁻ p, ENNReal.ofReal ((Z (p.2 c') - Z p.1) ^ 2) ∂X.botResampling n W L := by
  have hact := X.measurePreserving_act g hg
  have hold : MeasurePreserving Prod.fst (X.botResampling n W L) X.P :=
    X.measurePreserving_old _ _
  have hnew : ∀ c : BlockIdx m, MeasurePreserving (fun p : X.Ω × (BlockIdx m → X.Ω) => p.2 c)
      (X.botResampling n W L) X.P := fun c =>
    X.measurePreserving_new (σ := (X.botInfo n W L).1) bot_le
  have hmk := hZ.ae_eq_mk
  have hZ' := hZ.measurable_mk
  set H : X.Ω × X.Ω → ℝ≥0∞ := fun q => ENNReal.ofReal ((hZ.mk Z q.2 - hZ.mk Z q.1) ^ 2) with hH
  have hHm : Measurable H :=
    (((hZ'.comp measurable_snd).sub (hZ'.comp measurable_fst)).pow_const 2).ennreal_ofReal
  have hm₁ : Measurable fun p : X.Ω × (BlockIdx m → X.Ω) => (X.act g p.1, X.act g (p.2 c)) :=
    (hact.measurable.comp measurable_fst).prodMk
      (hact.measurable.comp ((measurable_pi_apply c).comp measurable_snd))
  have hm₂ : Measurable fun p : X.Ω × (BlockIdx m → X.Ω) => (p.1, p.2 c') :=
    measurable_fst.prodMk ((measurable_pi_apply c').comp measurable_snd)
  have e₁ : ∫⁻ p, ENNReal.ofReal ((Z (X.act g (p.2 c)) - Z (X.act g p.1)) ^ 2)
      ∂X.botResampling n W L = ∫⁻ p, H (X.act g p.1, X.act g (p.2 c)) ∂X.botResampling n W L := by
    refine lintegral_congr_ae ?_
    filter_upwards [(hact.comp hold).quasiMeasurePreserving.ae hmk,
      (hact.comp (hnew c)).quasiMeasurePreserving.ae hmk] with p h₁ h₂
    simp only [hH]
    rw [← show Z (X.act g p.1) = hZ.mk Z (X.act g p.1) from h₁,
      ← show Z (X.act g (p.2 c)) = hZ.mk Z (X.act g (p.2 c)) from h₂]
  have e₂ : ∫⁻ p, ENNReal.ofReal ((Z (p.2 c') - Z p.1) ^ 2) ∂X.botResampling n W L =
      ∫⁻ p, H (p.1, p.2 c') ∂X.botResampling n W L := by
    refine lintegral_congr_ae ?_
    filter_upwards [hold.quasiMeasurePreserving.ae hmk,
      (hnew c').quasiMeasurePreserving.ae hmk] with p h₁ h₂
    simp only [hH]
    rw [← show Z p.1 = hZ.mk Z p.1 from h₁, ← show Z (p.2 c') = hZ.mk Z (p.2 c') from h₂]
  rw [e₁, e₂, ← lintegral_map hHm hm₁, ← lintegral_map hHm hm₂, X.map_act_botResampling n W L hg hG]

/-- The energy of `F_j` for the block `(i, z + j L e₀)` is that of `F` for the block `(i, z)`. -/
theorem lintegral_F_shift_bot (hm : 1 ≤ m) {b : ℝ} (hb : X.IsUpperBound b) (K : ℕ) (hn : 0 < n)
    (j i : ℕ) (z : Fin m → ℤ) :
    ∫⁻ p, ENNReal.ofReal ((X.F b K n (((j : ℝ) * L * W) • e₂ m) (p.2 (i, z + blockShift hm j L)) -
        X.F b K n (((j : ℝ) * L * W) • e₂ m) p.1) ^ 2) ∂X.botResampling n W L =
      ∫⁻ p, ENNReal.ofReal ((X.F b K n 0 (p.2 (i, z)) - X.F b K n 0 p.1) ^ 2)
        ∂X.botResampling n W L := by
  rw [F_shift_eq]
  exact lintegral_sq_act_botResampling X (isProperRigidMotion_shiftBy _)
    (c := (i, z + blockShift hm j L)) (c' := (i, z)) (image_shiftBy_block_add hm n W L i j z)
    (Infra.Slab.aemeasurable_F X hb hn 0 K)

/-- **The sum over the blocks of the energies of `F_j` is that of `F`** (proof of Lemma
`lem:fewtranslates`, "by stationarity"): the sum is reindexed by `z ↦ z + j L e₀`. -/
theorem tsum_lintegral_F_shift_bot (hm : 1 ≤ m) {b : ℝ} (hb : X.IsUpperBound b) {K : ℕ}
    (hn : 0 < n) (o : Fin K → Fin m → Fin L) (j : ℕ) :
    ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
        ∫⁻ p, ENNReal.ofReal ((X.F b K n (((j : ℝ) * L * W) • e₂ m)
            (p.2 ((i : ℕ), (z : Fin m → ℤ))) -
          X.F b K n (((j : ℝ) * L * W) • e₂ m) p.1) ^ 2) ∂X.botResampling n W L =
      ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
        ∫⁻ p, ENNReal.ofReal ((X.F b K n 0 (p.2 ((i : ℕ), (z : Fin m → ℤ))) -
          X.F b K n 0 p.1) ^ 2) ∂X.botResampling n W L := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (blockIndexShift hm j L (o i)).tsum_eq]
  refine tsum_congr fun z => ?_
  exact lintegral_F_shift_bot X hm hb K hn j i z

end Proofs.Gain

end IsotropicVariance.Paper
