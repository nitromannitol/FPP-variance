/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.BridgeKernel
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import IsotropicVariance.Paper.Proofs.Gain.BridgeGeometry

/-!
# The resamplings of the blocks given their labels

The resamplings of Section `sec:gain`, which do not depend on the
offsets.

A `LabelResamplingData` lives on a probability space in `Type`, while the noise lives in `Type u`.
The pair laws `pairLaw` on `Ω × Ω` are therefore carried to `ℝ` by a Borel embedding of the standard
Borel space `Ω × Ω` (`realLaw`), with a measurable left inverse `pairDecode` giving the old and new
noise.
* `bridgeResampling X Λ hdet i z`: the block resampled given the noise off it and its label.
* `lintegral_realLaw_pairDecode`: the energies of these resamplings are integrals against the pair
  laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Gain.Bridge

open IsotropicVariance.Paper

universe u

/-! ### From `Ω × Ω` to the reals -/

section Transport

variable {m : ℕ} (N : NoiseModel.{u} m)

local instance : Nonempty N.Ω := nonempty_of_isProbabilityMeasure N.P

/-- A measurable left inverse of the Borel embedding of `Ω × Ω` into `ℝ`. -/
noncomputable def pairDecode : ℝ → N.Ω × N.Ω :=
  Function.extend (embeddingReal (N.Ω × N.Ω)) id fun _ => Classical.arbitrary _

/-- The left inverse is measurable. -/
theorem measurable_pairDecode : Measurable (pairDecode N) :=
  (measurableEmbedding_embeddingReal _).measurable_extend measurable_id measurable_const

/-- The left inverse inverts the embedding. -/
theorem pairDecode_embeddingReal (p : N.Ω × N.Ω) : pairDecode N (embeddingReal _ p) = p :=
  (measurableEmbedding_embeddingReal _).injective.extend_apply _ _ p

/-- A law on `Ω × Ω` carried to the reals by the Borel embedding. -/
noncomputable def realLaw (Q : Measure (N.Ω × N.Ω)) : Measure ℝ :=
  Q.map (embeddingReal _)

/-- A probability law carried to the reals is a probability. -/
instance (Q : Measure (N.Ω × N.Ω)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (realLaw N Q) := by
  unfold realLaw
  infer_instance

/-- Decoding carries the law on the reals back to the law on `Ω × Ω`. -/
theorem measurePreserving_pairDecode (Q : Measure (N.Ω × N.Ω)) :
    MeasurePreserving (pairDecode N) (realLaw N Q) Q := by
  refine ⟨measurable_pairDecode N, ?_⟩
  rw [realLaw, Measure.map_map (measurable_pairDecode N) (measurable_embeddingReal _)]
  have : pairDecode N ∘ embeddingReal (N.Ω × N.Ω) = id := funext (pairDecode_embeddingReal N)
  rw [this, Measure.map_id]

end Transport

/-! ### Couplings along measure-preserving maps -/

section Comp

variable {m : ℕ} {X : Setting.{u} m} {G : Set (Pt m)} {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
  [mΩ₂ : MeasurableSpace Ω₂] {P₁ : Measure Ω₁} {Q : Measure Ω₂} {r : Ω₁ → Ω₂}

/-- Independence of two σ-algebras is pulled back by a measure-preserving map. -/
theorem indep_comap_of_measurePreserving (hr : MeasurePreserving r P₁ Q)
    {a b : MeasurableSpace Ω₂} (ha : a ≤ mΩ₂) (hb : b ≤ mΩ₂) (h : Indep a b Q) :
    Indep (a.comap r) (b.comap r) P₁ := by
  rw [Indep_iff] at h ⊢
  intro t₁ t₂ ht₁ ht₂
  let _ : MeasurableSpace Ω₂ := mΩ₂
  obtain ⟨s₁, hs₁, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht₁
  obtain ⟨s₂, hs₂, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht₂
  have h₁ : MeasurableSet[mΩ₂] s₁ := ha s₁ hs₁
  have h₂ : MeasurableSet[mΩ₂] s₂ := hb s₂ hs₂
  rw [← preimage_inter, hr.measure_preimage (h₁.inter h₂).nullMeasurableSet,
    hr.measure_preimage h₁.nullMeasurableSet, hr.measure_preimage h₂.nullMeasurableSet]
  exact h s₁ s₂ hs₁ hs₂

/-- A coupling of `G` composed with a measure-preserving map is a coupling of `G`. -/
theorem isBlockCoupling_comp (hr : MeasurePreserving r P₁ Q) {old new : Ω₂ → X.Ω}
    (h : X.IsBlockCoupling G Q old new) : X.IsBlockCoupling G P₁ (old ∘ r) (new ∘ r) where
  measurePreserving_old := h.measurePreserving_old.comp hr
  measurePreserving_new := h.measurePreserving_new.comp hr
  exchangeable := by
    have hon := h.measurePreserving_old.measurable.prodMk h.measurePreserving_new.measurable
    have hno := h.measurePreserving_new.measurable.prodMk h.measurePreserving_old.measurable
    change P₁.map ((fun q => (old q, new q)) ∘ r) = P₁.map ((fun q => (new q, old q)) ∘ r)
    rw [← Measure.map_map hon hr.measurable, ← Measure.map_map hno hr.measurable, hr.map_eq]
    exact h.exchangeable
  agree_compl A hA := hr.quasiMeasurePreserving.ae (h.agree_compl A hA)
  indep := by
    have hold := h.measurePreserving_old.measurable
    have hnew := h.measurePreserving_new.measurable
    rw [← MeasurableSpace.comap_comp, ← MeasurableSpace.comap_comp, ← MeasurableSpace.comap_comp,
      ← MeasurableSpace.comap_sup]
    exact indep_comap_of_measurePreserving hr
      (sup_le ((MeasurableSpace.comap_mono (X.info_le G)).trans hold.comap_le)
        ((MeasurableSpace.comap_mono (X.info_le G)).trans hnew.comap_le))
      ((MeasurableSpace.comap_mono (X.info_le Gᶜ)).trans hold.comap_le) h.indep

/-- A resampling given a label composed with a measure-preserving map is a resampling given
the label (the fibers of the label being events). -/
theorem isLabelResampling_comp (hr : MeasurePreserving r P₁ Q) {Λ : X.LabelFamily} {n W : ℝ}
    {L i : ℕ} {z : Fin m → ℤ} (hℓ : ∀ v, MeasurableSet (Λ.label i z ⁻¹' {v}))
    {old new : Ω₂ → X.Ω} (h : X.IsLabelResampling Λ n W L i z Q old new) :
    X.IsLabelResampling Λ n W L i z P₁ (old ∘ r) (new ∘ r) where
  isBlockCoupling := isBlockCoupling_comp hr h.isBlockCoupling
  label_eq := hr.quasiMeasurePreserving.ae h.label_eq
  condIndep A B hA hB v := by
    have hold := h.isBlockCoupling.measurePreserving_old.measurable
    have hnew := h.isBlockCoupling.measurePreserving_new.measurable
    have hA' := X.info_le _ A hA
    have hB' := X.info_le _ B hB
    have hm : ∀ S : Set Ω₂, MeasurableSet S → P₁ (r ⁻¹' S) = Q S :=
      fun S hS => hr.measure_preimage hS.nullMeasurableSet
    have hfib := hold (hℓ v)
    rw [show {ω | (old ∘ r) ω ∈ A ∧ (new ∘ r) ω ∈ B ∧ Λ.label i z ((old ∘ r) ω) = v} =
        r ⁻¹' (old ⁻¹' A ∩ new ⁻¹' B ∩ old ⁻¹' (Λ.label i z ⁻¹' {v})) by
          ext ω; simp [and_assoc],
      show {ω | Λ.label i z ((old ∘ r) ω) = v} = r ⁻¹' (old ⁻¹' (Λ.label i z ⁻¹' {v})) by
          ext ω; simp,
      show {ω | (old ∘ r) ω ∈ A ∧ Λ.label i z ((old ∘ r) ω) = v} =
        r ⁻¹' (old ⁻¹' A ∩ old ⁻¹' (Λ.label i z ⁻¹' {v})) by ext ω; simp,
      show {ω | (old ∘ r) ω ∈ B ∧ Λ.label i z ((old ∘ r) ω) = v} =
        r ⁻¹' (old ⁻¹' B ∩ old ⁻¹' (Λ.label i z ⁻¹' {v})) by ext ω; simp,
      hm _ (((hold hA').inter (hnew hB')).inter hfib), hm _ hfib, hm _ ((hold hA').inter hfib),
      hm _ ((hold hB').inter hfib)]
    have := h.condIndep A B hA hB v
    rwa [show {ω | old ω ∈ A ∧ new ω ∈ B ∧ Λ.label i z (old ω) = v} =
        old ⁻¹' A ∩ new ⁻¹' B ∩ old ⁻¹' (Λ.label i z ⁻¹' {v}) by ext ω; simp [and_assoc],
      show {ω | Λ.label i z (old ω) = v} = old ⁻¹' (Λ.label i z ⁻¹' {v}) by ext ω; simp,
      show {ω | old ω ∈ A ∧ Λ.label i z (old ω) = v} =
        old ⁻¹' A ∩ old ⁻¹' (Λ.label i z ⁻¹' {v}) by ext ω; simp,
      show {ω | old ω ∈ B ∧ Λ.label i z (old ω) = v} =
        old ⁻¹' B ∩ old ⁻¹' (Λ.label i z ⁻¹' {v}) by ext ω; simp] at this

end Comp

/-! ### The couplings of the bridge -/

section Data

variable {m : ℕ} (X : Setting.{u} m)

/-- **The resampling of a block** `(i, z)` given its label used for the bridge: the noise in the
block resampled independently given the noise off it and the label, realized on the reals. -/
noncomputable def bridgeResampling (Λ : X.LabelFamily) {n W : ℝ} {L : ℕ}
    (hdet : Λ.IsDetermined n W L) (i : ℕ) (z : Fin m → ℤ) : X.LabelResamplingData Λ n W L i z where
  Ω' := ℝ
  P' := realLaw X.toNoiseModel (pairLaw X.toNoiseModel (block n W L i z) (Λ.label i z))
  old t := (pairDecode X.toNoiseModel t).1
  new t := (pairDecode X.toNoiseModel t).2
  isLabelResampling := isLabelResampling_comp (measurePreserving_pairDecode _ _)
    (fun v => X.info_le _ _ (hdet i z v)) (isLabelResampling_pairLaw X Λ hdet i z)

/-- **The energies of the couplings.** For `Z` almost surely equal to a measurable `Zm`, an
integral of `(Z(old), Z(new))` against a coupling on the reals is the integral of
`(Zm(p.1), Zm(p.2))` against the pair law, when the pair law has the marginals of the noise. -/
theorem lintegral_realLaw_pairDecode (Q : Measure (X.Ω × X.Ω))
    (hold : MeasurePreserving Prod.fst Q X.P) (hnew : MeasurePreserving Prod.snd Q X.P)
    {Z Zm : X.Ω → ℝ} (hZm : Measurable Zm) (hZ : Z =ᵐ[X.P] Zm) {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ t, F (Z (pairDecode X.toNoiseModel t).1, Z (pairDecode X.toNoiseModel t).2)
        ∂realLaw X.toNoiseModel Q =
      ∫⁻ p, F (Zm p.1, Zm p.2) ∂Q := by
  have hr := measurePreserving_pairDecode X.toNoiseModel Q
  have h1 : (fun t => Z (pairDecode X.toNoiseModel t).1) =ᵐ[realLaw X.toNoiseModel Q]
      fun t => Zm (pairDecode X.toNoiseModel t).1 :=
    (hold.comp hr).quasiMeasurePreserving.ae_eq_comp hZ
  have h2 : (fun t => Z (pairDecode X.toNoiseModel t).2) =ᵐ[realLaw X.toNoiseModel Q]
      fun t => Zm (pairDecode X.toNoiseModel t).2 :=
    (hnew.comp hr).quasiMeasurePreserving.ae_eq_comp hZ
  have h3 : (fun t => F (Z (pairDecode X.toNoiseModel t).1, Z (pairDecode X.toNoiseModel t).2))
      =ᵐ[realLaw X.toNoiseModel Q]
      fun t => F (Zm (pairDecode X.toNoiseModel t).1, Zm (pairDecode X.toNoiseModel t).2) := by
    filter_upwards [h1, h2] with t h1t h2t
    rw [h1t, h2t]
  rw [lintegral_congr_ae h3]
  exact hr.lintegral_comp (hF.comp ((hZm.comp measurable_fst).prodMk (hZm.comp measurable_snd)))

end Data

end IsotropicVariance.Paper.Proofs.Gain.Bridge
