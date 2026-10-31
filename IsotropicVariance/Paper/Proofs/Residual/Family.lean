/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.CommonCouplings
public import IsotropicVariance.Paper.Proofs.Resampling.Coupling
import IsotropicVariance.Infra.Measurability.SlabVersion
import IsotropicVariance.Paper.Proofs.BlockReplacement.Rewards

/-!
# The resampling of the blocks as a family of couplings

The proof of equation `eq:residual` is written with the concrete
resampling `X.blockResampling`, with `σ_G = X_G` (`labelInfo`). The lemmas of
`IsotropicVariance.Paper.Proofs.LabelResidual` take a `Setting.BlockCouplingFamily`, whose
probability space is in `Type`, while the noise is in `Type u`. So the law of the resampling is
carried to the reals by a Borel embedding (`realResampling`), which keeps the full joint law, and
decoded back (`resamplingFamily`). The embedding is a measurable embedding, so integrals transfer
with no measurability assumption (`lintegral_realResampling`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Residual

open LabelResidual

/-- A family of functions indexed by a countable type, evaluated at a random index. -/
theorem aemeasurable_comp_index {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] {μ : Measure Ω} {ι : Ω → V} (hι : AEMeasurable ι μ)
    {F : V → Ω → ℝ≥0∞} (hF : ∀ p, AEMeasurable (F p) μ) :
    AEMeasurable (fun ω => F (ι ω) ω) μ := by
  have hm : Measurable fun q : Ω × V => (hF q.2).mk (F q.2) q.1 :=
    measurable_from_prod_countable_left fun p => (hF p).measurable_mk
  refine ⟨fun ω => (hF (hι.mk ι ω)).mk _ ω, hm.comp (measurable_id.prodMk hι.measurable_mk), ?_⟩
  filter_upwards [hι.ae_eq_mk, ae_all_iff.2 fun p => (hF p).ae_eq_mk] with ω h1 h2
  rw [h1]
  exact h2 _

variable {m : ℕ} (X : Setting.{u} m) {n W : ℝ} {L : ℕ}

local instance : Nonempty X.Ω := nonempty_of_isProbabilityMeasure X.P

/-- The choice `σ_G = X_G` of Lemma `lem:residual`. -/
def labelInfo (Λ : X.LabelFamily) (hdet : Λ.IsDetermined n W L) : X.BlockInfo n W L :=
  ⟨fun p => Λ.sigma p.1 p.2, fun p => Λ.sigma_le hdet p.1 p.2⟩

/-- The law of the resampling, carried to the reals. -/
noncomputable def realResampling (σ : X.BlockInfo n W L) : Measure ℝ :=
  (X.blockResampling n W L σ.1).map (embeddingReal (X.Ω × (BlockIdx m → X.Ω)))

instance (σ : X.BlockInfo n W L) : IsProbabilityMeasure (realResampling X σ) := by
  unfold realResampling
  infer_instance

/-- Decoding carries the law on the reals back to the law of the resampling. -/
theorem measurePreserving_decode (σ : X.BlockInfo n W L) :
    MeasurePreserving (decodeReal (E := X.Ω × (BlockIdx m → X.Ω))) (realResampling X σ)
      (X.blockResampling n W L σ.1) := by
  refine ⟨measurable_decodeReal, ?_⟩
  rw [realResampling, Measure.map_map measurable_decodeReal (measurable_embeddingReal _)]
  have : decodeReal (E := X.Ω × (BlockIdx m → X.Ω)) ∘
      embeddingReal (X.Ω × (BlockIdx m → X.Ω)) = id := funext decodeReal_embeddingReal
  rw [this, Measure.map_id]

/-- **Integrals transfer**, with no measurability assumption. -/
theorem lintegral_realResampling (σ : X.BlockInfo n W L)
    (f : X.Ω × (BlockIdx m → X.Ω) → ℝ≥0∞) :
    ∫⁻ t, f (decodeReal t) ∂realResampling X σ = ∫⁻ p, f p ∂X.blockResampling n W L σ.1 := by
  rw [realResampling, (measurableEmbedding_embeddingReal _).lintegral_map]
  simp only [decodeReal_embeddingReal]

/-- The resampling of the blocks of a slab, as a family of couplings on the reals. -/
noncomputable def resamplingFamily (σ : X.BlockInfo n W L) (i : ℕ) (blocks : Set (Fin m → ℤ)) :
    X.BlockCouplingFamily n W L i blocks where
  Ω' := ℝ
  P' := realResampling X σ
  old t := (decodeReal t : X.Ω × (BlockIdx m → X.Ω)).1
  new z t := (decodeReal t : X.Ω × (BlockIdx m → X.Ω)).2 (i, z)
  isBlockCoupling z _ := Gain.Bridge.isBlockCoupling_comp (measurePreserving_decode X σ)
    (X.isBlockCoupling_blockResampling n W L i z (σ.2 (i, z)))

/-- The new noise of a block of the family has the label of the old noise. -/
theorem ae_label_eq (Λ : X.LabelFamily) (hdet : Λ.IsDetermined n W L) (i : ℕ)
    (blocks : Set (Fin m → ℤ)) (z : Fin m → ℤ) :
    ∀ᵐ t ∂(resamplingFamily X (labelInfo X Λ hdet) i blocks).P',
      Λ.label i z ((resamplingFamily X (labelInfo X Λ hdet) i blocks).new z t) =
        Λ.label i z ((resamplingFamily X (labelInfo X Λ hdet) i blocks).old t) :=
  (measurePreserving_decode X (labelInfo X Λ hdet)).quasiMeasurePreserving.ae
    (X.isLabelResampling_blockResampling Λ hdet i z).label_eq

/-- The sum over the slabs of the selected rewards of the family is the expectation of equation
`eq:blocksum`. -/
theorem sum_lintegral_selected {b : ℝ} (hb : X.IsUpperBound b) (hn : 0 < n) (hW : 0 < W)
    (Qn : ℝ) {K : ℕ} (σ : X.BlockInfo n W L) (blocks : Fin K → Set (Fin m → ℤ)) :
    ∑ i : Fin K, ∫⁻ t, X.Y b n W Qn i
        (X.J b K n W 0 ((resamplingFamily X σ i (blocks i)).old t) i.castSucc)
        (X.J b K n W 0 ((resamplingFamily X σ i (blocks i)).old t) i.succ) (blocks i)
        (resamplingFamily X σ i (blocks i)).old (resamplingFamily X σ i (blocks i)).new t
        ∂(resamplingFamily X σ i (blocks i)).P' =
      ∫⁻ p, ∑ i : Fin K, X.Y b n W Qn i (X.J b K n W 0 p.1 i.castSucc)
        (X.J b K n W 0 p.1 i.succ) (blocks i) Prod.fst
        (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 ((i : ℕ), z)) p
        ∂X.blockResampling n W L σ.1 := by
  have hold : MeasurePreserving (fun t => (decodeReal t : X.Ω × (BlockIdx m → X.Ω)).1)
      (realResampling X σ) X.P :=
    (X.measurePreserving_old (fun p : BlockIdx m => block n W L p.1 p.2) σ.1).comp
      (measurePreserving_decode X σ)
  have hm : ∀ i : Fin K, AEMeasurable (fun t => X.Y b n W Qn i
      (X.J b K n W 0 (decodeReal t : X.Ω × (BlockIdx m → X.Ω)).1 i.castSucc)
      (X.J b K n W 0 (decodeReal t : X.Ω × (BlockIdx m → X.Ω)).1 i.succ) (blocks i)
      (resamplingFamily X σ i (blocks i)).old (resamplingFamily X σ i (blocks i)).new t)
      (realResampling X σ) := fun i => by
    have hι := ((Infra.Slab.aemeasurable_J X hb hn 0 K W i.castSucc).prodMk
      (Infra.Slab.aemeasurable_J X hb hn 0 K W i.succ)).comp_quasiMeasurePreserving
        hold.quasiMeasurePreserving
    exact aemeasurable_comp_index hι (F := fun q => X.Y b n W Qn i q.1 q.2 (blocks i)
      (resamplingFamily X σ i (blocks i)).old (resamplingFamily X σ i (blocks i)).new)
      fun q => BlockReplacement.aemeasurable_Y X hb hn hW Qn i (blocks i) _ q.1 q.2
  refine Eq.trans (lintegral_finsetSum' Finset.univ fun i _ => hm i).symm ?_
  exact lintegral_realResampling X σ fun p => ∑ i : Fin K, X.Y b n W Qn i
    (X.J b K n W 0 p.1 i.castSucc) (X.J b K n W 0 p.1 i.succ) (blocks i) Prod.fst
    (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 ((i : ℕ), z)) p

end IsotropicVariance.Paper.Proofs.Residual
