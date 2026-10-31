/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.CoreLoad
public import IsotropicVariance.Paper.Proofs.LabelResidual.BadMoment

/-!
# The near-pair moment at a good offset

The actual normalized reward `Setting.Y` is controlled by the squared core response off the
old localization event, and by its `16d` moment on that event. Holder gives its `4d` moment
with the small profile error plus the `3/4` power of the event probability, as in the proof of
Lemma `lem:residual`. The remaining offset average uses the count in `Offsets`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.LabelResidual

variable {m : ℕ} {X : Setting.{u} m}

/-- The reward of a common-old family is a.e. measurable. -/
theorem aemeasurable_Y {b A ℓ : ℝ} {K i L : ℕ}
    (hb : X.IsUpperBound b) (hn : 0 ≤ ℓ / K) (hW : 0 ≤ W K A (ℓ / K))
    (o : Fin m → Fin L)
    (fam : X.BlockCouplingFamily (ℓ / K) (W K A (ℓ / K)) L i {z | IsBlockIndex L o z})
    (g₀ : {z : Fin m → ℤ | IsBlockIndex L o z}) (j k : Fin m → ℤ) :
    AEMeasurable (fun ω => X.Y b (ℓ / K) (W K A (ℓ / K)) (Q K A (ℓ / K)) i j k
      {z | IsBlockIndex L o z} fam.old fam.new ω) fam.P' := by
  unfold Setting.Y
  split_ifs
  · apply AEMeasurable.tsum
    intro z
    exact ((((Responses.aemeasurable_blockGain hb hn hW i j k
      (fam.isBlockCoupling g₀ g₀.2).measurePreserving_old
      (fam.isBlockCoupling z z.2).measurePreserving_new).div_const _).pow_const 2).ennreal_ofReal)
  · exact aemeasurable_const

/-- At a good offset, the `4d` reward moment is small apart from the old localization event. -/
theorem lintegral_Y_pow_le_of_good_offset {Λ : X.LabelFamily} {b A ℓ ε : ℝ} {K i : ℕ}
    {L : ℕ+} (hi : i < K) (hε : 0 ≤ ε) (hprof : Gain.LabelProfileBound X b K A ℓ L Λ ε)
    (hb : X.IsUpperBound b) (hn : 0 ≤ ℓ / K) (hW : 1 ≤ W K A (ℓ / K))
    (hQ : 0 < Q K A (ℓ / K)) (o : Fin m → Fin (L : ℕ)) (g j k : Fin m → ℤ)
    (D : ℝ) (hρ : Real.sqrt m ≤ 2 * Real.sqrt m + 2 + (W K A (ℓ / K))⁻¹ * D)
    (hcore : {y : EuclideanSpace ℝ (Fin m) |
      infDist y (segment ℝ (Responses.transverseIntegerPoint j) (Responses.transverseIntegerPoint k)) ≤
        2 * Real.sqrt m + 2 + (W K A (ℓ / K))⁻¹ * D} ⊆
      OffsetGeometry.groupCore L (Real.sqrt (L : ℕ)) o g)
    (fam : X.BlockCouplingFamily (ℓ / K) (W K A (ℓ / K)) L i {z | IsBlockIndex L o z})
    (heq : ∀ᵐ ω ∂fam.P', Λ.label i (blockLowerIndex L o g) (fam.new (blockLowerIndex L o g) ω) =
      Λ.label i (blockLowerIndex L o g) (fam.old ω))
    {B : Set fam.Ω'} (hB : MeasurableSet B)
    (hcurve : ∀ᵐ ω ∂fam.P', ω ∉ B →
      ∀ u ∈ gridCube (ℓ / K) (W K A (ℓ / K)) 0 i j,
        ∀ v ∈ gridCube (ℓ / K) (W K A (ℓ / K)) 0 (i + 1) k,
        ∀ γ : RectifiableCurve (Pt m),
          IsOneOptimal ((chainSlab (ℓ / K) 0 i).density b (X.ρ (fam.old ω)))
            (chainSlab (ℓ / K) 0 i).set u v γ → ∀ t ∈ Icc (0 : ℝ) 1,
              infDist (γ.toFun t) (segment ℝ u v) ≤ D)
    {M : ℝ≥0∞} (h4p : ∫⁻ ω,
      X.Y b (ℓ / K) (W K A (ℓ / K)) (Q K A (ℓ / K)) i j k
        {z | IsBlockIndex L o z} fam.old fam.new ω ^ (4 * (4 * (m + 1))) ∂fam.P' ≤
          M ^ (4 * (4 * (m + 1)))) :
    ∫⁻ ω, X.Y b (ℓ / K) (W K A (ℓ / K)) (Q K A (ℓ / K)) i j k
        {z | IsBlockIndex L o z} fam.old fam.new ω ^ (4 * (m + 1)) ∂fam.P' ≤
      ENNReal.ofReal ((2 * ε) ^ (8 * (m + 1))) + M ^ (4 * (m + 1)) * fam.P' B ^ (3 / 4 : ℝ) := by
  let g₀ : {z : Fin m → ℤ | IsBlockIndex L o z} :=
    ⟨blockLowerIndex L o g, isBlockIndex_blockLowerIndex L o g⟩
  have hsmall := lintegral_coreResponse_pow_le_of_label_eq hε hprof hi
    (fam.isBlockCoupling g₀ g₀.2).measurePreserving_old
    (fam.isBlockCoupling g₀ g₀.2).measurePreserving_new heq
  have hsmall' : ∫⁻ ω,
      (coreResponse b K A ℓ L i (blockLowerIndex L o g)
        (fam.old ω) (fam.new (blockLowerIndex L o g) ω) ^ 2) ^ (4 * (m + 1)) ∂fam.P' ≤
      ENNReal.ofReal ((2 * ε) ^ (8 * (m + 1))) := by
    simpa only [← pow_mul, show 2 * (4 * (m + 1)) = 8 * (m + 1) by omega] using hsmall
  apply lintegral_pow_le_of_small_off_event
    (aemeasurable_Y hb hn (lt_of_lt_of_le zero_lt_one hW).le o fam g₀ j k) hB
    (4 * (m + 1)) hsmall' h4p
  filter_upwards [ae_Y_le_coreResponse_sq hb hn hW hQ o g j k D hρ hcore fam, hcurve]
    with ω hω hc hωB
  exact hω (hc hωB)

end IsotropicVariance.Paper.Proofs.LabelResidual
