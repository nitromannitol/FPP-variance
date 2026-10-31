/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.NearMoment
public import IsotropicVariance.Paper.Proofs.LabelResidual.AverageMoments
public import IsotropicVariance.Paper.Proofs.LabelResidual.TubeOffsets
public import IsotropicVariance.Paper.Proofs.LabelResidual.LocalizationEvent
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The actual near-pair reward moment averaged over offsets

At every good offset, all contributing cells belong to one label core on the old localization
event's complement. The core profile bound and the correct old/new laws therefore give a
small moment. At bad offsets only the coarse moment is used. This is the offset-averaging
step of the proof of Lemma `lem:residual`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.LabelResidual

variable {m : ℕ} {X : Setting.{u} m}

/-- The averaged `4d` moment is controlled by the profile error, a Gaussian localization tail,
and the explicit fraction of offsets that fail to contain the index tube in one core. -/
theorem average_lintegral_Y_pow_le {Λ : X.LabelFamily} {b A ℓ ε Cr R : ℝ} {K i : ℕ}
    {L : ℕ+} (hi : i < K) (hε : 0 ≤ ε) (hprof : Gain.LabelProfileBound X b K A ℓ L Λ ε)
    (hb : X.IsUpperBound b) (hn : 0 ≤ ℓ/K) (hW : 1 ≤ W K A (ℓ/K))
    (hQ : 0 < Q K A (ℓ/K)) (hCr : 0 < Cr) (hR : 0 ≤ R) (j k : Fin m → ℤ)
    (hloc : Cited.IsOs X.P 2 Cr
      (Responses.pairLocalizationRadius X b (ℓ/K) (W K A (ℓ/K)) i j k))
    (fam : (o : Fin m → Fin (L : ℕ)) →
      X.BlockCouplingFamily (ℓ/K) (W K A (ℓ/K)) L i {z | IsBlockIndex L o z})
    (heq : ∀ o (z : {z : Fin m → ℤ | IsBlockIndex L o z}),
      ∀ᵐ ω ∂(fam o).P', Λ.label i z ((fam o).new z ω) = Λ.label i z ((fam o).old ω))
    {M : ℝ≥0∞}
    (h4p : ∀ o, ∫⁻ ω, X.Y b (ℓ/K) (W K A (ℓ/K)) (Q K A (ℓ/K)) i j k
      {z | IsBlockIndex L o z} (fam o).old (fam o).new ω ^ (16*(m+1)) ∂(fam o).P' ≤
        M ^ (16*(m+1))) :
    (Fintype.card (Fin m → Fin (L : ℕ)) : ℝ≥0∞)⁻¹ *
      ∑ o : Fin m → Fin (L : ℕ), ∫⁻ ω,
        X.Y b (ℓ/K) (W K A (ℓ/K)) (Q K A (ℓ/K)) i j k
          {z | IsBlockIndex L o z} (fam o).old (fam o).new ω ^ (4*(m+1)) ∂(fam o).P' ≤
    ENNReal.ofReal ((2*ε)^(8*(m+1))) + M^(4*(m+1)) *
      (ENNReal.ofReal (2*Real.exp (-(R/Cr)^2)) +
        ENNReal.ofReal ((m : ℝ) * (zNorm (k-j) + 2*(2*Real.sqrt m+2+R) +
          2*Real.sqrt (L : ℕ) + 2) / (L : ℝ))) ^ (3/4 : ℝ) := by
  classical
  let _ : Nonempty (Fin m → Fin (L : ℕ)) := ⟨fun _ => ⟨0,L.pos⟩⟩
  let ρ : ℝ := 2*Real.sqrt m+2+R
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  let bad := OffsetGeometry.badOffsets L (Real.sqrt (L : ℕ)) (indexTube j k ρ)
  let x : (Fin m → Fin (L : ℕ)) → ℝ≥0∞ := fun o =>
    ∫⁻ ω, X.Y b (ℓ/K) (W K A (ℓ/K)) (Q K A (ℓ/K)) i j k
      {z | IsBlockIndex L o z} (fam o).old (fam o).new ω ^ (4*(m+1)) ∂(fam o).P'
  have hcoarse (o : Fin m → Fin (L : ℕ)) : x o ≤ M^(4*(m+1)) := by
    let z₀ : {z : Fin m → ℤ | IsBlockIndex L o z} :=
      ⟨Responses.cellBlockIndex L o 0, Responses.isBlockIndex_cellBlockIndex L o 0⟩
    have H := lintegral_indicator_pow_le (aemeasurable_Y hb hn (by linarith) o (fam o) z₀ j k)
      MeasurableSet.univ (4*(m+1)) (by simpa only [show 4*(4*(m+1)) = 16*(m+1) by omega] using h4p o)
    simpa using H
  have hgood (o : Fin m → Fin (L : ℕ)) (ho : o ∉ bad) :
      x o ≤ ENNReal.ofReal ((2*ε)^(8*(m+1))) +
        M^(4*(m+1)) * ENNReal.ofReal (2*Real.exp (-(R/Cr)^2))^(3/4 : ℝ) := by
    have hex : ∃ g, indexTube j k ρ ⊆
        OffsetGeometry.groupCore L (Real.sqrt (L : ℕ)) o g := by
      simpa only [bad, OffsetGeometry.badOffsets, Finset.mem_filter, Finset.mem_univ,
        true_and, not_not] using ho
    obtain ⟨g,hg⟩ := hex
    let z₀ : {z : Fin m → ℤ | IsBlockIndex L o z} :=
      ⟨blockLowerIndex L o g, isBlockIndex_blockLowerIndex L o g⟩
    obtain ⟨B,hB,hPB,hcurve⟩ := exists_localization_event hb (by linarith) hCr hR i j k
      hloc ((fam o).isBlockCoupling z₀ z₀.2).measurePreserving_old
    have hnorm : 2*Real.sqrt m+2+(W K A (ℓ/K))⁻¹*(R*W K A (ℓ/K)) = ρ := by
      dsimp [ρ]
      field_simp
    have H := lintegral_Y_pow_le_of_good_offset hi hε hprof hb hn hW hQ o g j k
      (R*W K A (ℓ/K)) (by rw [hnorm]; dsimp [ρ]; linarith [Real.sqrt_nonneg (m : ℝ)])
      (by simpa only [hnorm, indexTube] using hg) (fam o) (heq o z₀) hB hcurve
      (by simpa only [show 4*(4*(m+1)) = 16*(m+1) by omega] using h4p o)
    exact H.trans (add_le_add le_rfl (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow hPB (by norm_num))))
  have H := average_le_of_good_offsets x bad (fun o _ => hcoarse o) hgood
  exact H.trans (add_le_add le_rfl (mul_le_mul' le_rfl
    (ENNReal.rpow_le_rpow (add_le_add le_rfl (average_bad_indexTube_le L j k hρ))
      (by norm_num))))

end IsotropicVariance.Paper.Proofs.LabelResidual
