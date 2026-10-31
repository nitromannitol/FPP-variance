/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.Moments

/-!
# The small response on the core

For a label-preserving resampling, the supremum of the normalized changes over the two core
faces has `8d`-th moment at most `(2ε)^(8d)`. Any grid-cube pair contained in the core inherits
this bound. This is the small-change part of the proof of Lemma `lem:residual`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.LabelResidual

variable {m : ℕ} {X : Setting.{u} m}

/-- The normalized absolute response on the two core faces, in `[0,∞]`. -/
noncomputable def coreResponse (b : ℝ) (K : ℕ) (A ℓ : ℝ) (L i : ℕ) (z : Fin m → ℤ)
    (old new : X.Ω) : ℝ≥0∞ :=
  ⨆ (u : coreFace (ℓ / K) (W K A (ℓ / K)) L i z)
    (v : coreFace (ℓ / K) (W K A (ℓ / K)) L (i + 1) z),
    ENNReal.ofReal |(X.slabTime b (chainSlab (ℓ / K) 0 i) new u v -
      X.slabTime b (chainSlab (ℓ / K) 0 i) old u v) / Q K A (ℓ / K)|

/-- The common label cancels simultaneously at all endpoint pairs in the core. -/
theorem coreResponse_le_profileError_pair {Λ : X.LabelFamily} {b A ℓ : ℝ} {K L i : ℕ}
    {z : Fin m → ℤ} {old new : X.Ω} (h : Λ.label i z new = Λ.label i z old) :
    coreResponse b K A ℓ L i z old new ≤
      profileError Λ b K A ℓ L i z new + profileError Λ b K A ℓ L i z old :=
  iSup_le fun u => iSup_le fun v => ofReal_abs_normalized_sub_le h u v

/-- The core response has the moment needed for the square of the normalized reward. -/
theorem lintegral_coreResponse_pow_le_of_label_eq {Λ : X.LabelFamily} {b A ℓ ε : ℝ} {K L i : ℕ}
    {z : Fin m → ℤ} (hε : 0 ≤ ε) (h : Gain.LabelProfileBound X b K A ℓ L Λ ε) (hi : i < K)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (hold : MeasurePreserving old P' X.P) (hnew : MeasurePreserving new P' X.P)
    (heq : ∀ᵐ ω ∂P', Λ.label i z (new ω) = Λ.label i z (old ω)) :
    ∫⁻ ω, coreResponse b K A ℓ L i z (old ω) (new ω) ^ (8 * (m + 1)) ∂P' ≤
      ENNReal.ofReal ((2 * ε) ^ (8 * (m + 1))) := by
  apply (lintegral_mono_ae ?_).trans (lintegral_profileError_pair_pow_le_of_measurePreserving (z := z) hε h hi hold hnew)
  filter_upwards [heq] with ω hω
  exact pow_le_pow_left' (coreResponse_le_profileError_pair hω) _

/-- A grid-cube pair inside a block core has positive response bounded by the core response. -/
theorem ofReal_blockGain_div_le_coreResponse {b A ℓ : ℝ} {K L i : ℕ} {z j k : Fin m → ℤ}
    (hQ : 0 < Q K A (ℓ / K))
    (hj : gridCube (ℓ / K) (W K A (ℓ / K)) 0 i j ⊆
      coreFace (ℓ / K) (W K A (ℓ / K)) L i z)
    (hk : gridCube (ℓ / K) (W K A (ℓ / K)) 0 (i + 1) k ⊆
      coreFace (ℓ / K) (W K A (ℓ / K)) L (i + 1) z)
    (old new : X.Ω) :
    ENNReal.ofReal (X.blockGain b (ℓ / K) (W K A (ℓ / K)) i j k old new / Q K A (ℓ / K)) ≤
      coreResponse b K A ℓ L i z old new := by
  by_cases hfin : coreResponse b K A ℓ L i z old new = ⊤
  · rw [hfin]
    exact le_top
  have hbound : X.blockGain b (ℓ / K) (W K A (ℓ / K)) i j k old new ≤
      (coreResponse b K A ℓ L i z old new).toReal * Q K A (ℓ / K) := by
    apply Real.iSup_le (fun u => Real.iSup_le (fun v => ?_) (by positivity)) (by positivity)
    have hh : ENNReal.ofReal |(X.slabTime b (chainSlab (ℓ / K) 0 i) new u v -
        X.slabTime b (chainSlab (ℓ / K) 0 i) old u v) / Q K A (ℓ / K)| ≤
        coreResponse b K A ℓ L i z old new :=
      le_iSup_of_le ⟨u, hj u.2⟩ (le_iSup_of_le ⟨v, hk v.2⟩ le_rfl)
    have hr := ENNReal.toReal_mono hfin hh
    rw [ENNReal.toReal_ofReal (abs_nonneg _)] at hr
    apply max_le _ (by positivity)
    exact (div_le_iff₀ hQ).mp ((le_abs_self _).trans hr)
  calc
    _ ≤ ENNReal.ofReal (coreResponse b K A ℓ L i z old new).toReal :=
      ENNReal.ofReal_le_ofReal ((div_le_iff₀ hQ).mpr hbound)
    _ = _ := ENNReal.ofReal_toReal hfin

end IsotropicVariance.Paper.Proofs.LabelResidual
