/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.NearAverage
public import IsotropicVariance.Paper.Proofs.LabelResidual.FarMoment
public import IsotropicVariance.Paper.Proofs.LabelResidual.Parameters

/-!
# Small penalized moments for conditional reward arrays

This transfers the near-pair offset average and the far-pair moment estimate in the proof of Lemma
`lem:residual`. The profile tolerance and minimum block side depend only on dimension, the
localization and reward constants, and the desired array penalty. They do not depend on `K`, the
scale or the supplied resampling laws.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.LabelResidual

/-- Any array dominated in moments by the actual averaged reward has small penalized moments. -/
theorem exists_small_dominated_reward_moments (m : ℕ) {C Cr lam : ℝ}
    (hC : 0 < C) (hCr : 0 < Cr) (hlam : 0 < lam) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ L₀ : ℕ,
      ∀ X : Setting.{u} m, ∀ Λ : X.LabelFamily, ∀ b A ℓ ε : ℝ, ∀ K i : ℕ,
      ∀ L : ℕ+, 0 ≤ ε → ε ≤ ε₀ → L₀ ≤ (L : ℕ) → i < K →
      Gain.LabelProfileBound X b K A ℓ L Λ ε →
      X.IsUpperBound b → 0 ≤ ℓ/K → 1 ≤ W K A (ℓ/K) → 0 < Q K A (ℓ/K) →
      ∀ j k : Fin m → ℤ,
      Cited.IsOs X.P 2 Cr
        (Responses.pairLocalizationRadius X b (ℓ/K) (W K A (ℓ/K)) i j k) →
      ∀ fam : (o : Fin m → Fin (L : ℕ)) →
        X.BlockCouplingFamily (ℓ/K) (W K A (ℓ/K)) L i {z | IsBlockIndex L o z},
      (∀ o (z : {z : Fin m → ℤ | IsBlockIndex L o z}),
        ∀ᵐ ω ∂(fam o).P', Λ.label i z ((fam o).new z ω) = Λ.label i z ((fam o).old ω)) →
      (∀ o, ∫⁻ ω, X.Y b (ℓ/K) (W K A (ℓ/K)) (Q K A (ℓ/K)) i j k
        {z | IsBlockIndex L o z} (fam o).old (fam o).new ω ^ (16*(m+1)) ∂(fam o).P' ≤
          ENNReal.ofReal ((C*(1+zNorm (k-j)))^(16*(m+1)))) →
      ∀ Z : X.Ω → ℝ≥0∞,
      (∀ p : ℕ, 1 ≤ p → ∫⁻ ω, Z ω^p ∂X.P ≤
        (Fintype.card (Fin m → Fin (L : ℕ)) : ℝ≥0∞)⁻¹ *
          ∑ o : Fin m → Fin (L : ℕ), ∫⁻ ω,
            X.Y b (ℓ/K) (W K A (ℓ/K)) (Q K A (ℓ/K)) i j k
              {z | IsBlockIndex L o z} (fam o).old (fam o).new ω^p ∂(fam o).P') →
      ∫⁻ ω, (Z ω - ENNReal.ofReal (lam*zNorm (k-j)^2))^(4*(m+1)) ∂X.P ≤
        ENNReal.ofReal (lam^(4*(m+1))) := by
  let D : ℝ := max 1 ((2*C/lam)^2)
  have hD : 0 ≤ D := zero_le_one.trans (le_max_left _ _)
  obtain ⟨ε₀,R,hε₀,hR,L₀,H⟩ := exists_near_moment_parameters m (4*(m+1)) (by omega)
    hC hCr hlam hD
  refine ⟨ε₀,hε₀,L₀,?_⟩
  intro X Λ b A ℓ ε K i L hε hε' hL hi hprof hb hn hW hQ j k hloc fam heq h4p Z hZ
  let _ : Nonempty (Fin m → Fin (L : ℕ)) := ⟨fun _ => ⟨0,L.pos⟩⟩
  let r : ℝ := zNorm (k-j)
  have hr : 0 ≤ r := Profiles.zNorm_nonneg _
  have hM : 0 ≤ C*(1+r) := by positivity
  by_cases hrD : D ≤ r
  · apply lintegral_penalized_pow_le_far (4*(m+1)) hC hlam hrD
    apply (hZ (4*(4*(m+1))) (by omega)).trans
    apply average_le_const
    intro o
    simpa only [show 4*(4*(m+1)) = 16*(m+1) by omega] using h4p o
  · have hrD' : r ≤ D := le_of_lt (lt_of_not_ge hrD)
    have hreal := H ε hε hε' L hL r hr hrD'
    let T : ℝ := 2*Real.exp (-(R/Cr)^2)
    let B : ℝ := (m : ℝ)*(r+2*(2*Real.sqrt m+2+R)+2*Real.sqrt (L : ℕ)+2)/(L : ℝ)
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have havg := average_lintegral_Y_pow_le hi hε hprof hb hn hW hQ hCr hR j k hloc fam heq
      (M := ENNReal.ofReal (C*(1+r)))
      (fun o => by
        rw [← ENNReal.ofReal_pow hM]
        exact h4p o)
    have hcast : ENNReal.ofReal ((2*ε)^(8*(m+1))) +
        ENNReal.ofReal (C*(1+r))^(4*(m+1)) *
          (ENNReal.ofReal T + ENNReal.ofReal B)^(3/4 : ℝ) ≤
        ENNReal.ofReal (lam^(4*(m+1))) := by
      rw [← ENNReal.ofReal_pow hM, ← ENNReal.ofReal_add hT hB,
        ENNReal.ofReal_rpow_of_nonneg (add_nonneg hT hB) (by norm_num : (0 : ℝ) ≤ 3/4),
        ← ENNReal.ofReal_mul (pow_nonneg hM _),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [T,B,show 2*(4*(m+1)) = 8*(m+1) by omega] using hreal
    apply (lintegral_mono fun ω => pow_le_pow_left' tsub_le_self _).trans
    exact (hZ (4*(m+1)) (by omega)).trans (havg.trans hcast)

end IsotropicVariance.Paper.Proofs.LabelResidual
