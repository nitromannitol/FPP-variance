/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.AverageRewards
public import IsotropicVariance.Paper.Proofs.LabelResidual.ConditionalMoments
import Mathlib.Tactic.Linarith
import IsotropicVariance.Paper.Proofs.SmallMean.ChainSum

/-!
# The small selected-reward estimate

The actual reward is converted into slab-measurable conditional arrays, averaged over offsets.
The moment bounds of the proof of Lemma `lem:residual` and the independent-array inequality then
control the selected sum by a small multiple of the number of slabs and the expected row energy.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.LabelResidual

open Infra.Arrays

private theorem le_one_add_nat_pow {x : ℝ≥0∞} {p : ℕ} (hp : 1 ≤ p) : x ≤ 1+x^p := by
  by_cases hx : x ≤ 1
  · exact hx.trans le_self_add
  · have hx' := le_of_lt (lt_of_not_ge hx)
    exact (pow_one x).symm.le.trans
      ((pow_le_pow_right₀ hx' hp).trans le_add_self)

/-- Uniform profile and localization estimates give, for the selected reward averaged over the
offsets, arrays on the noise, independent over the slabs, with small penalized moments (proof of
Lemma `lem:residual`, the arrays `Y_i` with the offsets included in the expectations). The constants
and parameter choices are independent of `K`. -/
theorem exists_small_penalized_rewards (m : ℕ) {C Cr lam : ℝ}
    (hC : 0 < C) (hCr : 0 < Cr) (hlam : 0 < lam) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ L₀ : ℕ,
      ∀ X : Setting.{u} m, ∀ Λ : X.LabelFamily, ∀ b A ℓ ε : ℝ, ∀ K : ℕ,
      ∀ L : ℕ+, 0 ≤ ε → ε ≤ ε₀ → L₀ ≤ (L : ℕ) →
      Gain.LabelProfileBound X b K A ℓ L Λ ε → X.IsUpperBound b →
      0 < ℓ/K → 1 ≤ W K A (ℓ/K) → 0 < Q K A (ℓ/K) →
      (∀ i : Fin K, ∀ j k, W K A (ℓ/K)*zNorm (k-j) ≤ ℓ/K/2 →
        Cited.IsOs X.P 2 Cr
          (Responses.pairLocalizationRadius X b (ℓ/K) (W K A (ℓ/K)) i j k)) →
      ∀ fam : (i : Fin K) → (o : Fin m → Fin (L : ℕ)) →
        X.BlockCouplingFamily (ℓ/K) (W K A (ℓ/K)) L i {z | IsBlockIndex L o z},
      (∀ (i : Fin K) o (z : {z : Fin m → ℤ | IsBlockIndex L o z}),
        ∀ᵐ ω ∂(fam i o).P', Λ.label i z ((fam i o).new z ω) = Λ.label i z ((fam i o).old ω)) →
      (∀ (i : Fin K) o (j k : Fin m → ℤ), W K A (ℓ/K)*zNorm (k-j) ≤ ℓ/K/2 →
        ∫⁻ ω, X.Y b (ℓ/K) (W K A (ℓ/K)) (Q K A (ℓ/K)) i j k
          {z | IsBlockIndex L o z} (fam i o).old (fam i o).new ω^(16*(m+1)) ∂(fam i o).P' ≤
            ENNReal.ofReal ((C*(1+zNorm (k-j)))^(16*(m+1)))) →
      ∃ y : Fin K → (Fin m → ℤ) → (Fin m → ℤ) → X.Ω → ℝ≥0∞,
        (∀ i j k, Measurable (y i j k)) ∧
        iIndepFun (fun i ω => fun j k => y i j k ω) X.P ∧
        (∀ i j k, W K A (ℓ/K)*zNorm (k-j) ≤ ℓ/K/2 →
          ∫⁻ ω, (y i j k ω - ENNReal.ofReal (lam*(sqNorm (k-j) : ℝ)))^(4*(m+1)) ∂X.P ≤
            ENNReal.ofReal (lam^(4*(m+1)))) ∧
        (Fintype.card (Fin K → Fin m → Fin (L : ℕ)) : ℝ≥0∞)⁻¹ *
          ∑ o : Fin K → Fin m → Fin (L : ℕ), ∑ i : Fin K,
            ∫⁻ ω, X.Y b (ℓ/K) (W K A (ℓ/K)) (Q K A (ℓ/K)) i
              (X.J b K (ℓ/K) (W K A (ℓ/K)) 0 ((fam i (o i)).old ω) i.castSucc)
              (X.J b K (ℓ/K) (W K A (ℓ/K)) 0 ((fam i (o i)).old ω) i.succ)
              {z | IsBlockIndex L (o i) z} (fam i (o i)).old (fam i (o i)).new ω
                ∂(fam i (o i)).P' ≤
          ∫⁻ ω, ∑ i : Fin K, y i (X.J b K (ℓ/K) (W K A (ℓ/K)) 0 ω i.castSucc)
            (X.J b K (ℓ/K) (W K A (ℓ/K)) 0 ω i.succ) ω ∂X.P := by
  obtain ⟨ε₀,hε₀,L₀,H⟩ := exists_small_dominated_reward_moments m hC hCr hlam
  refine ⟨ε₀,hε₀,L₀,?_⟩
  intro X Λ b A ℓ ε K L hε hε' hL hprof hb hn hW hQ hloc fam heq hhigh
  have hW0 : 0 < W K A (ℓ/K) := by linarith
  have hfin : ∀ (i : Fin K) o (j k : Fin m → ℤ), W K A (ℓ/K)*zNorm (k-j) ≤ ℓ/K/2 →
      ∫⁻ ω, X.Y b (ℓ/K) (W K A (ℓ/K)) (Q K A (ℓ/K)) i j k
        {z | IsBlockIndex L o z} (fam i o).old (fam i o).new ω ∂(fam i o).P' ≠ ∞ := by
    intro i o j k hadm
    apply ne_top_of_le_ne_top _ (lintegral_mono fun ω =>
      le_one_add_nat_pow (x := X.Y b (ℓ/K) (W K A (ℓ/K)) (Q K A (ℓ/K)) i j k
        {z | IsBlockIndex L o z} (fam i o).old (fam i o).new ω) (by omega : 1 ≤ 16*(m+1)))
    rw [lintegral_add_left' aemeasurable_const, lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hhigh i o j k hadm)⟩
  obtain ⟨y,hym,hyind,hymom,hysel⟩ := exists_average_conditional_rewards X hb hn hW0
    (Q K A (ℓ/K)) L fam hfin
  refine ⟨y,hym,hyind,fun i j k hadm => ?_,hysel⟩
  have hsq : (sqNorm (k-j) : ℝ) = zNorm (k-j)^2 := by
    rw [SmallMean.zNorm_sq]
    simp only [sqNorm, Int.cast_sum, Int.cast_pow]
  rw [hsq]
  exact H X Λ b A ℓ ε K i L hε hε' hL i.2 hprof hb hn.le hW hQ j k
    (hloc i j k hadm) (fam i) (heq i) (fun o => hhigh i o j k hadm) (y i j k)
    (hymom i j k)

end IsotropicVariance.Paper.Proofs.LabelResidual
