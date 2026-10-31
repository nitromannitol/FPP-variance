/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.MinimumResponse
public import IsotropicVariance.Paper.Proofs.Responses.SlabSeparation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The sum of positive changes is bounded by the selected reward

The deterministic inequality at the end of the proof of Lemma `lem:blocks`, on a family of
couplings with one common old outcome.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

variable {m : ℕ}

/-- Keeping the old minimizing tuple bounds the sum of squared positive changes by its reward, for
one old noise and the new noises of the blocks of a slab on any probability space. -/
theorem ae_tsum_pos_F_sub_sq_le_reward_of_isBlockCoupling {X : Setting m} {b : ℝ}
    (hb : X.IsUpperBound b) {s W Qn : ℝ} (hs : 0 < s) (hW : 0 < W) (hQ : 0 < Qn)
    (hWm : 4 * Real.sqrt m * W ≤ s) {K L : ℕ} (hL : 1 ≤ L)
    (o : Fin m → Fin L) (i : Fin K) {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {old : Ω' → X.Ω} {new : (Fin m → ℤ) → Ω' → X.Ω}
    (hcpl : ∀ g ∈ {g | IsBlockIndex L o g}, X.IsBlockCoupling (block s W L i g) P' old (new g)) :
    ∀ᵐ ω ∂P',
      (∑' g : {g : Fin m → ℤ | IsBlockIndex L o g},
        ENNReal.ofReal (max (X.F b K s 0 (new g ω) - X.F b K s 0 (old ω)) 0 ^ 2)) ≤
      ENNReal.ofReal (Qn ^ 2) * X.Y b s W Qn i
        (X.J b K s W 0 (old ω) i.castSucc) (X.J b K s W 0 (old ω) i.succ)
        {g | IsBlockIndex L o g} old new ω := by
  have hae : ∀ᵐ ω ∂P', ∀ g : {g : Fin m → ℤ | IsBlockIndex L o g}, ∀ r : ℕ,
      r ≠ (i : ℕ) → ∀ u v : Pt m,
        X.slabTime b (chainSlab s 0 r) (new g ω) u v =
          X.slabTime b (chainSlab s 0 r) (old ω) u v :=
    ae_all_iff.mpr fun g => IsBlockCoupling.ae_other_slabTime_eq b hs.le hW hL i g (hcpl g g.2)
  filter_upwards [hae] with ω hω
  rw [Setting.Y, ite_eq_left (Profiles.J_step X hb hs hW hWm (old ω) i), ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro g
  have hsame (r : Fin K) (hri : r ≠ i) : ∀ u v : Pt m,
      X.slabTime b (chainSlab s 0 r) (new g ω) u v =
        X.slabTime b (chainSlab s 0 r) (old ω) u v :=
    hω g r (fun h => hri (Fin.ext h))
  have hgain := pos_F_sub_le_blockGain X hb hs.le hW i (old ω) (new g ω) hsame
  rw [← ENNReal.ofReal_mul (sq_nonneg Qn)]
  apply ENNReal.ofReal_le_ofReal
  have hcancel : Qn ^ 2 * (X.blockGain b s W i
      (X.J b K s W 0 (old ω) i.castSucc) (X.J b K s W 0 (old ω) i.succ)
      (old ω) (new g ω) / Qn) ^ 2 =
        X.blockGain b s W i (X.J b K s W 0 (old ω) i.castSucc)
          (X.J b K s W 0 (old ω) i.succ) (old ω) (new g ω) ^ 2 := by
    field_simp
  rw [hcancel]
  exact pow_le_pow_left₀ (le_max_right _ _) hgain 2

/-- Integrating the common-old comparison and using exchangeability bounds the full energies, for
one old noise and the new noises of the blocks of a slab on any probability space. -/
theorem tsum_lintegral_F_sub_sq_le_selected_reward_of_isBlockCoupling {X : Setting m} {b : ℝ}
    (hb : X.IsUpperBound b) {s W Qn : ℝ} (hs : 0 < s) (hW : 0 < W) (hQ : 0 < Qn)
    (hWm : 4 * Real.sqrt m * W ≤ s) {K L : ℕ} (hL : 1 ≤ L)
    (o : Fin m → Fin L) (i : Fin K) {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {old : Ω' → X.Ω} {new : (Fin m → ℤ) → Ω' → X.Ω}
    (hcpl : ∀ g ∈ {g | IsBlockIndex L o g}, X.IsBlockCoupling (block s W L i g) P' old (new g)) :
    (∑' g : {g : Fin m → ℤ | IsBlockIndex L o g},
      ∫⁻ ω, ENNReal.ofReal ((X.F b K s 0 (new g ω) - X.F b K s 0 (old ω)) ^ 2) ∂P') ≤
      (2 * ENNReal.ofReal (Qn ^ 2)) * ∫⁻ ω, X.Y b s W Qn i
        (X.J b K s W 0 (old ω) i.castSucc) (X.J b K s W 0 (old ω) i.succ)
        {g | IsBlockIndex L o g} old new ω ∂P' := by
  let I := {g : Fin m → ℤ | IsBlockIndex L o g}
  have hF := Infra.Slab.aemeasurable_F X hb hs (0 : Pt m) K
  have hm (g : I) : AEMeasurable (fun ω => ENNReal.ofReal
      (max (X.F b K s 0 (new g ω) - X.F b K s 0 (old ω)) 0 ^ 2)) P' := by
    have hc := hcpl g g.2
    exact ((((hF.comp_quasiMeasurePreserving hc.measurePreserving_new.quasiMeasurePreserving).sub
      (hF.comp_quasiMeasurePreserving hc.measurePreserving_old.quasiMeasurePreserving)).max
        aemeasurable_const).pow_const 2).ennreal_ofReal
  have hswap (g : I) := IsBlockCoupling.lintegral_sq_sub_eq_two_mul (hcpl g g.2) hF
  simp_rw [hswap]
  rw [ENNReal.tsum_mul_left, ← lintegral_tsum hm, mul_assoc]
  apply mul_le_mul' le_rfl
  exact (lintegral_mono_ae
    (ae_tsum_pos_F_sub_sq_le_reward_of_isBlockCoupling hb hs hW hQ hWm hL o i hcpl)).trans_eq
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

end IsotropicVariance.Paper.Proofs.Responses
