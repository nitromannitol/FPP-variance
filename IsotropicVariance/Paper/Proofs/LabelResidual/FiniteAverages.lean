/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.OffsetAverage
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic.Ring

/-!
# Finite averaging and moments of conditional rewards

A coordinate of a uniformly averaged offset vector is uniform. Jensen transfers a moment
bound through a finite average. These are the finite-sum identities used to average the
slab-measurable conditional reward arrays in the proof of Lemma `lem:residual`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.LabelResidual

/-- A uniformly averaged coordinate of a finite function is uniform. -/
theorem average_apply {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [Nonempty B]
    (i : I) (g : B → ℝ≥0∞) :
    (Fintype.card (I → B) : ℝ≥0∞)⁻¹ * ∑ f : I → B, g (f i) =
      (Fintype.card B : ℝ≥0∞)⁻¹ * ∑ b, g b := by
  classical
  let e := Equiv.funSplitAt i B
  have hs : ∑ f : I → B, g (f i) =
      ∑ p : B × ({j : I // j ≠ i} → B), g p.1 :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hc : Fintype.card (I → B) =
      Fintype.card B * Fintype.card ({j : I // j ≠ i} → B) :=
    (Fintype.card_congr e).trans (Fintype.card_prod _ _)
  rw [hs, hc, Nat.cast_mul, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
  calc
    _ = (Fintype.card B : ℝ≥0∞)⁻¹ *
        ((Fintype.card ({j : I // j ≠ i} → B) : ℝ≥0∞)⁻¹ *
          Fintype.card ({j : I // j ≠ i} → B)) * ∑ b, g b := by ring
    _ = _ := by
      rw [ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp), mul_one]

/-- Jensen for the natural power of a uniform finite average. -/
theorem average_pow_le {I : Type*} [Fintype I] [Nonempty I]
    (a : I → ℝ≥0∞) {p : ℕ} (hp : 1 ≤ p) :
    ((Fintype.card I : ℝ≥0∞)⁻¹ * ∑ i, a i)^p ≤
      (Fintype.card I : ℝ≥0∞)⁻¹ * ∑ i, a i^p := by
  have hw : ∑ _i : I, (Fintype.card I : ℝ≥0∞)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)]
  have h := ENNReal.rpow_arith_mean_le_arith_mean_rpow (s := Finset.univ)
    (fun _ : I => (Fintype.card I : ℝ≥0∞)⁻¹) a hw (by exact_mod_cast hp : (1 : ℝ) ≤ p)
  simpa only [← Finset.mul_sum, ENNReal.rpow_natCast] using h

/-- Integrating Jensen transfers moments through a uniform finite average. -/
theorem lintegral_average_pow_le {I Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Ω] {P : Measure Ω} (Y : I → Ω → ℝ≥0∞)
    (hY : ∀ i, AEMeasurable (Y i) P) {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ ω, ((Fintype.card I : ℝ≥0∞)⁻¹ * ∑ i, Y i ω)^p ∂P ≤
      (Fintype.card I : ℝ≥0∞)⁻¹ * ∑ i, ∫⁻ ω, Y i ω^p ∂P := by
  calc
    _ ≤ ∫⁻ ω, (Fintype.card I : ℝ≥0∞)⁻¹ * ∑ i, Y i ω^p ∂P :=
      lintegral_mono fun ω => average_pow_le (fun i => Y i ω) hp
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by simp),
        lintegral_finsetSum' _ fun i _ => (hY i).pow_const p]

end IsotropicVariance.Paper.Proofs.LabelResidual
