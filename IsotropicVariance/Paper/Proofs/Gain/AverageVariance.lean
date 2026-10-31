/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.PoincareBound
public import IsotropicVariance.Paper.Proofs.Gain.AveragedMin
import IsotropicVariance.Infra.EfronStein.Conditional
import IsotropicVariance.Paper.Proofs.Gain.GainAssembly
import Mathlib.Probability.CondVar

/-!
# The variance of `F̄`

The first part of the proof of Proposition `prop:gain`, with the decomposition of `Var[F̄]` stated
before Lemma `lem:residual`:

* `le_of_mul_log_le`: the case analysis of the proof of Proposition `prop:gain`, which turns the
  inequality of Proposition `prop:BR` into `Var[f] ≤ (K^{−1/12} + C/(α_L log K)) K Q_n²`;
* `evariance_labelMean_le`: the bound of `Var[f]`, for every choice of the vectors `a_i`;
* `evariance_eq_lintegral_add_evariance`: the decomposition of `Var[F̄]` before Lemma
  `lem:residual`;
* `evariance_averagedMin_le_of_offsets`: `F̄` does not depend on the `a_i`, so the decomposition
  averages over them.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper

/-- **The case analysis of the proof of Proposition `prop:gain`.** Let `S ≤ C A`, `B ≤ C K^{−1/6} A`
and `V log(V/B) ≤ (4/α) S`. If `V ≥ K^{−1/12} A`, then `V/B ≥ K^{1/12}/C ≥ K^{1/24}`, so the
logarithm is at least `(log K)/24`. Hence `V ≤ (K^{−1/12} + 96 C/(α log K)) A`. Here `C ≤ K^{1/24}`
is the paper's "for `K` large", and `B = 0 → V = 0` is the case in which the Lean logarithm of `V/0`
is `0`. -/
theorem le_of_mul_log_le {V B S A C α K : ℝ} (hK : 1 < K) (hA : 0 < A) (hC : 0 < C)
    (hCK : C ≤ K ^ ((1 : ℝ) / 24)) (hα : 0 < α) (hB0 : 0 ≤ B) (hS : S ≤ C * A)
    (hB : B ≤ C * K ^ (-(1 : ℝ) / 6) * A) (hlog : V * Real.log (V / B) ≤ 4 / α * S)
    (hzero : B = 0 → V = 0) :
    V ≤ (K ^ (-(1 : ℝ) / 12) + 96 * C / (α * Real.log K)) * A := by
  have hK0 : 0 < K := by linarith only [hK]
  have hlogK : 0 < Real.log K := Real.log_pos hK
  have hterm : 0 ≤ 96 * C / (α * Real.log K) * A := by positivity
  have hκ : 0 < K ^ (-(1 : ℝ) / 12) := Real.rpow_pos_of_pos hK0 _
  have hκA : 0 < K ^ (-(1 : ℝ) / 12) * A := mul_pos hκ hA
  rw [add_mul]
  by_cases hcase : V < K ^ (-(1 : ℝ) / 12) * A
  · linarith only [hcase, hterm]
  · push Not at hcase
    have hV : 0 < V := hκA.trans_le hcase
    have hBpos : 0 < B := lt_of_le_of_ne hB0 fun h => hV.ne' (hzero h.symm)
    have hratio : K ^ ((1 : ℝ) / 24) ≤ V / B := by
      rw [le_div_iff₀ hBpos]
      have hexp : K ^ ((1 : ℝ) / 24) * (K ^ ((1 : ℝ) / 24) * K ^ (-(1 : ℝ) / 6)) =
          K ^ (-(1 : ℝ) / 12) := by
        rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]
        norm_num
      have hK24 : 0 ≤ K ^ ((1 : ℝ) / 24) := (Real.rpow_pos_of_pos hK0 _).le
      have hK6 : 0 ≤ K ^ (-(1 : ℝ) / 6) := (Real.rpow_pos_of_pos hK0 _).le
      calc K ^ ((1 : ℝ) / 24) * B ≤ K ^ ((1 : ℝ) / 24) * (C * K ^ (-(1 : ℝ) / 6) * A) :=
            mul_le_mul_of_nonneg_left hB hK24
        _ ≤ K ^ ((1 : ℝ) / 24) * (K ^ ((1 : ℝ) / 24) * K ^ (-(1 : ℝ) / 6) * A) := by
            gcongr
        _ = K ^ (-(1 : ℝ) / 12) * A := by rw [← hexp]; ring
        _ ≤ V := hcase
    have hlog2 : Real.log K / 24 ≤ Real.log (V / B) := by
      have h := Real.log_le_log (Real.rpow_pos_of_pos hK0 _) hratio
      rw [Real.log_rpow hK0] at h
      linarith only [h]
    have h1 : V * (Real.log K / 24) ≤ 4 / α * (C * A) :=
      (mul_le_mul_of_nonneg_left hlog2 hV.le).trans
        (hlog.trans (mul_le_mul_of_nonneg_left hS (by positivity)))
    have h2 : V ≤ 96 * C / (α * Real.log K) * A := by
      have e : 96 * C / (α * Real.log K) * A = (4 / α * (C * A)) / (Real.log K / 24) := by
        field_simp
        norm_num
      rw [e, le_div_iff₀ (by positivity)]
      exact h1
    linarith only [h2, hκA]

/-- **The decomposition of the variance** (stated before Lemma `lem:residual`):
`Var[Z] = E[Var[Z | m]] + Var[E[Z | m]]`, with `E[Var[Z | m]]` the mean square of `Z − E[Z | m]`, in
`[0, ∞]`. -/
theorem evariance_eq_lintegral_add_evariance {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {P : Measure[mΩ] Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : MemLp Z 2 P) :
    evariance Z P = ∫⁻ ω, ENNReal.ofReal ((Z ω - P[Z | m] ω) ^ 2) ∂P + evariance (P[Z | m]) P := by
  have htv := integral_condVar_add_variance_condExp hm hZ
  have h0 : 0 ≤ ∫ ω, Var[Z; P | m] ω ∂P := by
    rw [condVar, integral_condExp hm]
    exact integral_nonneg fun ω => sq_nonneg _
  rw [← ofReal_variance hZ, ← ofReal_variance (hZ.condExp one_le_two),
    ← Infra.EfronStein.ofReal_integral_condVar hm hZ,
    ← ENNReal.ofReal_add h0 (variance_nonneg _ _), htv]

section Noise

variable {m L K : ℕ} {X : Setting.{u} m}

/-- **The bound of `Var[f]`, for every choice of the vectors `a_i`** (proof of Proposition
`prop:gain`): every value of `X_G` of positive probability has probability at least `α`, so
Proposition `prop:BR` applies to `f`, and the two bounds of Lemma `lem:fewtranslates` give
`Var[f] ≤ (K^{−1/12} + 96 C/(α log K)) K Q_n²` when `C ≤ K^{1/24}`. -/
theorem evariance_labelMean_le (hMP : Contracts.ModifiedPoincareStatement.{0, 0}) (hK : 1 < K)
    {b n W Q C α : ℝ} (hn : 0 < n) (hW : 0 < W) (hQ : 0 < Q) (hC : 0 < C)
    (hCK : C ≤ (K : ℝ) ^ ((1 : ℝ) / 24)) (Λ : X.LabelFamily) (hdet : Λ.IsDetermined n W L)
    (hα : 0 < α) (hat : Λ.AtomsGe α) (o : Fin K → Fin m → Fin L)
    (hF : MemLp (averagedMin X b K n W L) 2 X.P)
    (hfew : ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
        eLpNorm (X.labelMean b K n W Λ o -
          X.P[X.labelMean b K n W Λ o | Λ.otherSigma K o i z]) 2 X.P ^ 2 ≤
          ENNReal.ofReal (C * K * Q ^ 2) ∧
      ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
        eLpNorm (X.labelMean b K n W Λ o -
          X.P[X.labelMean b K n W Λ o | Λ.otherSigma K o i z]) 1 X.P ^ 2 ≤
          ENNReal.ofReal (C * (K : ℝ) ^ (-(1 : ℝ) / 6) * K * Q ^ 2)) :
    evariance (X.labelMean b K n W Λ o) X.P ≤
      ENNReal.ofReal (((K : ℝ) ^ (-(1 : ℝ) / 12) + 96 * C / (α * Real.log K)) * (K * Q ^ 2)) := by
  have hK1 : (1 : ℝ) < K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith only [hK1]
  have hf : MemLp (X.labelMean b K n W Λ o) 2 X.P := hF.condExp one_le_two
  have hfm : StronglyMeasurable[Λ.allSigma K o] (X.labelMean b K n W Λ o) :=
    stronglyMeasurable_condExp
  have hA : 0 < (K : ℝ) * Q ^ 2 := by positivity
  have hκ : 0 < (K : ℝ) ^ (-(1 : ℝ) / 6) := Real.rpow_pos_of_pos hK0 _
  obtain ⟨S, B, hB0, hSa, hBb, hlog, hzero⟩ := Printed.modifiedPoincare_labelMean hMP Λ hn hW hdet
    hα (le_one_of_atomsGe X hat) hat o hf hfm (a := C * K * Q ^ 2) (by positivity) (by positivity)
    hfew.1 hfew.2
  have h := le_of_mul_log_le hK1 hA hC hCK hα hB0 (by rw [← mul_assoc]; exact hSa)
    (by rw [show C * (K : ℝ) ^ (-(1 : ℝ) / 6) * (K * Q ^ 2) =
      C * (K : ℝ) ^ (-(1 : ℝ) / 6) * K * Q ^ 2 by ring]; exact hBb) hlog hzero
  rw [← ofReal_variance hf]
  exact ENNReal.ofReal_le_ofReal h

/-- **The decomposition, averaged over the vectors `a_i`** (proof of Proposition `prop:gain`):
`F̄` does not depend on the `a_i`, so a bound of the average of `E[Var[F̄ | (X_G)_G]]` and a bound
of `Var[f]` at every choice of the `a_i` give a bound of `Var[F̄]`. -/
theorem evariance_averagedMin_le_of_offsets {b n W R T : ℝ} (hL : 1 ≤ L)
    (Λ : X.LabelFamily) (hdet : Λ.IsDetermined n W L)
    (hF : MemLp (averagedMin X b K n W L) 2 X.P)
    (hres : ((L : ℝ≥0∞) ^ (m * K))⁻¹ * ∑ o : Fin K → Fin m → Fin L,
        ∫⁻ ω, ENNReal.ofReal ((averagedMin X b K n W L ω -
          X.P[averagedMin X b K n W L | Λ.allSigma K o] ω) ^ 2) ∂X.P ≤ ENNReal.ofReal R)
    (hf : ∀ o : Fin K → Fin m → Fin L,
      evariance (X.labelMean b K n W Λ o) X.P ≤ ENNReal.ofReal T) :
    evariance (averagedMin X b K n W L) X.P ≤ ENNReal.ofReal R + ENNReal.ofReal T := by
  set N : ℝ≥0∞ := (L : ℝ≥0∞) ^ (m * K) with hNdef
  have hN0 : N ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show L ≠ 0 by omega))
  have hNtop : N ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top L)
  have hcard : ∑ _o : Fin K → Fin m → Fin L, (1 : ℝ≥0∞) = N := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_offsets]
  have hconst : ∀ x : ℝ≥0∞, ∑ _o : Fin K → Fin m → Fin L, x = N * x := fun x => by
    rw [← hcard, Finset.sum_mul, one_mul]
  have hvar : ∀ o : Fin K → Fin m → Fin L, evariance (averagedMin X b K n W L) X.P ≤
      ∫⁻ ω, ENNReal.ofReal ((averagedMin X b K n W L ω -
        X.P[averagedMin X b K n W L | Λ.allSigma K o] ω) ^ 2) ∂X.P + ENNReal.ofReal T := by
    intro o
    rw [evariance_eq_lintegral_add_evariance (Λ.allSigma_le hdet K o) hF]
    exact add_le_add le_rfl (hf o)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun o _ => hvar o
  rw [Finset.sum_add_distrib, hconst, hconst] at hsum
  calc evariance (averagedMin X b K n W L) X.P
      = N⁻¹ * (N * evariance (averagedMin X b K n W L) X.P) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hN0 hNtop, one_mul]
    _ ≤ N⁻¹ * (∑ o : Fin K → Fin m → Fin L,
          ∫⁻ ω, ENNReal.ofReal ((averagedMin X b K n W L ω -
            X.P[averagedMin X b K n W L | Λ.allSigma K o] ω) ^ 2) ∂X.P +
          N * ENNReal.ofReal T) := by gcongr
    _ = N⁻¹ * ∑ o : Fin K → Fin m → Fin L,
          ∫⁻ ω, ENNReal.ofReal ((averagedMin X b K n W L ω -
            X.P[averagedMin X b K n W L | Λ.allSigma K o] ω) ^ 2) ∂X.P + ENNReal.ofReal T := by
        rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hN0 hNtop, one_mul]
    _ ≤ ENNReal.ofReal R + ENNReal.ofReal T := add_le_add hres le_rfl

end Noise

end IsotropicVariance.Paper.Proofs.Gain
