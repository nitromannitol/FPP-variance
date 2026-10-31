/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.GainPoincare
import CurvatureVariance.Infra.EfronStein.Conditional
import Mathlib.Probability.CondVar

/-!
# The variance of `F̄`

As `IsotropicVariance.Paper.Proofs.Gain.AverageVariance` in the continuum library, adapted. The
first part of the proof of [AB26, Proposition 6.5] (its second and third paragraphs, with the
decomposition of `Var[F̄]` stated before [AB26, Lemma 6.3]), which the paper applies in the proof of
Proposition `prop:gain`.

* `le_of_mul_log_le`: the case analysis of the second paragraph of the proof of
  [AB26, Proposition 6.5], which turns the inequality of [AB26, Proposition 1.3] into
  `Var[f] ≤ (K^{−1/12} + C/(α_L log K)) K Q_n²`;
* `evariance_labelMean_le`: the bound of `Var[f]`, for every choice of the vectors `a_i`;
* `evariance_eq_lintegral_add_evariance`: the decomposition of `Var[F̄]` before [AB26, Lemma 6.3];
* `evariance_le_of_offsets`: `F̄` does not depend on the `a_i`, so the decomposition averages over
  them.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain.Printed

open CurvatureVariance.Paper

/-- **The case analysis of the second paragraph of the proof of [AB26, Proposition 6.5].** Let
`S ≤ C A`, `B ≤ C K^{−1/6} A` and `V log(V/B) ≤ (4/α) S`. If `V ≥ K^{−1/12} A`, then
`V/B ≥ K^{1/12}/C ≥ K^{1/24}`, so the logarithm is at least `(log K)/24`. Hence
`V ≤ (K^{−1/12} + 96 C/(α log K)) A`. Here `C ≤ K^{1/24}` is the paper's "for `K` large", and
`B = 0 → V = 0` is the case in which the Lean logarithm of `V/0` is `0`. As
`IsotropicVariance.Paper.Proofs.Gain.le_of_mul_log_le` in the continuum library. -/
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

/-- **The decomposition of the variance** (the display before [AB26, Lemma 6.3]):
`Var[Z] = E[Var[Z | m]] + Var[E[Z | m]]`, with `E[Var[Z | m]]` the mean square of `Z − E[Z | m]`, in
`[0, ∞]`. As `IsotropicVariance.Paper.Proofs.Gain.evariance_eq_lintegral_add_evariance` in the
continuum library. -/
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

section Labels

variable {m n w L K : ℕ} {t : EuclideanSpace ℝ (Fin m)} {β : Type}
  {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β} {M : Model m}

/-- **The bound of `Var[f]`, for every choice of the vectors `a_i`** (the second paragraph of the
proof of [AB26, Proposition 6.5]): every value of `X_G` has probability at least `α`, so
[AB26, Proposition 1.3] applies to `f`, and the two bounds of Lemma `lem:fewtranslates` give
`Var[f] ≤ (K^{−1/12} + 96 C/(α log K)) K Q_n²` when `C ≤ K^{1/24}`. As
`IsotropicVariance.Paper.Proofs.Gain.evariance_labelMean_le` in the continuum library. -/
theorem evariance_labelMean_le (hMP : Contracts.ModifiedPoincareStatement.{0, 0})
    (hM : M.Standing) (hK : 1 < K) {o : ℕ → Fin m → ℤ} (h : IsOffsetLabels n w L K t o lam)
    {Q C α : ℝ} (hQ : 0 < Q) (hC : 0 < C) (hCK : C ≤ (K : ℝ) ^ ((1 : ℝ) / 24)) (hα : 0 < α)
    (hα1 : α ≤ 1)
    (hat : ∀ i < K, ∀ (g : Fin m → ℤ) (ω : Config m),
      ENNReal.ofReal α ≤ M.P (lam (i + 1) (o (i + 1)) g ⁻¹' {lam (i + 1) (o (i + 1)) g ω}))
    {Z : Config m → ℝ} (hZ : MemLp Z 2 M.P)
    (hfew : (∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
        eLpNorm (labelMean M.P Z K o lam -
          integrateLabel M.P (labelMean M.P Z K o lam) K o lam i g) 2 M.P ^ 2 ≤
          ENNReal.ofReal (C * K * Q ^ 2)) ∧
      ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
        eLpNorm (labelMean M.P Z K o lam -
          integrateLabel M.P (labelMean M.P Z K o lam) K o lam i g) 1 M.P ^ 2 ≤
          ENNReal.ofReal (C * (K : ℝ) ^ (-(1 : ℝ) / 6) * (K * Q ^ 2))) :
    evariance (labelMean M.P Z K o lam) M.P ≤
      ENNReal.ofReal (((K : ℝ) ^ (-(1 : ℝ) / 12) + 96 * C / (α * Real.log K)) * (K * Q ^ 2)) := by
  have := hM.probP
  have hK1 : (1 : ℝ) < K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith only [hK1]
  have hf : MemLp (labelMean M.P Z K o lam) 2 M.P := hZ.condExp one_le_two
  have hfm : StronglyMeasurable[blockLabelSigma K o lam Set.univ] (labelMean M.P Z K o lam) :=
    stronglyMeasurable_condExp
  have hA : 0 < (K : ℝ) * Q ^ 2 := by positivity
  have hκ : 0 < (K : ℝ) ^ (-(1 : ℝ) / 6) := Real.rpow_pos_of_pos hK0 _
  obtain ⟨S, B, hB0, hSa, hBb, hlog, hzero⟩ := h.modifiedPoincare_labelMean hMP hM hα hα1 hat hf hfm
    (a := C * K * Q ^ 2) (by positivity) (by positivity) hfew.1 hfew.2
  have h' := le_of_mul_log_le hK1 hA hC hCK hα hB0 (by rw [← mul_assoc]; exact hSa) hBb hlog hzero
  rw [← ofReal_variance hf]
  exact ENNReal.ofReal_le_ofReal h'

/-- The average over offsets of a constant. -/
theorem offsetAverage_const {K L : ℕ} (hL : 1 ≤ L) (c : ℝ≥0∞) :
    offsetAverage (m := m) K L (fun _ => c) = c := by
  unfold offsetAverage
  have hcard : (Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞) = (L : ℝ≥0∞) ^ (m * K) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [← pow_mul, mul_comm]
  have hpos : (L : ℝ≥0∞) ^ (m * K) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : L ≠ 0))
  have htop : (L : ℝ≥0∞) ^ (m * K) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top L)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← mul_assoc,
    ENNReal.inv_mul_cancel hpos htop, one_mul]

/-- The average over offsets of `E + c`. -/
theorem offsetAverage_add_const {K L : ℕ} (hL : 1 ≤ L) (E : (ℕ → Fin m → ℤ) → ℝ≥0∞) (c : ℝ≥0∞) :
    offsetAverage K L (fun o => E o + c) = offsetAverage K L E + c := by
  have h := offsetAverage_const (m := m) (K := K) hL c
  unfold offsetAverage at h ⊢
  rw [Finset.sum_add_distrib, mul_add, h]

/-- **The decomposition, averaged over the vectors `a_i`** (the third paragraph of the proof of
[AB26, Proposition 6.5]): `F̄` does not depend on the `a_i`, so a bound of the average of
`E[Var[F̄ | (X_G)_G]]` and a bound of `Var[f]` at every choice of the `a_i` give a bound of
`Var[F̄]`. As `IsotropicVariance.Paper.Proofs.Gain.evariance_averagedMin_le_of_offsets` in the
continuum library, through `Gain.offsetAverage`. -/
theorem evariance_le_of_offsets (hM : M.Standing) (hL : 1 ≤ L) {Z : Config m → ℝ}
    (hZ : MemLp Z 2 M.P)
    (hσ : ∀ σ : Fin K → Fin m → Fin L, blockLabelSigma K (offsetOf σ) lam Set.univ ≤
      (inferInstance : MeasurableSpace (Config m))) {R T : ℝ}
    (hres : offsetAverage K L (fun o => meanConditionalVariance M.P Z K o lam) ≤ ENNReal.ofReal R)
    (hf : ∀ σ : Fin K → Fin m → Fin L,
      evariance (labelMean M.P Z K (offsetOf σ) lam) M.P ≤ ENNReal.ofReal T) :
    evariance Z M.P ≤ ENNReal.ofReal R + ENNReal.ofReal T := by
  have := hM.probP
  have hvar : ∀ σ : Fin K → Fin m → Fin L, evariance Z M.P ≤
      meanConditionalVariance M.P Z K (offsetOf σ) lam + ENNReal.ofReal T := by
    intro σ
    rw [evariance_eq_lintegral_add_evariance (hσ σ) hZ]
    exact add_le_add le_rfl (hf σ)
  calc evariance Z M.P
      = offsetAverage K L (fun _ => evariance Z M.P) := (offsetAverage_const hL _).symm
    _ ≤ offsetAverage K L (fun o => meanConditionalVariance M.P Z K o lam + ENNReal.ofReal T) :=
        offsetAverage_mono hvar
    _ = offsetAverage K L (fun o => meanConditionalVariance M.P Z K o lam) + ENNReal.ofReal T :=
        offsetAverage_add_const hL _ _
    _ ≤ ENNReal.ofReal R + ENNReal.ofReal T := add_le_add hres le_rfl

end Labels

end CurvatureVariance.Paper.Gain.Printed
