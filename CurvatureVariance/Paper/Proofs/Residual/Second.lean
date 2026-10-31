/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Residual.EfronStein
public import CurvatureVariance.Paper.Proofs.Gain.AVResidual
import CurvatureVariance.Paper.Proofs.Gain.AveragedVariance
import CurvatureVariance.Paper.Proofs.Gain.AVMoments

/-!
# Lemma `lem:residual`: the conditional variance of `F̄`

The second bound of equation `eq:residual` at given offsets, by the third paragraph of the proof
of [AB26, Lemma 6.3], which the proof of Lemma `lem:residual` applies. The steps of the paper's
proof:

* the Efron–Stein inequality applied conditionally to `F̄` (`meanConditionalVariance_le`);
* Jensen's inequality over `m` (`blockEnergy_averagedMin_le`), which gives
  `E[Var[F̄ | (X_G)_G]] ≤ (2⌈K^{2/3}⌉)⁻¹ Σ_{m, G} E[(F_m^G − F_m)²]`;
* translations by multiples of `wL e₂` map blocks to blocks and the `X_G` of a block to that of the
  translated block, so by stationarity the sum over `G` is the same for every `m`
  (`blockEnergy_translatedMin_eq`).

The first bound of equation `eq:residual` then bounds the right side, in `Residual.Main`. The model
is the continuum's `IsotropicVariance.Paper.Proofs.Residual.lintegral_sub_condExp_averagedMin_le`.
There `labelCouplingEnergy_comp_act_shiftBy` moves the resamplings by the translation. Here the
energies are `labelES` terms, and `labelES_comp_translate` moves the blocks and the level sets of
the labels. The translation property of `Gain.IsLabelFamily` says that the family transported by a
translation is the family (`IsLabelFamily.shiftFamily_eq`), so one sum over `G` serves every `m`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Residual

open CurvatureVariance CurvatureVariance.Paper CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-- The vector `z = (0, wLm')` of the translation property at `m' = v e₂` is the common translation
`v L w e₂`. -/
theorem blockShift_eq_commonShift (v L w : ℕ) :
    blockShift w L ((v : ℤ) • transverseUnit m) = commonShift m v L w := by
  refine Prod.ext rfl ?_
  funext k
  simp only [blockShift, commonShift, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **The translation property, for the transported family**: a family of labels with the
translation property of `Gain.IsLabelFamily` is its own translate by `v L w e₂`: the label of the
block `G` is that of `G + v L w e₂` read from the translated weights. -/
theorem IsLabelFamily.shiftFamily_eq {M : Model m} {K : ℕ} {A : ℝ} {L n : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {P : Pt m} {α ε : ℝ}
    {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ}
    (hfam : IsLabelFamily M K A L n t P α ε lam) {i : ℕ} (hi : 1 ≤ i) (hiK : i ≤ K)
    {o : Fin m → ℤ} (ho : ∀ k, 0 ≤ o k ∧ o k < L) (v : ℕ) (g : Fin m → ℤ) :
    shiftFamily v L (wInt M K A n) lam i o g = lam i o g := by
  funext ω u u'
  have h := hfam.translate_eq i hi hiK o g ho ((v : ℤ) • transverseUnit m) ω u u'
  rw [blockShift_eq_commonShift] at h
  exact h

/-- **The sum over `G` is the same for every `m`** (the third paragraph of the proof of
[AB26, Lemma 6.3]): translations by multiples of `wL e₂` map blocks to blocks and, by the
translation property, the `X_G` of a block to that of the translated block, so by stationarity
`Σ_G E[(F_m^G − F_m)²] = Σ_G E[(F^G − F)²]`, for all offsets in range. -/
theorem blockEnergy_translatedMin_eq {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {L n ℓ : ℕ}
    {y : Fin m → ℤ} (hw : 0 < wInt M K A n) {P : Pt m} {α ε : ℝ}
    {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ}
    (hfam : IsLabelFamily M K A L n (targetSlope ℓ y) P α ε lam) {o : ℕ → Fin m → ℤ}
    (ho : ∀ i k, 0 ≤ o i k ∧ o i k < L) (v : ℕ) :
    blockEnergy M.P (fun ω => translatedMin M ω n K ℓ y
        (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m)) n (wInt M K A n) L K
        (targetSlope ℓ y) lam o =
      blockEnergy M.P (fun ω => targetMin M ω n K ℓ y) n (wInt M K A n) L K (targetSlope ℓ y)
        lam o := by
  have hlab := hfam.isOffsetLabels ho
  have h := labelEnergy_translatedMin_eq (L := L) hM hw ℓ y v lam o
    fun i hi g ω => (hlab i hi g).measurableSet ω
  unfold labelEnergy at h
  have h' := (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 h
  refine h'.trans (Finset.sum_congr rfl fun i hi => tsum_congr fun g => ?_)
  rw [IsLabelFamily.shiftFamily_eq hfam (by omega) (Nat.succ_le_of_lt (Finset.mem_range.1 hi))
    (ho (i + 1)) v g]

/-- **Jensen's inequality over `m`** (the third paragraph of the proof of [AB26, Lemma 6.3]):
`Σ_G E[(F̄^G − F̄)²] ≤ ⌈K^{2/3}⌉⁻¹ Σ_{m, G} E[(F_m^G − F_m)²]`. -/
theorem blockEnergy_averagedMin_le {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 1 ≤ K) {A : ℝ}
    {L n ℓ : ℕ} {y : Fin m → ℤ}
    (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ)
    (o : ℕ → Fin m → ℤ)
    (hlab : IsOffsetLabels n (wInt M K A n) L K (targetSlope ℓ y) o lam) :
    blockEnergy M.P (fun ω => averagedMin M K A L ω n ℓ y) n (wInt M K A n) L K
        (targetSlope ℓ y) lam o ≤
      (numTranslates K : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range (numTranslates K),
        blockEnergy M.P (fun ω => translatedMin M ω n K ℓ y
          (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m)) n (wInt M K A n) L K
          (targetSlope ℓ y) lam o := by
  have hprob := hM.probP
  set V := numTranslates K
  have hV := Gain.numTranslates_pos hK
  unfold blockEnergy
  calc ∑ i ∈ Finset.range K, ∑' g, labelES M.P
          (fun ω => averagedMin M K A L ω n ℓ y)
          (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g)
          (lam (i + 1) (o (i + 1)) g)
      ≤ ∑ i ∈ Finset.range K, ∑' g, (V : ℝ≥0∞)⁻¹ *
          ∑ v ∈ Finset.range V, labelES M.P (fun ω => translatedMin M ω n K ℓ y
            (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m))
            (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g)
            (lam (i + 1) (o (i + 1)) g) := by
        gcongr with i hi g
        exact labelES_average_le M.P (fun v ω => translatedMin M ω n K ℓ y
          (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m))
          (fun _ => measurable_translatedMin M n K ℓ y _) hV _ _
          (hlab i (Finset.mem_range.1 hi) g).finite (hlab i (Finset.mem_range.1 hi) g).measurableSet
    _ = (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, ∑ i ∈ Finset.range K, ∑' g,
          labelES M.P (fun ω => translatedMin M ω n K ℓ y
            (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m))
            (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g)
            (lam (i + 1) (o (i + 1)) g) := by
        simp_rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_comm]

/-- **The second bound of Lemma `lem:residual` at given offsets** (the third paragraph of the
proof of [AB26, Lemma 6.3]):
`E[Var[F̄ | (X_G)_G]] ≤ (2⌈K^{2/3}⌉)⁻¹ Σ_{m, G} E[(F_m^G − F_m)²] = ½ Σ_G E[(F^G − F)²]`. -/
theorem meanConditionalVariance_averagedMin_le {M : Model m} (hM : M.Standing) {K : ℕ}
    (hK : 1 ≤ K) {A : ℝ} {L n ℓ : ℕ} {y : Fin m → ℤ} (hL : 1 ≤ L) (hn : 2 ≤ n)
    (hw : 0 < wInt M K A n) {P : Pt m} {α ε : ℝ}
    {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ}
    (hfam : IsLabelFamily M K A L n (targetSlope ℓ y) P α ε lam) {o : ℕ → Fin m → ℤ}
    (ho : ∀ i k, 0 ≤ o i k ∧ o i k < L) :
    meanConditionalVariance M.P (fun ω => averagedMin M K A L ω n ℓ y) K o lam ≤
      blockEnergy M.P (fun ω => targetMin M ω n K ℓ y) n (wInt M K A n) L K (targetSlope ℓ y)
        lam o / 2 := by
  have h₁ := meanConditionalVariance_le hM hfam ho (measurable_averagedMin M K A L n ℓ y)
    (memLp_averagedMin hM hn K A L ℓ y) fun ω ω' h => averagedMin_eq_of_forall_block hL o h
  have h₂ := blockEnergy_averagedMin_le hM hK lam o (hfam.isOffsetLabels ho)
  simp_rw [blockEnergy_translatedMin_eq hM hw hfam ho] at h₂
  have hV : (numTranslates K : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Gain.numTranslates_pos hK).ne'
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel hV (ENNReal.natCast_ne_top _), one_mul] at h₂
  exact h₁.trans (ENNReal.div_le_div_right h₂ 2)

end CurvatureVariance.Paper.Proofs.Residual
