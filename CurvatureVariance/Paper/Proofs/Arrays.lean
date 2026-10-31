/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Arrays
import CurvatureVariance.Infra.Arrays.Square

/-!
# [AB26, Lemma 2.4]: the contract from the `L²` counting

`ArraysStatement` follows from `Infra.Arrays.lintegral_iSup_penalizedSum_le_of_square`, the
`L²` counting of [AB26, Lemma 2.4]. The bridge changes the form only: the moment hypothesis in
`[0, ∞]` gives integrability and a real moment at most one; a sequence `k` with `k 0 = 0` is the
path through `0` and the free indices `Fin.tail k`; and `‖transversePoint y‖ ^ 2 = ∑ⱼ yⱼ ^ 2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

namespace CurvatureVariance.Paper.Proofs.Arrays

open Infra.Arrays

private lemma pathPt_tail {m M : ℕ} (k : Fin (M + 1) → Fin m → ℤ) (h0 : k 0 = 0) (i : ℕ)
    (hi : i < M + 1) : pathPt 0 (Fin.tail k) i = k ⟨i, hi⟩ := by
  rcases i with _ | j
  · simpa using h0.symm
  · have hj : j < M := by omega
    simp only [pathPt, hj, dite_true, Fin.tail]
    rfl

/-- **[AB26, Lemma 2.4]**, from the `L²` counting. -/
theorem arraysStatement_holds (m : ℕ) : Contracts.ArraysStatement.{u} m := by
  obtain ⟨C, hC, hmain⟩ := lintegral_iSup_penalizedSum_le_of_square m
  refine ⟨C, hC, fun M hM Ω _ P _ Z hmeas hnonneg hind hmom => ?_⟩
  have hint : ∀ i j k, Integrable (fun ω => Z i ω j k ^ (4 * (m + 1))) P := by
    intro i j k
    refine ⟨((hmeas i j k).pow_const _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω =>
      pow_nonneg (hnonneg i ω j k) _)]
    exact (hmom i j k).trans_lt ENNReal.one_lt_top
  have hmom' : ∀ i j k, ∫ ω, Z i ω j k ^ (4 * (m + 1)) ∂P ≤ 1 := by
    intro i j k
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω =>
      pow_nonneg (hnonneg i ω j k) _) (hint i j k).aestronglyMeasurable]
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hmom i j k)
    simpa using this
  refine le_trans (lintegral_mono fun ω => ?_) (hmain M Ω P Z hmeas hnonneg hind hint hmom')
  refine iSup₂_le fun k hk => ?_
  refine le_iSup_of_le (Fin.tail k) (le_of_eq ?_)
  congr 1
  have hp : ∀ i : Fin M, pathPt 0 (Fin.tail k) i = k i.castSucc := fun i =>
    pathPt_tail k hk i (by omega)
  have hs : ∀ i : Fin M, Fin.tail k i = k i.succ := fun i => rfl
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hp, hs]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hp, hs]
    simp [transversePoint, Real.norm_eq_abs, sq_abs]

end CurvatureVariance.Paper.Proofs.Arrays
