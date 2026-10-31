/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.TupleMoments
public import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Infra.FPP.Model
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.Positivity

/-!
# A uniform fourth moment for the target comparison

Any deterministic admissible tuple supplies a linear-in-`N` fourth-norm bound for `F − T`,
with a constant uniform over models fitting `bd`.
The constant may depend on the fixed number of slabs `K`, as allowed in equation
`eq:fixedcomparison`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

open Infra.FPP

variable {m : ℕ}

/-- The coordinate-path length bound for a slab of an admissible tuple. -/
theorem tuple_coordinate_length_le {M : Model m} (hM : M.Standing) {n K N ℓ : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N) (hℓ : 1 ≤ ℓ) {y : Fin m → ℤ}
    (hy : y ∈ premiseDomain M ℓ) {Y : Fin (K + 1) → Fin m → ℤ}
    (hY : IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y) (i : Fin K) :
    (|(tuplePoint 0 n Y i.castSucc).1 - (tuplePoint 0 n Y i.succ).1| : ℝ) +
        ∑ j, |((tuplePoint 0 n Y i.castSucc).2 j : ℝ) -
          ((tuplePoint 0 n Y i.succ).2 j : ℝ)| + 2 ≤ (3 + (2 + ‖M.t₀‖) * (m : ℝ)) * N := by
  have hi := norm_increment_le_base_mul hM hn (targetSlope_norm_le_base_add_one hM hℓ hy) hY i
  have hsum : ∑ j, |(Y i.castSucc j : ℝ) - (Y i.succ j : ℝ)| ≤ (m : ℝ) * ((2 + ‖M.t₀‖) * n) := by
    calc
      _ ≤ ∑ _j : Fin m, (2 + ‖M.t₀‖) * n := by
        apply Finset.sum_le_sum
        intro j _
        have h := (abs_coord_le_norm_transversePoint (Y i.succ - Y i.castSucc) j).trans hi
        simpa only [Pi.sub_apply, Int.cast_sub, abs_sub_comm] using h
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfst : ((tuplePoint 0 n Y i.castSucc).1 : ℝ) -
      ((tuplePoint 0 n Y i.succ).1 : ℝ) = -(n : ℝ) := by
    simp only [tuplePoint, Prod.fst_zero, zero_add, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_add, Nat.cast_one, Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_one]
    ring
  rw [hfst, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  change (n : ℝ) + ∑ j, |(Y i.castSucc j : ℝ) - (Y i.succ j : ℝ)| + 2 ≤ _
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_left hnN'
    (show 0 ≤ 3 + (2 + ‖M.t₀‖) * (m : ℝ) by positivity)
  nlinarith only [hsum, hmul, hn']

/-- The fourth norm of `F − T` is uniformly at most a constant times `N`, whenever an
admissible tuple exists. The constant depends only on `bd` and `K`, and is chosen before the
model. No moment comparison premise or amplitude restriction is used. -/
theorem target_difference_four_le (bd : Bounds m) (hbd : bd.Valid) (K : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ M : Model m, M.Standing → M.Fits bd → ∀ (N n ℓ : ℕ) (y : Fin m → ℤ),
      2 ≤ n → n ≤ ℓ → ℓ ≤ N → y ∈ premiseDomain M ℓ →
      (∃ Y, IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y) →
      eLpNorm (fun ω => targetMin M ω n K ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)) 4 M.P ≤
        ENNReal.ofReal (B * N) := by
  let : IsProbabilityMeasure bd.law.F := hbd.law.probF
  obtain ⟨α, hα, hexp⟩ := hbd.law.assumptionW.1
  have hW := memLp_four_weight hα hexp
  let W := (eLpNorm (fun x : ℝ≥0 => (x : ℝ)) 4 bd.law.F).toReal
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hWeq : eLpNorm (fun x : ℝ≥0 => (x : ℝ)) 4 bd.law.F = ENNReal.ofReal W :=
    (ENNReal.ofReal_toReal hW.ne).symm
  have hTnonneg : 0 ≤ bd.T := hbd.T_nonneg
  let D : ℝ := (K : ℝ) * (3 + (2 + bd.T) * m) + (1 + m * (1 + bd.T))
  refine ⟨(D + 1) * (W + 1), by dsimp only [D]; positivity, ?_⟩
  intro M hM hfit N n ℓ y hn hnℓ hℓN hy hYexists
  have hWeqM : eLpNorm (fun x : ℝ≥0 => (x : ℝ)) 4 M.F = ENNReal.ofReal W := by
    rw [hfit.F_eq]
    exact hWeq
  obtain ⟨Y, hY⟩ := hYexists
  have hℓ : 1 ≤ ℓ := by omega
  have hnN : n ≤ N := hnℓ.trans hℓN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hF : eLpNorm (fun ω => targetMin M ω n K ℓ y) 4 M.P ≤
      ENNReal.ofReal ((K : ℝ) * (3 + (2 + bd.T) * m) * N * W) := by
    calc
      _ ≤ ∑ i : Fin K, eLpNorm (fun ω => slabTimeReal ω
          ((i : ℤ) * n) (((i : ℤ) + 1) * n)
          (tuplePoint 0 n Y i.castSucc) (tuplePoint 0 n Y i.succ)) 4 M.P := by
        simpa only [targetMin, Prod.fst_zero, zero_add] using eLpNorm_slabMin_four_le_tuple hn hY
      _ ≤ ∑ _i : Fin K, ENNReal.ofReal ((3 + (2 + bd.T) * (m : ℝ)) * N) * ENNReal.ofReal W := by
        apply Finset.sum_le_sum
        intro i _
        have hb := eLpNorm_slabTimeReal_four_le hM.iid
          (p := (i : ℤ) * n) (q := ((i : ℤ) + 1) * n)
          (u := tuplePoint 0 n Y i.castSucc) (v := tuplePoint 0 n Y i.succ)
          (by
            have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
            nlinarith only [hn'])
          (by simp only [tuplePoint, Prod.fst_zero, zero_add, Fin.val_castSucc];
              constructor <;> nlinarith only [Nat.cast_nonneg (α := ℤ) n])
          (by simp only [tuplePoint, Prod.fst_zero, zero_add, Fin.val_succ, Nat.cast_add, Nat.cast_one];
              constructor <;> nlinarith only [Nat.cast_nonneg (α := ℤ) n])
        rw [hWeqM] at hb
        refine hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
        push_cast
        refine (tuple_coordinate_length_le hM (by omega) hnN hℓ hy hY i).trans ?_
        gcongr
        exact hfit.t₀_le
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast]
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ K)]
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (K : ℝ) * ((3 + (2 + bd.T) * m) * N))]
        congr 1
        ring
  have hl1 : (l1Dist (0 : Vertex m) ((ℓ : ℤ), y) : ℝ) ≤ (1 + (m : ℝ) * (1 + bd.T)) * N := by
    have hsum : ∑ j, |(y j : ℝ)| ≤ (m : ℝ) * ((1 + bd.T) * N) := by
      calc
        _ ≤ ∑ _j : Fin m, (1 + bd.T) * (N : ℝ) := Finset.sum_le_sum fun j _ =>
          ((abs_coord_le_norm_transversePoint y j).trans (target_norm_le_length hM hℓ hy)).trans
            ((mul_le_mul_of_nonneg_right (by linarith only [hfit.t₀_le])
              (Nat.cast_nonneg ℓ)).trans
              (mul_le_mul_of_nonneg_left (by exact_mod_cast hℓN) (by positivity)))
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [l1Dist, Prod.fst_zero, Prod.snd_zero, zero_sub, Pi.zero_apply, Int.natAbs_neg,
      Int.natAbs_natCast, Nat.cast_add, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs] 
    have hℓN' : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓN
    linarith only [hsum, hℓN']
  have hT : eLpNorm (fun ω => passageTimeReal ω 0 ((ℓ : ℤ), y)) 4 M.P ≤
      ENNReal.ofReal ((1 + (m : ℝ) * (1 + bd.T)) * N * W) := by
    have h := eLpNorm_passageTimeReal_four_le hM.iid (0 : Vertex m) ((ℓ : ℤ), y)
    rw [hWeqM, ← ENNReal.ofReal_natCast] at h
    refine h.trans ?_
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1 + (m : ℝ) * (1 + bd.T)) * N)]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hl1) le_rfl
  calc
    _ ≤ eLpNorm (fun ω => targetMin M ω n K ℓ y) 4 M.P +
        eLpNorm (fun ω => passageTimeReal ω 0 ((ℓ : ℤ), y)) 4 M.P := eLpNorm_sub_le (by norm_num)
    _ ≤ ENNReal.ofReal ((K : ℝ) * (3 + (2 + bd.T) * m) * N * W) +
        ENNReal.ofReal ((1 + (m : ℝ) * (1 + bd.T)) * N * W) := add_le_add hF hT
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hD0 : 0 ≤ D := by dsimp only [D]; positivity
      have hle : D * W ≤ (D + 1) * (W + 1) := by nlinarith only [hD0, hW0]
      have hmul := mul_le_mul_of_nonneg_right hle hN0
      dsimp only [D] at hmul
      nlinarith only [hmul]

end CurvatureVariance.Paper.Responses
