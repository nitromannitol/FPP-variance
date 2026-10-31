/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.RowCubes
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes

/-!
# Slopes and increments of row cubes

Rounding the row origins produces a bounded error. If `w` is small compared with the admissible
increment scale, every admissible tuple has the index increments used by the localization arrays.
-/

@[expose] public section

open Set

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- The rounding error of the transverse origin of a row. -/
noncomputable def rowRounding (n : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun j => (⌊(i : ℝ) * n * t j⌋ : ℝ) - (i : ℝ) * n * t j

/-- Rounding a transverse origin moves it by at most `√m`. -/
theorem norm_rowRounding_le (n : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) :
    ‖rowRounding n t i‖ ≤ Real.sqrt m := by
  simpa only [mul_one] using
    Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le (m := m) (r := 1) zero_le_one (fun j => by
      change |(⌊(i : ℝ) * n * t j⌋ : ℝ) - (i : ℝ) * n * t j| ≤ 1
      have hl := Int.floor_le ((i : ℝ) * n * t j)
      have hu := Int.lt_floor_add_one ((i : ℝ) * n * t j)
      exact abs_le.mpr ⟨by linarith only [hu], by linarith only [hl]⟩)

/-- Center increments differ from the nominal drift and the index increment only by rounding. -/
theorem rowCenter_sub (n w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (j k : Fin m → ℤ) :
    rowCenter n w t (i + 1) k - rowCenter n w t i j =
      (n : ℝ) • t + (w : ℝ) • transversePoint (k - j) +
        (rowRounding n t (i + 1) - rowRounding n t i) := by
  ext q
  simp only [rowCenter, rowRounding, transversePoint, PiLp.sub_apply, PiLp.add_apply,
    PiLp.smul_apply, Pi.sub_apply, Int.cast_add, Int.cast_one,
    Int.cast_sub, smul_eq_mul]
  ring

/-- A point of the row is at distance at most `√m w` from its center. -/
theorem norm_point_sub_rowCenter_le (n : ℕ) {w : ℕ} (hw : 1 ≤ w)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (y : Fin m → ℤ) :
    ‖transversePoint y - rowCenter n w t i (rowIndex n w t i y)‖ ≤ Real.sqrt m * w := by
  apply Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le (Nat.cast_nonneg w)
  intro q
  have hrow : ((i * (n : ℤ), y) : Vertex m) ∈ rowCube n w t i (rowIndex n w t i y) := ⟨rfl, rfl⟩
  rw [rowCube_eq_transverseCube n hw t i _] at hrow
  have h := hrow.2 q
  change |(y q : ℝ) - rowCenter n w t i (rowIndex n w t i y) q| ≤ w
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  linarith only [h, hw']

/-- A center-slope bound from the nominal slope, index increment and rounding margin. -/
theorem rowPairSlope_norm_le {n w : ℕ} (hn : 1 ≤ n) (t : EuclideanSpace ℝ (Fin m))
    (i : ℤ) (j k : Fin m → ℤ) {t₀ : EuclideanSpace ℝ (Fin m)} {e : ℝ}
    (ht : ‖t - t₀‖ ≤ (1 / 2 : ℝ) * (n : ℝ) ^ e)
    (hjk : (w : ℝ) * ‖transversePoint (k - j)‖ ≤ (n : ℝ) ^ (1 + e) / 8)
    (hround : 16 * Real.sqrt m ≤ (n : ℝ) ^ (1 + e)) :
    ‖rowPairSlope n w t i j k - t₀‖ ≤ (n : ℝ) ^ e := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hp : (n : ℝ) ^ (1 + e) = (n : ℝ) * (n : ℝ) ^ e := by
    rw [Real.rpow_add hnpos, Real.rpow_one]
  have hroundnorm : ‖rowRounding n t (i + 1) - rowRounding n t i‖ ≤ 2 * Real.sqrt m :=
    (norm_sub_le _ _).trans (by linarith only [norm_rowRounding_le n t (i + 1), norm_rowRounding_le n t i])
  have hcenter : ‖rowCenter n w t (i + 1) k - rowCenter n w t i j - (n : ℝ) • t₀‖ ≤
      (n : ℝ) * ‖t - t₀‖ + (w : ℝ) * ‖transversePoint (k - j)‖ + 2 * Real.sqrt m := by
    rw [rowCenter_sub]
    have hid : (n : ℝ) • t + (w : ℝ) • transversePoint (k - j) +
        (rowRounding n t (i + 1) - rowRounding n t i) - (n : ℝ) • t₀ =
        (n : ℝ) • (t - t₀) + (w : ℝ) • transversePoint (k - j) +
        (rowRounding n t (i + 1) - rowRounding n t i) := by module
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
          abs_of_nonneg (Nat.cast_nonneg (α := ℝ) w), le_refl])) hroundnorm)
  have hnt := mul_le_mul_of_nonneg_left ht hnpos.le
  have hctr : ‖rowCenter n w t (i + 1) k - rowCenter n w t i j - (n : ℝ) • t₀‖ ≤
      (n : ℝ) * (n : ℝ) ^ e := by
    rw [hp] at hjk hround
    nlinarith only [hcenter, hnt, hjk, hround, mul_nonneg hnpos.le (Real.rpow_nonneg hnpos.le e)]
  have hid : rowPairSlope n w t i j k - t₀ = (n : ℝ)⁻¹ •
      (rowCenter n w t (i + 1) k - rowCenter n w t i j - (n : ℝ) • t₀) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hnpos.ne', one_smul, rowPairSlope]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnpos]
  exact (mul_le_mul_of_nonneg_left hctr (inv_nonneg.mpr hnpos.le)).trans_eq
    (by rw [← mul_assoc, inv_mul_cancel₀ hnpos.ne', one_mul])

/-- Every admissible tuple has the index increment allowed by the slab arrays, once the
rounding and cube widths fit inside the margin. -/
theorem tuple_index_increment_le {M : Model m} {n K w : ℕ} (hw : 1 ≤ w)
    {t : EuclideanSpace ℝ (Fin m)} {u v : Vertex m} {Y : Fin (K + 1) → Fin m → ℤ}
    (hY : IsAdmissibleTuple M n K t u v Y)
    (hsmall : 32 * Real.sqrt m * ((w : ℝ) + 1) ≤ (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100))
    (i : Fin K) :
    (w : ℝ) * ‖transversePoint (tupleIndex n w t Y i.succ - tupleIndex n w t Y i.castSucc)‖ ≤
      (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 8 := by
  let j := tupleIndex n w t Y i.castSucc
  let k := tupleIndex n w t Y i.succ
  let c₀ := rowCenter n w t (i : ℤ) j
  let c₁ := rowCenter n w t ((i : ℤ) + 1) k
  have h₀ : ‖transversePoint (Y i.castSucc) - c₀‖ ≤ Real.sqrt m * w :=
    norm_point_sub_rowCenter_le n hw t (i : ℤ) _
  have h₁ : ‖transversePoint (Y i.succ) - c₁‖ ≤ Real.sqrt m * w := by
    simpa only [c₁, k, tupleIndex, Fin.val_succ, Nat.cast_add, Nat.cast_one] using
      norm_point_sub_rowCenter_le n hw t ((i : ℤ) + 1) (Y i.succ)
  have hid : (w : ℝ) • transversePoint (k - j) =
      (transversePoint (Y i.succ) - transversePoint (Y i.castSucc) - (n : ℝ) • t) +
        (c₁ - transversePoint (Y i.succ)) + (transversePoint (Y i.castSucc) - c₀) -
          (rowRounding n t ((i : ℤ) + 1) - rowRounding n t (i : ℤ)) := by
    have h := rowCenter_sub n w t (i : ℤ) j k
    calc
      _ = (rowCenter n w t ((i : ℤ) + 1) k - rowCenter n w t (i : ℤ) j) -
          (n : ℝ) • t - (rowRounding n t ((i : ℤ) + 1) - rowRounding n t (i : ℤ)) := by
        rw [h]
        module
      _ = _ := by dsimp only [c₀, c₁]; module
  have hr : ‖rowRounding n t ((i : ℤ) + 1) - rowRounding n t (i : ℤ)‖ ≤ 2 * Real.sqrt m :=
    (norm_sub_le _ _).trans (by linarith only [norm_rowRounding_le n t ((i : ℤ) + 1), norm_rowRounding_le n t (i : ℤ)])
  have hinc := hY.2.2 i
  rw [Infra.FPP.transversePoint_sub] at hinc
  have hb := norm_sub_le
    ((transversePoint (Y i.succ) - transversePoint (Y i.castSucc) - (n : ℝ) • t) +
      (c₁ - transversePoint (Y i.succ)) + (transversePoint (Y i.castSucc) - c₀))
    (rowRounding n t ((i : ℤ) + 1) - rowRounding n t (i : ℤ))
  have ha := norm_add_le
    ((transversePoint (Y i.succ) - transversePoint (Y i.castSucc) - (n : ℝ) • t) +
      (c₁ - transversePoint (Y i.succ))) (transversePoint (Y i.castSucc) - c₀)
  have hb' := norm_add_le
    (transversePoint (Y i.succ) - transversePoint (Y i.castSucc) - (n : ℝ) • t)
    (c₁ - transversePoint (Y i.succ))
  rw [← hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) w)] at hb
  rw [norm_sub_rev] at h₁
  change (w : ℝ) * ‖transversePoint (k - j)‖ ≤ _
  nlinarith only [hb, ha, hb', hr, hinc, h₀, h₁, hsmall]

end CurvatureVariance.Paper.Responses
