/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.GaussianSum
public import IsotropicVariance.Paper.Proofs.Responses.SegmentNet
import IsotropicVariance.Paper.Proofs.Profiles.CubeGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Gaussian sum along a segment

The weighted cell count in the proof of Lemma `lem:blocks`: summing a Gaussian of
the distance to an integer segment costs at most a dimensional constant times one plus its length.
Unit nets replace the tube-volume calculation and keep the constant uniform in both endpoints.
-/

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

variable {m : ℕ}

/-- Rounding each coordinate to its integer part moves a point by at most `√m`. -/
lemma dist_floor_point_le (x : EuclideanSpace ℝ (Fin m)) :
    dist (transverseIntegerPoint fun i => ⌊x i⌋) x ≤ Real.sqrt m := by
  rw [dist_eq_norm]
  convert Profiles.norm_le_of_abs_le (y := transverseIntegerPoint (fun i => ⌊x i⌋) - x)
    zero_le_one (fun i => ?_) using 1 <;> try rw [mul_one]
  change |(⌊x i⌋ : ℝ) - x i| ≤ 1
  rw [abs_le]
  constructor <;> linarith only [Int.floor_le (x i), Int.lt_floor_add_one (x i)]

/-- Moving the center of a Gaussian by at most `r` only changes its constant and exponent. -/
lemma exp_neg_sq_le_of_dist_le {E : Type*} [PseudoMetricSpace E] {c r : ℝ}
    (hc : 0 ≤ c) {z x q : E} (h : dist x q ≤ r) :
    Real.exp (-c * dist z x ^ 2) ≤
      Real.exp (c * r ^ 2) * Real.exp (-(c / 2) * dist z q ^ 2) := by
  have hr : 0 ≤ r := dist_nonneg.trans h
  have ht : dist z q ≤ dist z x + r :=
    (dist_triangle z x q).trans (add_le_add_right h _)
  have hsq : dist z q ^ 2 ≤ 2 * dist z x ^ 2 + 2 * r ^ 2 := by
    have := pow_le_pow_left₀ dist_nonneg ht 2
    nlinarith only [this, sq_nonneg (dist z x - r)]
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hc (sub_nonneg.mpr hsq)])

/-- A Gaussian lattice sum is bounded uniformly in its real center. -/
theorem tsum_exp_neg_dist_sq_le {c : ℝ} (hc : 0 < c)
    (x : EuclideanSpace ℝ (Fin m)) :
    (∑' z : Fin m → ℤ, ENNReal.ofReal (Real.exp (-c * dist (transverseIntegerPoint z) x ^ 2))) ≤
      ENNReal.ofReal (Real.exp (c * m) * (2 / (1 - Real.exp (-(c / 2)))) ^ m) := by
  let q : Fin m → ℤ := fun i => ⌊x i⌋
  have hround : dist x (transverseIntegerPoint q) ≤ Real.sqrt m := by
    rw [dist_comm]
    exact dist_floor_point_le x
  calc
    _ ≤ ∑' z : Fin m → ℤ, ENNReal.ofReal (Real.exp (c * m)) *
        ENNReal.ofReal (Real.exp (-(c / 2) * ∑ i, (((z - q) i : ℝ)) ^ 2)) := by
      apply ENNReal.tsum_le_tsum
      intro z
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have h := exp_neg_sq_le_of_dist_le hc.le (z := transverseIntegerPoint z) hround
      have hd : dist (transverseIntegerPoint z) (transverseIntegerPoint q) ^ 2 =
          ∑ i, (((z - q) i : ℝ)) ^ 2 := by
        rw [dist_eq_norm, ← transverseIntegerPoint_sub, norm_transverseIntegerPoint, zNorm,
          Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      rw [Real.sq_sqrt (Nat.cast_nonneg m), hd] at h
      exact h
    _ = ENNReal.ofReal (Real.exp (c * m)) *
        ∑' z : Fin m → ℤ, ENNReal.ofReal (Real.exp (-(c / 2) * ∑ i, ((z i : ℝ)) ^ 2)) := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      exact (Equiv.subRight q).tsum_eq fun z =>
        ENNReal.ofReal (Real.exp (-(c / 2) * ∑ i, ((z i : ℝ)) ^ 2))
    _ ≤ ENNReal.ofReal (Real.exp (c * m)) *
        ENNReal.ofReal ((2 / (1 - Real.exp (-(c / 2)))) ^ m) :=
      mul_le_mul' le_rfl (tsum_exp_neg_sq_le (by positivity : 0 < c / 2) m)
    _ = _ := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

/-- The explicit constant in the Gaussian sum along an integer segment. -/
noncomputable def gaussianSegmentConst (m : ℕ) (c : ℝ) : ℝ :=
  2 * Real.exp c * (Real.exp ((c / 2) * m) * (2 / (1 - Real.exp (-(c / 4)))) ^ m)

lemma gaussianSegmentConst_pos (m : ℕ) {c : ℝ} (hc : 0 < c) :
    0 < gaussianSegmentConst m c := by
  have hexp : Real.exp (-(c / 4)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold gaussianSegmentConst
  positivity

/-- Gaussian weights of all cells along `[j,k]` sum to at most `C(1 + |j-k|)`. -/
theorem tsum_exp_neg_infDist_segment_sq_le {c : ℝ} (hc : 0 < c) (j k : Fin m → ℤ) :
    (∑' z : Fin m → ℤ, ENNReal.ofReal (Real.exp (-c *
        infDist (transverseIntegerPoint z)
          (segment ℝ (transverseIntegerPoint j) (transverseIntegerPoint k)) ^ 2))) ≤
      ENNReal.ofReal (gaussianSegmentConst m c * (1 + zNorm (j - k))) := by
  classical
  let p := transverseIntegerPoint j
  let q := transverseIntegerPoint k
  obtain ⟨N, hN, hnet⟩ := segment_unit_net p q
  let x : ℕ → EuclideanSpace ℝ (Fin m) := fun n => p + ((n : ℝ) / N) • (q - p)
  have hcompact : IsCompact (segment ℝ p q) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hterm (z : Fin m → ℤ) : ENNReal.ofReal (Real.exp (-c *
      infDist (transverseIntegerPoint z) (segment ℝ p q) ^ 2)) ≤
      ∑ n ∈ Finset.range (N + 1), ENNReal.ofReal (Real.exp c) *
        ENNReal.ofReal (Real.exp (-(c / 2) * dist (transverseIntegerPoint z) (x n) ^ 2)) := by
    obtain ⟨y, hy, hdist⟩ := hcompact.exists_infDist_eq_dist
      ⟨p, left_mem_segment ℝ p q⟩ (transverseIntegerPoint z)
    obtain ⟨n, hn, hclose⟩ := hnet y hy
    apply le_trans _ (Finset.single_le_sum (fun _ _ => bot_le) hn)
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, hdist]
    apply ENNReal.ofReal_le_ofReal
    simpa only [one_pow, mul_one] using exp_neg_sq_le_of_dist_le hc.le
      (z := transverseIntegerPoint z) hclose
  calc
    _ ≤ ∑' z : Fin m → ℤ, ∑ n ∈ Finset.range (N + 1), ENNReal.ofReal (Real.exp c) *
        ENNReal.ofReal (Real.exp (-(c / 2) * dist (transverseIntegerPoint z) (x n) ^ 2)) :=
      ENNReal.tsum_le_tsum hterm
    _ = ∑ n ∈ Finset.range (N + 1), ENNReal.ofReal (Real.exp c) *
        ∑' z : Fin m → ℤ,
          ENNReal.ofReal (Real.exp (-(c / 2) * dist (transverseIntegerPoint z) (x n) ^ 2)) := by
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      simp_rw [ENNReal.tsum_mul_left]
    _ ≤ ∑ _n ∈ Finset.range (N + 1), ENNReal.ofReal (Real.exp c) *
        ENNReal.ofReal (Real.exp ((c / 2) * m) * (2 / (1 - Real.exp (-(c / 4)))) ^ m) := by
      apply Finset.sum_le_sum
      intro n _
      have h := tsum_exp_neg_dist_sq_le (by positivity : 0 < c / 2) (x n)
      rw [show c / 2 / 2 = c / 4 by ring] at h
      exact mul_le_mul' le_rfl h
    _ = ENNReal.ofReal ((N + 1 : ℝ) * Real.exp c *
        (Real.exp ((c / 2) * m) * (2 / (1 - Real.exp (-(c / 4)))) ^ m)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hlength : (N + 1 : ℝ) ≤ 2 * (1 + zNorm (j - k)) := by
        rw [norm_sub_rev, ← transverseIntegerPoint_sub, norm_transverseIntegerPoint] at hN
        have := Real.sqrt_nonneg (∑ i, (((j - k) i : ℝ)) ^ 2)
        change 0 ≤ zNorm (j - k) at this
        linarith only [hN, this]
      have hexp : Real.exp (-(c / 4)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have := mul_le_mul_of_nonneg_right hlength (by positivity : 0 ≤ Real.exp c *
        (Real.exp ((c / 2) * m) * (2 / (1 - Real.exp (-(c / 4)))) ^ m))
      dsimp only [gaussianSegmentConst]
      nlinarith only [this]

end IsotropicVariance.Paper.Proofs.Responses
