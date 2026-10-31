/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Closing

/-!
# The final target

The proof of Theorem `thm:main` checks that the points near the ray `ℝ₊ξ` lie in the domains `𝒟(s)`.
The theorem at one direction (`CurvatureVariance.evariance_passageTime_floorVertex_le`, not in the
paper) has the targets `⌊nξ⌋`, and the same check reads: `1 ≤ s_n ≤ 2n` and `y_n ∈ 𝒟(s_n)` for every
integer `n` beyond a threshold, here for any `a ∈ [a₀, a₁]` and any distance `C₀`. If
`z_n = (s_n, y_n)` is within `C₀` of `n a (1, t₀)`, then `|s_n − na| ≤ C₀` and
`|y_n − s_n t₀| ≤ |y_n − na t₀| + |na − s_n| |t₀| ≤ C₀ (1 + T)` for `|t₀| ≤ T`, while the radius
`s_n^{3/4+δ/100}` of `𝒟(s_n)` is at least `√s_n ≥ √(a₀ n − C₀)`. The threshold depends only on the
bound `T` of the slope, `a₀` and `C₀`.

* `abs_fst_sub_le_of_norm_le`, `norm_snd_sub_le_of_norm_le`: the two coordinates of a vertex near
  `b (1, t)`;
* `finalTargetStatement_holds`: the contract `Contracts.FinalTargetStatement`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.Reduction

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

variable {m : ℕ}

/-- The longitudinal coordinate of a vertex within `C` of `b (1, t)` is within `C` of `b`. -/
theorem abs_fst_sub_le_of_norm_le {z : Vertex m} {b C : ℝ} {t : EuclideanSpace ℝ (Fin m)}
    (h : ‖point z - b • slopeVec t‖ ≤ C) : |(z.1 : ℝ) - b| ≤ C := by
  have h1 := WithLp.norm_fst_le (x := point z - b • slopeVec t)
  simp only [WithLp.sub_fst, WithLp.smul_fst, point, slopeVec, WithLp.toLp_fst, smul_eq_mul,
    mul_one, Real.norm_eq_abs] at h1
  exact h1.trans h

/-- The transverse coordinate of a vertex within `C` of `b (1, t)` is within `C` of `b t`. -/
theorem norm_snd_sub_le_of_norm_le {z : Vertex m} {b C : ℝ} {t : EuclideanSpace ℝ (Fin m)}
    (h : ‖point z - b • slopeVec t‖ ≤ C) : ‖transversePoint z.2 - b • t‖ ≤ C := by
  have h1 := WithLp.norm_snd_le (x := point z - b • slopeVec t)
  simp only [WithLp.sub_snd, WithLp.smul_snd, point, slopeVec, WithLp.toLp_snd] at h1
  exact h1.trans h

/-- **The final target** (for the theorem at one direction, as in the proof of Theorem `thm:main`):
the contract `Contracts.FinalTargetStatement`. With `C = |C₀|` and `D = C(1 + T)`, the threshold is
`n₁ = ⌈C⌉ + ⌈(max(1, D²) + C)/a₀⌉`; it depends only on `bd.T`, `a₀` and `C₀`. -/
theorem finalTargetStatement_holds (m : ℕ) : FinalTargetStatement m := by
  intro bd hbd a₀ a₁ C₀ ha₀ _
  set C := |C₀| with hCdef
  have hC : 0 ≤ C := abs_nonneg _
  set D := C * (1 + bd.T) with hD
  have hD0 : 0 ≤ D := mul_nonneg hC (by linarith [hbd.T_nonneg])
  set B := max 1 (D ^ 2) + C with hB
  refine ⟨⌈C⌉₊ + ⌈B / a₀⌉₊, fun M hM hfit a ha0 _ z hz' n hn => ?_⟩
  have hz : ∀ n : ℕ, ‖point (z n) - ((n : ℝ) * a) • slopeVec M.t₀‖ ≤ C := fun n =>
    (hz' n).trans (le_abs_self _)
  have ha : 0 < a := ha₀.trans_le ha0
  have hn' : (⌈C⌉₊ : ℝ) + ⌈B / a₀⌉₊ ≤ n := by exact_mod_cast hn
  have hnC : C ≤ n := (Nat.le_ceil C).trans (by linarith [Nat.cast_nonneg (α := ℝ) ⌈B / a₀⌉₊])
  have hnB : B ≤ n * a := by
    have h1 : B / a₀ ≤ n :=
      (Nat.le_ceil _).trans (by linarith [Nat.cast_nonneg (α := ℝ) ⌈C⌉₊])
    rw [div_le_iff₀ ha₀] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left ha0 (Nat.cast_nonneg _))
  have h1 := abs_fst_sub_le_of_norm_le (hz n)
  have h2 := norm_snd_sub_le_of_norm_le (hz n)
  rw [abs_le] at h1
  -- the longitudinal coordinate `s_n ≥ max 1 D²`
  have hS : max 1 (D ^ 2) ≤ ((z n).1 : ℝ) := by linarith
  have hS1 : (1 : ℝ) ≤ (z n).1 := (le_max_left _ _).trans hS
  have hS0 : 0 ≤ (z n).1 := by exact_mod_cast (zero_le_one.trans hS1)
  set s := (z n).1.toNat with hsdef
  have hsz : ((s : ℤ) : ℤ) = (z n).1 := Int.toNat_of_nonneg hS0
  have hsR : (s : ℝ) = ((z n).1 : ℝ) := by
    rw [← hsz, Int.cast_natCast]
  refine ⟨s, by exact_mod_cast hsR ▸ hS1, ?_, hsz.symm, ?_⟩
  · rw [hsR]
    nlinarith
  -- the transverse coordinate: `|y_n − s_n t₀| ≤ C(1 + |t₀|) ≤ D ≤ √s_n ≤ s_n^{3/4+δ/100}`
  show ‖transversePoint (z n).2 - (s : ℝ) • M.t₀‖ ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)
  have hdist : ‖transversePoint (z n).2 - (s : ℝ) • M.t₀‖ ≤ D := by
    have e : transversePoint (z n).2 - (s : ℝ) • M.t₀ =
        (transversePoint (z n).2 - ((n : ℝ) * a) • M.t₀) + ((n : ℝ) * a - s) • M.t₀ := by
      rw [sub_smul]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have h3 : |(n : ℝ) * a - s| ≤ C := by rw [hsR, abs_le]; constructor <;> linarith
    have h4 : |(n : ℝ) * a - s| * ‖M.t₀‖ ≤ C * bd.T :=
      mul_le_mul h3 hfit.t₀_le (norm_nonneg _) hC
    rw [hD]
    nlinarith
  have hs1 : (1 : ℝ) ≤ s := hsR ▸ hS1
  have hsqrt : D ≤ Real.sqrt s := by
    rw [← Real.sqrt_sq hD0]
    exact Real.sqrt_le_sqrt ((le_max_right _ _).trans (hsR ▸ hS))
  have hrpow : Real.sqrt s ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hs1 (by linarith [hM.delta_pos])
  exact hdist.trans (hsqrt.trans hrpow)

end CurvatureVariance.Paper.Proofs.Reduction
