/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Localization
public import IsotropicVariance.Paper.Proofs.Profiles.GridGeometry
import IsotropicVariance.Infra.Os.SumRule
import IsotropicVariance.Paper.Proofs.Modulus.RadiusPointwise
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Lemma `lem:localization` at the pairs of the arrays of Section `sec:gain`

In the proof of Lemma `lem:blocks`, Lemma `lem:localization` at the length `n ≥ N/(8K)` gives
`R_i(j, k) ≤ O_2(C)`. The lemma measures the deviation of a curve from `u` to `v` from the segment
`[u, v]`, and `R_i(j, k)` measures it from the segment of the centers `[ū, v̄]`. The two differ by a
bounded amount after dividing by `W_n` (`Modulus.radius_le`), and adding a constant keeps an `O_2`
bound.

* `isOs_two_one_add`: `1 + f ≤ O_2(2 + C)` for `0 ≤ f ≤ O_2(C)`.
* `isOs_one_add_gridPair`: the quantity `1 + W⁻¹ sup dist(x, [u, v])` of the pair of cubes
  `gridPair n W i j k` is `O_2`, from the bound for all admissible pairs of slope at most `1/2`, for
  `W|k − j| ≤ n/2`. It bounds `R_i(j, k)` (`Modulus.radius_le`) and is the radius of the tube in
  the first bound of equation `eq:rewardmoment`.
-/

@[expose] public section

open MeasureTheory

universe u

namespace IsotropicVariance.Paper.Proofs.Blocks

open Contracts

variable {m : ℕ}

/-- Adding one to a nonnegative `O_2(C)` variable. -/
theorem isOs_two_one_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {C : ℝ} (hC : 0 < C) {f : Ω → ℝ} (hf : Cited.IsOs P 2 C f) (hf0 : ∀ ω, 0 ≤ f ω) :
    Cited.IsOs P 2 (2 + C) (fun ω => 1 + f ω) := by
  have hone : Cited.IsOs P 2 2 (fun _ : Ω => (1 : ℝ)) := by
    refine ⟨aemeasurable_const, ?_⟩
    have h : Real.exp ((max (1 : ℝ) 0 / 2) ^ (2 : ℝ)) ≤ 2 := by
      have e : (max (1 : ℝ) 0 / 2) ^ (2 : ℝ) = 1 / 4 := by
        rw [max_eq_left zero_le_one, Real.rpow_two]
        norm_num
      rw [e]
      calc Real.exp (1 / 4) ≤ Real.exp (Real.log 2) :=
            Real.exp_le_exp.mpr (by linarith only [Real.log_two_gt_d9])
        _ = 2 := Real.exp_log two_pos
    simp only [lintegral_const, measure_univ, mul_one]
    calc ENNReal.ofReal _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal h
      _ = 2 := by norm_num
  let Z : Fin 2 → Ω → ℝ := ![fun _ => 1, f]
  let θ : Fin 2 → ℝ := ![2, C]
  have hs := Infra.Os.isOs_sum_of_one_le (P := P) (s := 2) (by norm_num) Finset.univ θ
    (fun i _ => by fin_cases i <;> simp [θ, hC]) Z
    (fun i _ => by
      fin_cases i
      · exact hone
      · exact hf)
    (fun i _ => by
      fin_cases i
      · exact ae_of_all _ fun ω => by simp [Z]
      · exact ae_of_all _ hf0)
  simp only [Fin.sum_univ_two, θ, Z, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
  exact hs

/-- **The localization at the pairs of cubes.** From the bound of Lemma `lem:localization` for the
admissible pairs of slope at most `1/2`, the quantity `1 + W⁻¹ sup dist(x, [u, v])` of the pair of
cubes `gridPair n W i j k` is `O_2`, for `W|k − j| ≤ n/2`. -/
theorem isOs_one_add_gridPair (X : Setting.{u} m) {b n W Cl : ℝ} (hn : 0 < n) (hW : 0 < W)
    (hCl : 0 < Cl) (H : ∀ p : CubePair m, p.IsAdmissible n W (1 / 2) →
      Cited.IsOs X.P 2 Cl (fun ω => W⁻¹ *
        maxSegmentDeviation (p.slab.density b (X.ρ ω)) p.slab.set p.first p.second))
    (i : ℕ) {j k : Fin m → ℤ} (hjk : W * zNorm (k - j) ≤ n / 2) :
    Cited.IsOs X.P 2 (2 + Cl) (fun ω => 1 + W⁻¹ *
      maxSegmentDeviation ((Profiles.gridPair n W i j k).slab.density b (X.ρ ω))
        (Profiles.gridPair n W i j k).slab.set (Profiles.gridPair n W i j k).first
        (Profiles.gridPair n W i j k).second) :=
  isOs_two_one_add hCl (H _ (Profiles.gridPair_isAdmissible_half hn hW.le (i := i) hjk)) fun _ =>
    mul_nonneg (inv_nonneg.mpr hW.le) (Modulus.maxSegmentDeviation_nonneg _ _ _ _)

end IsotropicVariance.Paper.Proofs.Blocks
