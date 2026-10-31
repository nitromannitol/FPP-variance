/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.RadiusVersion
public import IsotropicVariance.Paper.Proofs.Profiles.RowEnergy
public import IsotropicVariance.Paper.Contracts.Blocks
public import IsotropicVariance.Paper.Contracts.Profiles
public import IsotropicVariance.Infra.Os.Moments
import Mathlib.Tactic.Linarith
import IsotropicVariance.Paper.Proofs.Gain.Tube
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:blocks`, equation `eq:radiusenergy`: `E Σ_i R_i(J_{i−1}, J_i)² ≤ C K`

The proof of Lemma `lem:blocks`: "Lemma `lem:localization` at the length `n ≥ N/(8K)` bounds
every fixed moment of `R_i(j, k)` by a constant, and `R_i(j, k)` is determined by the noise in the
`i`th slab, so the arrays `R_i²` are independent over `i`. Lemma `lem:polynomialarray`, applied to
a small fixed multiple of `R_i²`, and equation `eq:rowenergy` give equation `eq:radiusenergy`."

`lintegral_radius_pow_le`: `E R_i(j, k)^{8d} ≤ C'` from the pointwise bound `radius_le` and
equation `eq:localization` of Lemma `lem:localization` for the slab passage time of the pair
`gridPair n W i j k`.

The rest of the proof is `Proofs.Blocks.radiusEnergyStatement_of`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Metric

universe u

namespace IsotropicVariance.Paper.Proofs.Modulus

open Contracts Infra.Slab

variable {m : ℕ}

/-- The moment constant `C'` of `E R_i(j, k)^{8d} ≤ C'`. -/
noncomputable def radiusMomentConst (m : ℕ) (CL : ℝ) : ℝ :=
  (2 * Real.sqrt m + 2) ^ (8 * (m + 1)) *
    (2 * (1 + ((Nat.ceil (((8 * (m + 1) : ℕ) : ℝ) / 2)).factorial : ℝ)) *
      CL ^ (((8 * (m + 1) : ℕ) : ℝ)))

lemma radiusMomentConst_nonneg (m : ℕ) {CL : ℝ} (hCL : 0 ≤ CL) : 0 ≤ radiusMomentConst m CL := by
  unfold radiusMomentConst
  positivity

/-- **The moments of the radii**: `E R_i(j, k)^{8d} ≤ C'`, given equation `eq:localization` for
the slab passage time of the pair of cubes. -/
lemma lintegral_radius_pow_le (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {n W CL : ℝ}
    (hW : 0 < W) (hCL : 0 < CL) (i : ℕ) (j k : Fin m → ℤ)
    (hY : W * zNorm (k - j) ≤ n / 2 → Cited.IsOs X.P 2 CL (fun ω => 1 + W⁻¹ *
      maxSegmentDeviation ((Profiles.gridPair n W i j k).slab.density b (X.ρ ω))
        (Profiles.gridPair n W i j k).slab.set (Profiles.gridPair n W i j k).first
        (Profiles.gridPair n W i j k).second)) :
    ∫⁻ ω, ENNReal.ofReal (X.R b n W ω i j k ^ (8 * (m + 1))) ∂X.P ≤
      ENNReal.ofReal (radiusMomentConst m CL) := by
  by_cases hjk : W * zNorm (k - j) ≤ n / 2
  · set Y : X.Ω → ℝ := fun ω => 1 + W⁻¹ *
      maxSegmentDeviation ((Profiles.gridPair n W i j k).slab.density b (X.ρ ω))
        (Profiles.gridPair n W i j k).slab.set (Profiles.gridPair n W i j k).first
        (Profiles.gridPair n W i j k).second with hYdef
    have hYos := hY hjk
    have hY1 : ∀ ω, 1 ≤ Y ω := fun ω => by
      have h1 := maxSegmentDeviation_nonneg ((Profiles.gridPair n W i j k).slab.density b (X.ρ ω))
        (Profiles.gridPair n W i j k).slab.set (Profiles.gridPair n W i j k).first
        (Profiles.gridPair n W i j k).second
      have h2 : 0 ≤ W⁻¹ := inv_nonneg.mpr hW.le
      have := mul_nonneg h2 h1
      simp only [hYdef]
      linarith
    set N := 8 * (m + 1)
    set c : ℝ := 2 * Real.sqrt m + 2
    have hpt : ∀ ω, X.R b n W ω i j k ^ N ≤ c ^ N * max (Y ω) 0 ^ (N : ℝ) := by
      intro ω
      have h1 := radius_le X hb hW ω i hjk
      have h0 := Gain.R_nonneg X b n hW.le ω i j k
      have hsq := Real.sqrt_nonneg (m : ℝ)
      have hc : (radiusConst m + Real.sqrt m - 1) + Y ω ≤ c * Y ω := by
        have := hY1 ω
        simp only [radiusConst, c]
        nlinarith
      rw [max_eq_left (by linarith [hY1 ω]), Real.rpow_natCast, ← mul_pow]
      exact pow_le_pow_left₀ h0 (h1.trans hc) N
    calc ∫⁻ ω, ENNReal.ofReal (X.R b n W ω i j k ^ N) ∂X.P
        ≤ ∫⁻ ω, ENNReal.ofReal (c ^ N) * ENNReal.ofReal (max (Y ω) 0 ^ (N : ℝ)) ∂X.P := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hpt ω)
      _ = ENNReal.ofReal (c ^ N) * ∫⁻ ω, ENNReal.ofReal (max (Y ω) 0 ^ (N : ℝ)) ∂X.P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (c ^ N) * ENNReal.ofReal (2 * (1 +
            ((Nat.ceil ((N : ℝ) / 2)).factorial : ℝ)) * CL ^ (N : ℝ)) := by
          gcongr
          exact Cited.IsOs.lintegral_pos_rpow_le hYos (by norm_num) hCL (by positivity)
      _ = ENNReal.ofReal (radiusMomentConst m CL) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          rfl
  · have hR : ∀ ω, X.R b n W ω i j k = 0 := fun ω => by
      unfold Setting.R
      simp [hjk]
    simp [hR]

end IsotropicVariance.Paper.Proofs.Modulus

