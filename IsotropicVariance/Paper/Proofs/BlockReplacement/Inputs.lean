/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Blocks
public import IsotropicVariance.Infra.Os.Moments
public import IsotropicVariance.Paper.Contracts.Profiles

/-!
# An input of the second bound of equation `eq:rewardmoment`

`lintegral_rowEnergy_le`: the expected energy `E Σ_i |J_i − J_{i−1}|² ≤ 4C + CK` of the indices,
from equation `eq:rowenergy` in the indices (`Profiles.RowEnergyIndexStatement`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.BlockReplacement

variable {m : ℕ}

/-- **The expected energy of the indices** from equation `eq:rowenergy`. -/
theorem lintegral_rowEnergy_le (X : Setting m) {b : ℝ} {K : ℕ} {n W Qn CR : ℝ} (hQ : 0 < Qn)
    (hCR : 0 < CR)
    (hrow : Cited.IsOs X.P 1 (CR * Qn) (fun ω =>
      |X.F b K n 0 ω - K * n| +
        Qn * ∑ i : Fin K, zNorm (X.J b K n W 0 ω i.succ - X.J b K n W 0 ω i.castSucc) ^ 2 -
        CR * K * Qn)) :
    ∫⁻ ω, ENNReal.ofReal
        (∑ i : Fin K, zNorm (X.J b K n W 0 ω i.succ - X.J b K n W 0 ω i.castSucc) ^ 2) ∂X.P ≤
      ENNReal.ofReal (4 * CR + CR * K) := by
  set Pen : X.Ω → ℝ := fun ω =>
    ∑ i : Fin K, zNorm (X.J b K n W 0 ω i.succ - X.J b K n W 0 ω i.castSucc) ^ 2 with hPendef
  set U : X.Ω → ℝ := fun ω => |X.F b K n 0 ω - K * n| + Qn * Pen ω - CR * K * Qn with hUdef
  have hU := Cited.IsOs.lintegral_pos_rpow_le hrow one_pos (by positivity : 0 < CR * Qn)
    zero_le_one
  have e4 : 2 * (1 + ((Nat.ceil ((1 : ℝ) / 1)).factorial : ℝ)) * (CR * Qn) ^ (1 : ℝ) =
      4 * (CR * Qn) := by
    norm_num
  rw [e4] at hU
  simp only [Real.rpow_one] at hU
  have hpt : ∀ ω, ENNReal.ofReal (Pen ω) ≤
      ENNReal.ofReal Qn⁻¹ * ENNReal.ofReal (max (U ω) 0) + ENNReal.ofReal (CR * K) := by
    intro ω
    have hle : Pen ω ≤ Qn⁻¹ * max (U ω) 0 + CR * K := by
      have h1 : U ω ≤ max (U ω) 0 := le_max_left _ _
      have h2 : 0 ≤ |X.F b K n 0 ω - K * n| := abs_nonneg _
      have h3 : Qn * Pen ω ≤ max (U ω) 0 + CR * K * Qn := by
        simp only [hUdef] at h1
        linarith
      have h4 : Pen ω ≤ (max (U ω) 0 + CR * K * Qn) / Qn := by
        rw [le_div_iff₀ hQ]
        linarith
      calc Pen ω ≤ (max (U ω) 0 + CR * K * Qn) / Qn := h4
        _ = Qn⁻¹ * max (U ω) 0 + CR * K := by field_simp
    calc ENNReal.ofReal (Pen ω) ≤ ENNReal.ofReal (Qn⁻¹ * max (U ω) 0 + CR * K) :=
          ENNReal.ofReal_le_ofReal hle
      _ ≤ ENNReal.ofReal (Qn⁻¹ * max (U ω) 0) + ENNReal.ofReal (CR * K) :=
          ENNReal.ofReal_add_le
      _ = ENNReal.ofReal Qn⁻¹ * ENNReal.ofReal (max (U ω) 0) + ENNReal.ofReal (CR * K) := by
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr hQ.le)]
  calc ∫⁻ ω, ENNReal.ofReal (Pen ω) ∂X.P
      ≤ ∫⁻ ω, (ENNReal.ofReal Qn⁻¹ * ENNReal.ofReal (max (U ω) 0) +
          ENNReal.ofReal (CR * K)) ∂X.P := lintegral_mono hpt
    _ = ENNReal.ofReal Qn⁻¹ * ∫⁻ ω, ENNReal.ofReal (max (U ω) 0) ∂X.P +
          ENNReal.ofReal (CR * K) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal Qn⁻¹ * ENNReal.ofReal (4 * (CR * Qn)) + ENNReal.ofReal (CR * K) := by
        gcongr
    _ = ENNReal.ofReal (4 * CR + CR * K) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hQ.le), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        field_simp

end IsotropicVariance.Paper.Proofs.BlockReplacement
