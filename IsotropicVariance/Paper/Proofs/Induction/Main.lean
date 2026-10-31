/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Induction.Induction
public import IsotropicVariance.Infra.TimeConstant.Normalization

/-!
# Theorem `thm:general` over the noise interface

The proof of Theorem `thm:general` from Proposition `prop:induction`, by induction on the length.
`mainSettingStatement_of` proves `MainSettingStatement` from the improvement, equation
`eq:improvement`, and the induction.
- **Normalization.** Divide the density by the time constant `μ > 0`; the result is normalized.
- **The two contracts.** Equation `eq:improvement` gives `K ≥ 10` and a threshold. The induction
  gives `A ≥ 1` with `Var T_t ≤ 4A²t^{1−2/K}` for the normalized density.
- **Undoing the normalization.** For the original density,
  `Var T(0, te₁) ≤ 4μ²A²t^{1−2/K} ≤ t^{1−1/K}` once `t^{1/K} ≥ 4μ²A²`, so `ε = 1/K`.

`mainSettingExpStatement_of` proves `MainSettingExpStatement`, the conclusion of the theorems, in
the same way: the induction gives `|T_s − s| ≤ O_1(Q_s)` for the normalized density and every
`s ≥ 1`, and multiplying by `μ` gives `|T_t − μt| ≤ O_1(μQ_t)` for the original one. Since
`Q_t = A t^{1/2−1/K}`, this is the conclusion with `ε = 2/K` and `C = μA`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.Induction

open Infra.TimeConstant

/-- `c t^{1−2/K} ≤ t^{1−1/K}` once `t ≥ c^K`, for `c ≥ 0` and `t ≥ 1`. -/
theorem mul_rpow_le_rpow {K : ℕ} (hK : 0 < K) {c t : ℝ} (hc : 0 ≤ c) (ht1 : 1 ≤ t)
    (ht : c ^ (K : ℝ) ≤ t) : c * t ^ (1 - 2 / (K : ℝ)) ≤ t ^ (1 - 1 / (K : ℝ)) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hc' : c ≤ t ^ (1 / (K : ℝ)) := by
    calc c = (c ^ (K : ℝ)) ^ (1 / (K : ℝ)) := by
          rw [← Real.rpow_mul hc, mul_one_div_cancel hK', Real.rpow_one]
      _ ≤ t ^ (1 / (K : ℝ)) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hc _) ht (by positivity)
  calc c * t ^ (1 - 2 / (K : ℝ)) ≤ t ^ (1 / (K : ℝ)) * t ^ (1 - 2 / (K : ℝ)) :=
        mul_le_mul_of_nonneg_right hc' (Real.rpow_nonneg ht0.le _)
    _ = t ^ (1 - 1 / (K : ℝ)) := by
        rw [← Real.rpow_add ht0]
        congr 1
        ring

/-- **Theorem `thm:general` over the noise interface**, from the improvement, equation
`eq:improvement`, and the induction on the length (the proof of Theorem `thm:general` from
Proposition `prop:induction`). -/
theorem mainSettingStatement_of (hImp : Contracts.ImprovementStatement.{u})
    (hInd : Contracts.InductionStatement.{u}) : Contracts.MainSettingStatement.{u} := by
  intro m hm X
  have hμ : 0 < timeConstant X := timeConstant_pos X
  obtain ⟨K, hK, N₀, hN₀, hI⟩ := hImp m hm (normalized X) (normalized_isNormalized X)
  obtain ⟨A, hA, -, hvar⟩ := hInd m hm (normalized X) (normalized_isNormalized X) K hK N₀ hN₀ hI
  have hK0 : 0 < K := by omega
  set c : ℝ := 4 * timeConstant X ^ 2 * A ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨1 / K, by positivity, max 1 (c ^ (K : ℝ)), fun t ht => ?_⟩
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  refine ⟨(integrable_TRV X t).aemeasurable, ?_⟩
  have hY := hvar t ht1
  have heq : X.TRV t = fun ω => timeConstant X * (normalized X).TRV t ω := by
    funext ω
    change X.TRV t ω = timeConstant X * (rescale X (timeConstant X) hμ).TRV t ω
    rw [rescale_TRV, mul_div_cancel₀ _ hμ.ne']
  calc evariance (X.TRV t) X.P
      = ENNReal.ofReal (timeConstant X ^ 2) * evariance ((normalized X).TRV t) X.P := by
        rw [heq]
        exact evariance_mul (timeConstant X) ((normalized X).TRV t) X.P
    _ ≤ ENNReal.ofReal (timeConstant X ^ 2) *
          ENNReal.ofReal (4 * A ^ 2 * t ^ (1 - 2 / (K : ℝ))) := by gcongr; exact hY
    _ = ENNReal.ofReal (c * t ^ (1 - 2 / (K : ℝ))) := by
        rw [← ENNReal.ofReal_mul (by positivity), hc]
        ring_nf
    _ ≤ ENNReal.ofReal (t ^ (1 - 1 / (K : ℝ))) :=
        ENNReal.ofReal_le_ofReal (mul_rpow_le_rpow hK0 hc0 ht1 ((le_max_right _ _).trans ht))

/-- **Theorem `thm:general` over the noise interface**, with its conclusion: `ε = 2/K` and
`C = μA`, from the improvement and the induction. -/
theorem mainSettingExpStatement_of (hImp : Contracts.ImprovementStatement.{u})
    (hInd : Contracts.InductionStatement.{u}) : Contracts.MainSettingExpStatement.{u} := by
  intro m hm X
  have hμ : 0 < timeConstant X := timeConstant_pos X
  obtain ⟨K, hK, N₀, hN₀, hI⟩ := hImp m hm (normalized X) (normalized_isNormalized X)
  obtain ⟨A, hA, hOs, -⟩ := hInd m hm (normalized X) (normalized_isNormalized X) K hK N₀ hN₀ hI
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  refine ⟨timeConstant X, tendsto_mean_div_timeConstant X, 2 / K, by positivity,
    timeConstant X * A, by positivity, fun t ht => ?_⟩
  have hscale : timeConstant X * A * t ^ ((1 - 2 / (K : ℝ)) / 2) =
      timeConstant X * Q K A t := by
    rw [Q, show (1 - 2 / (K : ℝ)) / 2 = 1 / 2 - 1 / K by ring]
    ring
  have heq : (fun ω => |X.TRV t ω - timeConstant X * t|) =
      fun ω => timeConstant X * |(normalized X).TRV t ω - t| := by
    funext ω
    have hT : X.TRV t ω = timeConstant X * (normalized X).TRV t ω := by
      change X.TRV t ω = timeConstant X * (rescale X (timeConstant X) hμ).TRV t ω
      rw [rescale_TRV, mul_div_cancel₀ _ hμ.ne']
    rw [hT, ← mul_sub, abs_mul, abs_of_pos hμ]
  rw [hscale, heq]
  exact (Infra.Os.isOs_mul_iff hμ).2 (hOs t ht)

end IsotropicVariance.Paper.Proofs.Induction
