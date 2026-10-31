/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.ClassicalTails
public import CurvatureVariance.Paper.Contracts.Geometry
import CurvatureVariance.Statements.Inputs.IntegralPassageTimeLeTimeConstantAdd

/-!
# The classical estimates, equation `eq:classical`

`ClassicalStatement` (equation `eq:classical` and the text after it): for `x ≠ 0` and `r = |x|₁`,

* the first bound, `|T(0,x) − E T(0,x)| ≤ O₁(C √r)` (absolute form, `IsAbsOs`): as in the paper,
  from [ADH, Theorem 3.13] and the Chernoff bound along a path of `r` edges, which give the tails of
  `exists_tails_zero_of_law`, and [AKM, Lemma A.1], which gives the `O₁` bound (`isAbsOs_of_tails`);
* the second bound, `0 ≤ E T(0,x) − μ(x) ≤ C √(r log(2 + r))`: [ADH, Theorem 3.33] for `|x| > 1`
  (`integral_passageTime_le_timeConstant_add`), the bound `E T(0,x) ≤ r E τ` for the unit vectors,
  and `μ(x) ≤ E T(0,x)` (`Infra.FPP.le_meanTime`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

theorem norm_point_le_l1Dist (x : Vertex m) : ‖point x‖ ≤ (l1Dist 0 x : ℝ) := by
  obtain ⟨p, -, hl⟩ := exists_isPath_length_eq_l1Dist 0 x
  have := norm_point_sub_le_length p
  rwa [Infra.FPP.point_zero, zero_sub, norm_neg, hl] at this

/-- **Equation `eq:classical`**, both bounds, for a law under the standing hypotheses:
the constant depends on the law only. -/
theorem classical_of_law {L : Law m} (hL : L.Valid) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Vertex m, x ≠ 0 →
      Integrable (fun ω => passageTimeReal ω 0 x) L.P ∧
      IsAbsOs L.P 1 (C * Real.sqrt (oneNorm x))
        (fun ω => passageTimeReal ω 0 x - ∫ ω', passageTimeReal ω' 0 x ∂L.P) ∧
      0 ≤ (∫ ω, passageTimeReal ω 0 x ∂L.P) - L.μ.1 (point x) ∧
      (∫ ω, passageTimeReal ω 0 x ∂L.P) - L.μ.1 (point x) ≤
        C * Real.sqrt (oneNorm x * Real.log (2 + oneNorm x)) := by
  have := hL.probF
  have := hL.probP
  obtain ⟨ρ, hρ, htails⟩ := exists_tails_zero_of_law hL
  obtain ⟨Cm, hCm, hmean⟩ :=
    CurvatureVariance.integral_passageTime_le_timeConstant_add hL.one_le_m L.F hL.assumptionW
  obtain ⟨⟨α, hα, hexp⟩, -⟩ := hL.assumptionW
  have hF : Integrable (fun x : ℝ≥0 => (x : ℝ)) L.F := integrable_coe_of_exp hα hexp
  set m₁ := ∫ x : ℝ≥0, (x : ℝ) ∂L.F with hm₁
  have hm₁0 : 0 ≤ m₁ := integral_nonneg fun x => NNReal.coe_nonneg x
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set Cos := tailOsConst ρ with hCos
  have hCos0 : 0 < Cos := tailOsConst_pos hρ
  set C₀ := ((m : ℝ) + 1) * m₁ / Real.sqrt (Real.log 3) with hC₀
  refine ⟨max (max Cos Cm) C₀, lt_max_of_lt_left (lt_max_of_lt_left hCos0), fun x hx => ?_⟩
  obtain ⟨hT, htail⟩ := htails x hx
  have hr1 : (1 : ℝ) ≤ oneNorm x := one_le_oneNorm hx
  have hμle : L.μ.1 (point x) ≤ ∫ ω, passageTimeReal ω 0 x ∂L.P :=
    le_meanTime (IsIIDWeights.measurePreserving_translate hL.iid)
      (IsIIDWeights.integrable_passageTime hL.iid hF) hL.timeConstant x
  have hφ : Real.sqrt (Real.log 3) ≤ Real.sqrt (oneNorm x * Real.log (2 + oneNorm x)) := by
    refine Real.sqrt_le_sqrt ?_
    have : Real.log 3 ≤ Real.log (2 + oneNorm x) := Real.log_le_log (by norm_num) (by linarith)
    nlinarith
  refine ⟨hT, ?_, by linarith, ?_⟩
  · have hO : IsAbsOs L.P 1 (Cos * Real.sqrt (oneNorm x))
        (fun ω => passageTimeReal ω 0 x - ∫ ω', passageTimeReal ω' 0 x ∂L.P) :=
      isAbsOs_of_tails hρ hr1 ((measurable_passageTime_real 0 x).sub measurable_const).aemeasurable
        (fun z hz => (htail z hz).1) (fun z hz => (htail z hz).2)
    have hsq : 0 < Real.sqrt (oneNorm x) := Real.sqrt_pos.2 (by linarith)
    have hle : Cos * Real.sqrt (oneNorm x) ≤ max (max Cos Cm) C₀ * Real.sqrt (oneNorm x) :=
      mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) hsq.le
    exact ⟨hO.1, hO.2.mono_scale zero_le_one (by positivity) hle⟩
  · rcases lt_or_ge 1 ‖point x‖ with hx1 | hx1
    · obtain ⟨-, hup⟩ := hmean L.P hL.iid L.μ hL.timeConstant x hx1
      have hnorm := norm_point_le_l1Dist x
      rw [← oneNorm_eq_l1Dist] at hnorm
      have hlog : 0 < Real.log ‖point x‖ := Real.log_pos hx1
      have hmono : Real.sqrt (‖point x‖ * Real.log ‖point x‖) ≤
          Real.sqrt (oneNorm x * Real.log (2 + oneNorm x)) := by
        refine Real.sqrt_le_sqrt (mul_le_mul hnorm ?_ hlog.le (by linarith))
        exact Real.log_le_log (by linarith) (by linarith)
      have hC : Cm ≤ max (max Cos Cm) C₀ := le_max_of_le_left (le_max_right _ _)
      calc (∫ ω, passageTimeReal ω 0 x ∂L.P) - L.μ.1 (point x)
          ≤ Cm * Real.sqrt (‖point x‖ * Real.log ‖point x‖) := by
            simp only [passageTimeReal]; linarith
        _ ≤ max (max Cos Cm) C₀ * Real.sqrt (oneNorm x * Real.log (2 + oneNorm x)) :=
            mul_le_mul hC hmono (Real.sqrt_nonneg _) (hCm.le.trans hC)
    · have hr : (l1Dist 0 x : ℝ) ≤ (m : ℝ) + 1 := by
        have := l1Dist_zero_le_norm_point x
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      have hET : ∫ ω, passageTimeReal ω 0 x ∂L.P ≤ ((m : ℝ) + 1) * m₁ :=
        (IsIIDWeights.integral_passageTime_le hL.iid hF 0 x).trans
          (mul_le_mul_of_nonneg_right hr hm₁0)
      have hμ0 : 0 ≤ L.μ.1 (point x) := apply_nonneg _ _
      have hsq3 : 0 < Real.sqrt (Real.log 3) := Real.sqrt_pos.2 hlog3
      have hC : C₀ ≤ max (max Cos Cm) C₀ := le_max_right _ _
      calc (∫ ω, passageTimeReal ω 0 x ∂L.P) - L.μ.1 (point x)
          ≤ ((m : ℝ) + 1) * m₁ := by linarith
        _ = C₀ * Real.sqrt (Real.log 3) := by rw [hC₀]; field_simp
        _ ≤ max (max Cos Cm) C₀ * Real.sqrt (oneNorm x * Real.log (2 + oneNorm x)) :=
            mul_le_mul hC hφ hsq3.le ((by positivity : (0 : ℝ) ≤ C₀).trans hC)

/-- **Equation `eq:classical`**, both bounds, with the constant
of the law of `bd` (`classical_of_law`). -/
theorem classicalStatement_holds (m : ℕ) : ClassicalStatement m := by
  intro bd hbd
  obtain ⟨C, hC, h⟩ := classical_of_law hbd.law
  refine ⟨C, hC, fun M _ hfit => ?_⟩
  rw [hfit.P_eq, hfit.μ_eq]
  exact h

end CurvatureVariance.Paper.Proofs.Geometry
