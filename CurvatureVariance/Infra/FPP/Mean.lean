/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.MeanRate
public import CurvatureVariance.Infra.FPP.TimeConstant

/-!
# The mean rate of first-passage percolation ([ADH, Thm 3.33])

For the law `P` of independent weights with an integrable law `F`, the cheap-path estimate
`CheapPaths P a c` and the Gaussian lower tail of least costs `MinCostLowerTail P C₁ c₁`, every
time constant `μ` satisfies `μ(x) ≤ E T(0, x) ≤ μ(x) + C (|x| log |x|)^{1/2}` for `|x| > 1`
(`integral_passageTime_le_timeConstant_add_of_cheapPaths`), with one constant `C` for all time
constants (there is at most one, `isTimeConstant_unique`).

The inputs of Alexander's method (`meanTime_le_add_meanRate`) are discharged from the model:
- translation invariance (`IsIIDWeights.measurePreserving_translate`);
- integrable passage times and weights, and `E T(0, x) ≤ d E τ |x|` (`IsIIDWeights.meanTime_le`);
- the cheap-path estimate at a rate `a ≤ 1` (`CheapPaths.mono_rate`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- The cheap-path estimate is monotone in the rate: a smaller rate gives a smaller event. -/
theorem CheapPaths.mono_rate {P : Measure (Config m)} {a a' c : ℝ} (h : CheapPaths P a c)
    (ha' : a' ≤ a) : CheapPaths P a' c := fun u k => by
  refine le_trans (measure_mono fun ω hω => ?_) (h u k)
  obtain ⟨v, p, hp, hl, hcost⟩ := hω
  exact ⟨v, p, hp, hl, hcost.trans (mul_le_mul_of_nonneg_right ha' (Nat.cast_nonneg k))⟩

/-- A lattice point of norm greater than one has norm at least `√2`: its squared norm is an
integer. -/
theorem sqrt_two_le_norm_point {x : Vertex m} (hx : 1 < ‖point x‖) : Real.sqrt 2 ≤ ‖point x‖ := by
  have hsq : ‖point x‖ ^ 2 = ((x.1 ^ 2 + ∑ j, x.2 j ^ 2 : ℤ) : ℝ) := by
    rw [norm_point_sq, transversePoint, EuclideanSpace.norm_sq_eq]
    push_cast
    simp [Real.norm_eq_abs, sq_abs]
  have h1 : (1 : ℝ) < ‖point x‖ ^ 2 := by nlinarith
  rw [hsq] at h1
  have h2 : (2 : ℤ) ≤ x.1 ^ 2 + ∑ j, x.2 j ^ 2 := by exact_mod_cast h1
  have h3 : (2 : ℝ) ≤ ‖point x‖ ^ 2 := by rw [hsq]; exact_mod_cast h2
  calc Real.sqrt 2 ≤ Real.sqrt (‖point x‖ ^ 2) := Real.sqrt_le_sqrt h3
    _ = ‖point x‖ := Real.sqrt_sq (norm_nonneg _)

/-- `log(2 + r) ≤ κ log r` for `r ≥ √2`, with `κ = 1 + 2 log 3/log 2`. -/
theorem log_two_add_le {r : ℝ} (hr : Real.sqrt 2 ≤ r) :
    Real.log (2 + r) ≤ (1 + 2 * Real.log 3 / Real.log 2) * Real.log r := by
  have hs1 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hr1 : 1 ≤ r := hs1.trans hr
  have hr0 : 0 < r := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlr : Real.log 2 / 2 ≤ Real.log r := by
    have : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
      rw [Real.log_sqrt (by norm_num)]
    rw [← this]; exact Real.log_le_log (by positivity) hr
  have h3r : Real.log (2 + r) ≤ Real.log 3 + Real.log r := by
    rw [← Real.log_mul (by norm_num) hr0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hk : Real.log 3 ≤ 2 * Real.log 3 / Real.log 2 * Real.log r := by
    have e : Real.log 3 = 2 * Real.log 3 / Real.log 2 * (Real.log 2 / 2) := by
      field_simp
    calc Real.log 3 = 2 * Real.log 3 / Real.log 2 * (Real.log 2 / 2) := e
      _ ≤ 2 * Real.log 3 / Real.log 2 * Real.log r :=
          mul_le_mul_of_nonneg_left hlr (by positivity)
  have e2 : (1 + 2 * Real.log 3 / Real.log 2) * Real.log r =
      Real.log r + 2 * Real.log 3 / Real.log 2 * Real.log r := by ring
  linarith

/-- The rate `φ(r) = (r log(2 + r))^{1/2}` is at most `κ^{1/2} (r log r)^{1/2}` for `r ≥ √2`. -/
theorem meanRate_le_sqrt_mul {r : ℝ} (hr : Real.sqrt 2 ≤ r) :
    meanRate r ≤
      Real.sqrt (1 + 2 * Real.log 3 / Real.log 2) * Real.sqrt (r * Real.log r) := by
  have hκ0 : 0 ≤ 1 + 2 * Real.log 3 / Real.log 2 := by
    have : 0 ≤ 2 * Real.log 3 / Real.log 2 :=
      div_nonneg (by have := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num); linarith)
        (Real.log_nonneg (by norm_num))
    linarith
  have hr0 : 0 ≤ r := (Real.sqrt_nonneg 2).trans hr
  rw [← Real.sqrt_mul hκ0, meanRate]
  refine Real.sqrt_le_sqrt ?_
  have := log_two_add_le hr
  calc r * Real.log (2 + r) ≤ r * ((1 + 2 * Real.log 3 / Real.log 2) * Real.log r) :=
        mul_le_mul_of_nonneg_left this hr0
    _ = (1 + 2 * Real.log 3 / Real.log 2) * (r * Real.log r) := by ring

/-- **[ADH, Theorem 3.33]**: under the cheap-path estimate and the Gaussian lower tail of least
costs, one constant `C > 0` gives `μ(x) ≤ E T(0, x) ≤ μ(x) + C (|x| log |x|)^{1/2}` for every time
constant `μ` and every `x ∈ ℤ^d` with `|x| > 1`. -/
theorem integral_passageTime_le_timeConstant_add_of_cheapPaths {F : Measure ℝ≥0}
    [IsProbabilityMeasure F] (hF : Integrable (fun x : ℝ≥0 => (x : ℝ)) F)
    {P : Measure (Config m)} [IsProbabilityMeasure P] (hP : IsIIDWeights P F) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hcheap : CheapPaths P a c) {C₁ c₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hc₁ : 0 < c₁) (hlow : MinCostLowerTail P C₁ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : PtNorm m, IsTimeConstant P μ → ∀ x : Vertex m, 1 < ‖point x‖ →
      μ.1 (point x) ≤ ∫ ω, (passageTime ω 0 x : ℝ) ∂P ∧
        ∫ ω, (passageTime ω 0 x : ℝ) ∂P ≤
          μ.1 (point x) + C * √(‖point x‖ * Real.log ‖point x‖) := by
  by_cases hex : ∃ μ₀ : PtNorm m, IsTimeConstant P μ₀
  swap
  · exact ⟨1, one_pos, fun μ hμ => absurd ⟨μ, hμ⟩ hex⟩
  obtain ⟨μ₀, hμ₀⟩ := hex
  have hT := IsIIDWeights.measurePreserving_translate hP
  have hI := IsIIDWeights.integrable_passageTime hP hF
  have hE : ∀ e : Edge m, Integrable (fun ω : Config m => (ω e : ℝ)) P := fun e =>
    (IsIIDWeights.identDistrib hP e).integrable_iff.2 hF
  have hA : 0 ≤ ((m : ℝ) + 1) * ∫ t, (t : ℝ) ∂F :=
    mul_nonneg (by positivity) (integral_nonneg fun t => NNReal.coe_nonneg t)
  obtain ⟨C, hC, h⟩ := meanTime_le_add_meanRate hT hI hE hA (IsIIDWeights.meanTime_le hP hF) hμ₀
    (lt_min ha one_pos) (min_le_right _ _) hc (hcheap.mono_rate (min_le_left _ _)) hC₁ hc₁ hlow
  have hκ : 0 < 1 + 2 * Real.log 3 / Real.log 2 := by
    have : 0 < 2 * Real.log 3 / Real.log 2 :=
      div_pos (by have := Real.log_pos (show (1 : ℝ) < 3 by norm_num); linarith)
        (Real.log_pos (by norm_num))
    linarith
  refine ⟨C * Real.sqrt (1 + 2 * Real.log 3 / Real.log 2), mul_pos hC (Real.sqrt_pos.2 hκ),
    fun μ hμ x hx => ?_⟩
  obtain rfl := isTimeConstant_unique hμ₀ hμ
  refine ⟨le_meanTime hT hI hμ₀ x, ?_⟩
  have hrate := meanRate_le_sqrt_mul (sqrt_two_le_norm_point hx)
  calc ∫ ω, (passageTime ω 0 x : ℝ) ∂P ≤ μ₀.1 (point x) + C * meanRate ‖point x‖ :=
        h x hx.le
    _ ≤ μ₀.1 (point x) + C * (Real.sqrt (1 + 2 * Real.log 3 / Real.log 2) *
          Real.sqrt (‖point x‖ * Real.log ‖point x‖)) := by
        gcongr
    _ = μ₀.1 (point x) + C * Real.sqrt (1 + 2 * Real.log 3 / Real.log 2) *
          √(‖point x‖ * Real.log ‖point x‖) := by
        ring

end CurvatureVariance.Infra.FPP
