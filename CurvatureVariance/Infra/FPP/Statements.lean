/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Inputs.L1Norm
public import CurvatureVariance.Statements.Weights.AssumptionW
public import CurvatureVariance.Infra.FPP.ConcentrationADH
public import CurvatureVariance.Infra.FPP.Mean
public import CurvatureVariance.Infra.FPP.Symmetry
public import CurvatureVariance.Infra.FPP.TimeConstant
public import CurvatureVariance.Infra.Kesten.Estimate
import CurvatureVariance.Statements.Inputs.MeasureExistsIsPathWalkCostLtLe

/-!
# The cited first-passage statements

The cited results [ADH, Theorems 2.1, 2.5, 3.13 and 3.33] and the existence and uniqueness of the
time constant, each with exactly the conclusion of its statement in the namespace
`CurvatureVariance`. They are first proved under the hypothesis `KestenEstimate m F` (the
conclusion of Kesten's estimate, [ADH, p. 77]); Kesten's estimate
(`CurvatureVariance.Infra.Kesten.measure_exists_isPath_walkCost_lt_le`) discharges it, and the last
section states each result outright with exactly the statement in `CurvatureVariance`, which then
follows by `exact`:

* `exists_isTimeConstant` (`CurvatureVariance.exists_isTimeConstant`);
* `isTimeConstant_unique` (`CurvatureVariance.IsTimeConstant.unique`; in
  `CurvatureVariance.Infra.FPP.TimeConstant`);
* `exists_tendsto_passageTime_div` ([ADH, Theorem 2.1]);
* `timeConstant_pos` ([ADH, Theorem 2.5]);
* `pos_iff_forall_pos_of_isLatticeSymmetric` ([ADH, Theorem 2.6]; in
  `CurvatureVariance.Infra.FPP.Symmetry`);
* `measure_abs_passageTime_sub_integral_le` ([ADH, Theorem 3.13], with the hypothesis `x ≠ 0`,
  which [ADH, p. 49] leaves implicit);
* `integral_passageTime_le_timeConstant_add` ([ADH, Theorem 3.33]).

The conditional forms:

`exists_isTimeConstant_of_kestenEstimate`, `exists_tendsto_passageTime_div_of_kestenEstimate`,
`timeConstant_pos_of_kestenEstimate`, `measure_abs_passageTime_sub_integral_le_of_kestenEstimate`
and `integral_passageTime_le_timeConstant_add_of_kestenEstimate`.

The `ℓ¹` norm `l1Norm` is the definition `CurvatureVariance.l1Norm`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

theorem l1Norm_eq_l1Dist (x : Vertex m) : l1Norm x = l1Dist 0 x :=
  (l1Dist_zero_eq x).symm

/-- The hypotheses of the concentration chain, from (W) and Kesten's estimate. -/
theorem exists_concHyp_of_kestenEstimate {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    (hW : AssumptionW m F) (hK : KestenEstimate m F) :
    ∃ α a c : ℝ, ∀ (P : Measure (Config m)) [IsProbabilityMeasure P], IsIIDWeights P F →
      ConcHyp P F α a c := by
  obtain ⟨⟨α, hα, hexp⟩, -⟩ := hW
  obtain ⟨a, c, ha, hc, hcheap⟩ := KestenEstimate.exists_cheapPaths hK
  exact ⟨α, a, c, fun P _ hP => ⟨hP, hα, hexp, ha, hc, hcheap P hP⟩⟩

/-! ### The time constant -/

/-- **The time constant exists and is a norm** (`CurvatureVariance.exists_isTimeConstant`),
conditional on Kesten's estimate. -/
theorem exists_isTimeConstant_of_kestenEstimate (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hW : AssumptionW m F) (hK : KestenEstimate m F) (P : Measure (Config m))
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) :
    ∃ μ : PtNorm m, IsTimeConstant P μ := by
  obtain ⟨α, a, c, hconc⟩ := exists_concHyp_of_kestenEstimate hW hK
  have h := hconc P hP
  obtain ⟨μ, hμ, -⟩ := exists_isTimeConstant_of_cheapPaths
    (integrable_coe_of_exp h.α_pos h.expMoment) hP h.a_pos h.c_pos h.cheap
    (div_pos h.tailRate_pos (by positivity)) h.passageTimeConcentration
  exact ⟨μ, hμ⟩

/-- **[ADH, Theorem 2.1]** under (W), conditional on Kesten's estimate: `T(0, n e₁)/n → µ(e₁) ≥ 0`
almost surely and in `L¹`. -/
theorem exists_tendsto_passageTime_div_of_kestenEstimate (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (hK : KestenEstimate m F)
    (P : Measure (Config m)) [IsProbabilityMeasure P] (hP : IsIIDWeights P F) :
    ∃ μ₁ : ℝ, 0 ≤ μ₁ ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (passageTime ω 0 ((n : ℤ), 0) : ℝ) / n) atTop (𝓝 μ₁)) ∧
      Tendsto (fun n : ℕ => ∫ ω, |(passageTime ω 0 ((n : ℤ), 0) : ℝ) / n - μ₁| ∂P) atTop
        (𝓝 0) := by
  obtain ⟨α, a, c, hconc⟩ := exists_concHyp_of_kestenEstimate hW hK
  have h := hconc P hP
  exact exists_tendsto_passageTime_div_of_cheapPaths
    (integrable_coe_of_exp h.α_pos h.expMoment) hP h.a_pos h.c_pos h.cheap
    (div_pos h.tailRate_pos (by positivity)) h.passageTimeConcentration

/-- **[ADH, Theorem 2.5]** in the direction used, conditional on Kesten's estimate: the time
constant `µ(e₁)` is positive. -/
theorem timeConstant_pos_of_kestenEstimate (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hK : KestenEstimate m F) (P : Measure (Config m)) [IsProbabilityMeasure P]
    (hP : IsIIDWeights P F) (μ₁ : ℝ)
    (hμ₁ : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (passageTime ω 0 ((n : ℤ), 0) : ℝ) / n) atTop (𝓝 μ₁)) :
    0 < μ₁ := by
  obtain ⟨a, c, ha, hc, hcheap⟩ := KestenEstimate.exists_cheapPaths hK
  exact timeConstant_pos_of_cheapPaths ha hc (hcheap P hP) μ₁ hμ₁

/-! ### Concentration of the passage time -/

/-- **[ADH, Theorem 3.13]** under (W), conditional on Kesten's estimate, with the hypothesis
`x ≠ 0`, which [ADH] leaves implicit: `T(0, x)` is integrable, its upper deviations at scale
`‖x‖₁^{1/2}` have Gaussian tails `e^{-C₁ t²}` for `t ≤ C₂ ‖x‖₁^{1/2}`, and its lower deviations
for all `t ≥ 0`. Here `C₂ = 1`. -/
theorem measure_abs_passageTime_sub_integral_le_of_kestenEstimate (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (hK : KestenEstimate m F) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ (P : Measure (Config m)) [IsProbabilityMeasure P],
      IsIIDWeights P F → ∀ x : Vertex m, x ≠ 0 →
        Integrable (fun ω => (passageTime ω 0 x : ℝ)) P ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ C₂ * √(l1Norm x : ℝ) →
          P {ω | t * √(l1Norm x : ℝ) ≤
              (passageTime ω 0 x : ℝ) - ∫ ω', (passageTime ω' 0 x : ℝ) ∂P} ≤
            ENNReal.ofReal (Real.exp (-(C₁ * t ^ 2)))) ∧
        (∀ t : ℝ, 0 ≤ t →
          P {ω | (passageTime ω 0 x : ℝ) - ∫ ω', (passageTime ω' 0 x : ℝ) ∂P ≤
              -(t * √(l1Norm x : ℝ))} ≤
            ENNReal.ofReal (Real.exp (-(C₁ * t ^ 2)))) := by
  obtain ⟨α, a, c, hconc⟩ := exists_concHyp_of_kestenEstimate hW hK
  have h₀ := hconc _ (isIIDWeights_infinitePi F)
  refine ⟨gaussRate F α a c, 1, h₀.gaussRate_pos, one_pos, fun P _ hP x hx => ?_⟩
  rw [l1Norm_eq_l1Dist]
  exact (hconc P hP).passageTime_concentration_adh hx

/-! ### The mean passage time -/

/-- **[ADH, Theorem 3.33]** under (W), conditional on Kesten's estimate: there is `C` with
`µ(x) ≤ E T(0,x) ≤ µ(x) + C (|x| log |x|)^{1/2}` for `|x| > 1`. The constant is that of the
product law `F^{⊗E}`, which is the only law with independent weights of law `F`. -/
theorem integral_passageTime_le_timeConstant_add_of_kestenEstimate (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (hK : KestenEstimate m F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Config m)) [IsProbabilityMeasure P],
      IsIIDWeights P F → ∀ μ : PtNorm m, IsTimeConstant P μ → ∀ x : Vertex m, 1 < ‖point x‖ →
        μ.1 (point x) ≤ ∫ ω, (passageTime ω 0 x : ℝ) ∂P ∧
          ∫ ω, (passageTime ω 0 x : ℝ) ∂P ≤
            μ.1 (point x) + C * √(‖point x‖ * Real.log ‖point x‖) := by
  obtain ⟨α, a, c, hconc⟩ := exists_concHyp_of_kestenEstimate hW hK
  have hP₀ := isIIDWeights_infinitePi (m := m) F
  have h := hconc _ hP₀
  have hS := sqExpConst_nonneg F α
  obtain ⟨C, hC, hCP⟩ := integral_passageTime_le_timeConstant_add_of_cheapPaths
    (integrable_coe_of_exp h.α_pos h.expMoment) hP₀ h.a_pos h.c_pos h.cheap zero_le_one
    (div_pos one_pos (by linarith)) (minCostLowerTail h.α_pos h.expMoment hP₀)
  refine ⟨C, hC, fun P _ hP => ?_⟩
  obtain rfl := IsIIDWeights.eq_infinitePi hP
  exact hCP

/-! ### The statements outright -/

/-- **Kesten's estimate** in the form `KestenEstimate`, from `F(0) < p_c`. -/
theorem kestenEstimate {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (h0 : F {0} < ENNReal.ofReal (bondCriticalProb m)) : KestenEstimate m F :=
  CurvatureVariance.measure_exists_isPath_walkCost_lt_le hm F h0

/-- **The time constant exists and is a norm** ([ADH, Theorems 2.1, 2.5 and 2.6]): exactly the
statement `CurvatureVariance.exists_isTimeConstant`. -/
theorem exists_isTimeConstant {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hW : AssumptionW m F) (P : Measure (Config m)) [IsProbabilityMeasure P]
    (hP : IsIIDWeights P F) :
    ∃ μ : PtNorm m, IsTimeConstant P μ :=
  exists_isTimeConstant_of_kestenEstimate F hW (kestenEstimate hm F hW.2) P hP

/-- **[ADH, Theorem 2.1]**, specialized to (W): exactly the statement
`CurvatureVariance.exists_tendsto_passageTime_div`. -/
theorem exists_tendsto_passageTime_div {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (P : Measure (Config m))
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) :
    ∃ μ₁ : ℝ, 0 ≤ μ₁ ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (passageTime ω 0 ((n : ℤ), 0) : ℝ) / n) atTop (𝓝 μ₁)) ∧
      Tendsto (fun n : ℕ => ∫ ω, |(passageTime ω 0 ((n : ℤ), 0) : ℝ) / n - μ₁| ∂P) atTop
        (𝓝 0) :=
  exists_tendsto_passageTime_div_of_kestenEstimate F hW (kestenEstimate hm F hW.2) P hP

/-- **[ADH, Theorem 2.5]**, specialized to (W), the direction the paper uses: exactly the
statement `CurvatureVariance.timeConstant_pos`. -/
theorem timeConstant_pos {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hW : AssumptionW m F) (P : Measure (Config m)) [IsProbabilityMeasure P]
    (hP : IsIIDWeights P F) (μ₁ : ℝ)
    (hμ₁ : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (passageTime ω 0 ((n : ℤ), 0) : ℝ) / n) atTop (𝓝 μ₁)) :
    0 < μ₁ :=
  timeConstant_pos_of_kestenEstimate F (kestenEstimate hm F hW.2) P hP μ₁ hμ₁

/-- **[ADH, Theorem 3.13]**, specialized to (W), with the hypothesis `x ≠ 0`, which [ADH, p. 49]
leaves implicit: exactly the statement `CurvatureVariance.measure_abs_passageTime_sub_integral_le`.
-/
theorem measure_abs_passageTime_sub_integral_le {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ (P : Measure (Config m)) [IsProbabilityMeasure P],
      IsIIDWeights P F → ∀ x : Vertex m, x ≠ 0 →
        Integrable (fun ω => (passageTime ω 0 x : ℝ)) P ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ C₂ * √(l1Norm x : ℝ) →
          P {ω | t * √(l1Norm x : ℝ) ≤
              (passageTime ω 0 x : ℝ) - ∫ ω', (passageTime ω' 0 x : ℝ) ∂P} ≤
            ENNReal.ofReal (Real.exp (-(C₁ * t ^ 2)))) ∧
        (∀ t : ℝ, 0 ≤ t →
          P {ω | (passageTime ω 0 x : ℝ) - ∫ ω', (passageTime ω' 0 x : ℝ) ∂P ≤
              -(t * √(l1Norm x : ℝ))} ≤
            ENNReal.ofReal (Real.exp (-(C₁ * t ^ 2)))) :=
  measure_abs_passageTime_sub_integral_le_of_kestenEstimate F hW (kestenEstimate hm F hW.2)

/-- **[ADH, Theorem 3.33]**, specialized to (W): exactly the statement
`CurvatureVariance.integral_passageTime_le_timeConstant_add`. -/
theorem integral_passageTime_le_timeConstant_add {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Config m)) [IsProbabilityMeasure P],
      IsIIDWeights P F → ∀ μ : PtNorm m, IsTimeConstant P μ → ∀ x : Vertex m, 1 < ‖point x‖ →
        μ.1 (point x) ≤ ∫ ω, (passageTime ω 0 x : ℝ) ∂P ∧
          ∫ ω, (passageTime ω 0 x : ℝ) ∂P ≤
            μ.1 (point x) + C * √(‖point x‖ * Real.log ‖point x‖) :=
  integral_passageTime_le_timeConstant_add_of_kestenEstimate F hW (kestenEstimate hm F hW.2)

end CurvatureVariance.Infra.FPP
