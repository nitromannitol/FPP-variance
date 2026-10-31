/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.ConcentrationSetup

/-!
# Tails of the passage time

Under `ConcHyp P F α a c` (independent weights with law `F`, an exponential moment at rate `α`, the
cheap-path estimate at rate `a` with decay `c`), for vertices at `ℓ¹` distance `n`:

* **lower tail at every level**: `P(T - ET ≤ -z) ≤ (D + 1) e^{-c_L z²/(1+n)}`
  (`ConcHyp.measure_passageTime_sub_le_neg_le`);
* **upper tail**: `P(T - ET ≥ z) ≤ C_U e^{-c_U min(z²/(1+n), z)}`
  (`ConcHyp.measure_le_passageTime_sub_le`),

with constants `D, c_L, c_U, C_U` depending only on `F, α, a, c`. The proof compares `T` with the
restricted passage time `T_R` (`CurvatureVariance.Infra.FPP.ConcentrationSetup`), whose tails are
those of a minimum of edge-set costs (`CurvatureVariance.Infra.FPP.MinCostTails`); large upper
deviations come from the Chernoff bound for a coordinate path.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- The mean `m₁ = E τ` of the weights. -/
noncomputable def weightMean (F : Measure ℝ≥0) : ℝ := ∫ x, (x : ℝ) ∂F

theorem weightMean_nonneg (F : Measure ℝ≥0) : 0 ≤ weightMean F :=
  integral_nonneg fun x => NNReal.coe_nonneg x

/-- The rate `c_L` of the lower tail. -/
noncomputable def lowerRate (F : Measure ℝ≥0) (α a c : ℝ) : ℝ :=
  min (1 / (4 * (sqExpConst F α + 1) * ((restrictFactor F α a c : ℝ) + 1)))
    (1 / (weightMean F ^ 2 + 1))

/-- The rate `c_U` of the upper tail. -/
noncomputable def upperRate (F : Measure ℝ≥0) (α a c : ℝ) : ℝ :=
  min (min (1 / (16 * (sqExpConst F α + 1) * ((restrictFactor F α a c : ℝ) + 1))) (α / 8))
    (1 / (2 * log (expMom F α) / α + 1))

/-- The constant `C_U` of the upper tail. -/
noncomputable def upperConst (F : Measure ℝ≥0) (α a c : ℝ) : ℝ :=
  (badConst c + 1) * exp (2 * meanGap α c * upperRate F α a c)

section Hyp

variable {P : Measure (Config m)} {F : Measure ℝ≥0} [IsProbabilityMeasure F] {α a c : ℝ}

omit [IsProbabilityMeasure F] in
theorem ConcHyp.lowerRate_pos (_h : ConcHyp P F α a c) : 0 < lowerRate F α a c := by
  have := sqExpConst_nonneg F α
  unfold lowerRate
  exact lt_min (by positivity) (by positivity)

theorem ConcHyp.upperRate_pos (h : ConcHyp P F α a c) : 0 < upperRate F α a c := by
  have := sqExpConst_nonneg F α
  have hL := h.log_expMom_nonneg
  have hα := h.α_pos
  unfold upperRate
  exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)

omit [IsProbabilityMeasure F] in
theorem ConcHyp.upperRate_le_half (h : ConcHyp P F α a c) : upperRate F α a c ≤ α / 2 := by
  have h1 : upperRate F α a c ≤ α / 8 :=
    (min_le_left _ _).trans (min_le_right _ _)
  linarith [h.α_pos]

/-- `R + 1 ≤ (K₀ + 1)(1 + n)`. -/
theorem restrictLength_add_one_le (F : Measure ℝ≥0) (α a c : ℝ) (u v : Vertex m) :
    (restrictLength F α a c u v : ℝ) + 1 ≤
      ((restrictFactor F α a c : ℝ) + 1) * (1 + l1Dist u v) := by
  simp only [restrictLength]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) (l1Dist u v),
    Nat.cast_nonneg (α := ℝ) (restrictFactor F α a c)]

/-- **Lower tail of the passage time at every level**:
`P(T - ET ≤ -z) ≤ (D + 1) e^{-c_L z²/(1+n)}`. -/
theorem ConcHyp.measure_passageTime_sub_le_neg_le (h : ConcHyp P F α a c) (u v : Vertex m)
    {z : ℝ} (hz : 0 ≤ z) :
    P {ω | (passageTime ω u v : ℝ) - ∫ ω', (passageTime ω' u v : ℝ) ∂P ≤ -z} ≤
      ENNReal.ofReal ((badConst c + 1) *
        exp (-(lowerRate F α a c * (z ^ 2 / (1 + l1Dist u v))))) := by
  have := IsIIDWeights.isProbabilityMeasure h.iid
  set n := l1Dist u v
  set EW := ∫ ω, (passageTime ω u v : ℝ) ∂P
  set EZ := ∫ ω, restrictedTime F α a c u v ω ∂P
  set cL := lowerRate F α a c
  have hN : 0 < 1 + (n : ℝ) := by positivity
  have hD := h.badConst_pos
  have hm₁ := weightMean_nonneg F
  have hEW : EW ≤ weightMean F * n := by
    have := IsIIDWeights.integral_passageTime_le h.iid
      (integrable_coe_of_exp h.α_pos h.expMoment) u v
    simp only [EW, weightMean]; linarith
  rcases lt_or_ge EW z with hzn | hzn
  · have hempty : {ω | (passageTime ω u v : ℝ) - EW ≤ -z} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      linarith [NNReal.coe_nonneg (passageTime ω u v)]
    rw [hempty, measure_empty]
    exact zero_le
  have hEWZ : EW ≤ EZ := h.integral_passageTime_le_integral_restrictedTime u v
  have hsub : {ω | (passageTime ω u v : ℝ) - EW ≤ -z} ⊆
      {ω | restrictedTime F α a c u v ω ≠ passageTime ω u v} ∪
        {ω | restrictedTime F α a c u v ω ≤ EZ - z} := by
    intro ω hω
    by_cases hc : restrictedTime F α a c u v ω = passageTime ω u v
    · right
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [hc]
      linarith
    · exact Or.inl hc
  have hlow := measure_minCost_le_integral_sub h.α_pos h.expMoment h.iid
    (pathFamily u v (restrictLength F α a c u v))
    (pathFamily_nonempty (l1Dist_le_restrictLength F α a c u v))
    (fun S hS => card_le_restrictLength hS) hz
  have hcL : 0 < cL := h.lowerRate_pos
  -- the bad event: `κ(1+n) ≥ c_L z²/(1+n)` since `z ≤ m₁ n`
  have h1 : exp (-(decayRate F α * ((n : ℝ) + 1))) ≤ exp (-(cL * (z ^ 2 / (1 + n)))) := by
    refine exp_le_exp.2 (neg_le_neg ?_)
    have hκ := h.one_le_decayRate
    have hcL2 : cL ≤ 1 / (weightMean F ^ 2 + 1) := min_le_right _ _
    have hz2 : z ^ 2 ≤ (weightMean F ^ 2 + 1) * (1 + n) ^ 2 := by
      have : z ≤ weightMean F * (1 + n) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      nlinarith [sq_nonneg z, sq_nonneg (weightMean F * (1 + n))]
    have hq : cL * (z ^ 2 / (1 + n)) ≤ 1 + n := by
      rw [mul_div_assoc', div_le_iff₀ hN]
      calc cL * z ^ 2 ≤ 1 / (weightMean F ^ 2 + 1) * ((weightMean F ^ 2 + 1) * (1 + n) ^ 2) :=
            mul_le_mul hcL2 hz2 (sq_nonneg z) (by positivity)
        _ = (1 + n) * (1 + n) := by field_simp
    calc cL * (z ^ 2 / (1 + n)) ≤ 1 + n := hq
      _ ≤ decayRate F α * ((n : ℝ) + 1) := by nlinarith
  -- the minimum: `4 (B + 1)(R + 1) c_L ≤ 1 + n`
  have h2 : exp (-(z ^ 2 / (4 * ((sqExpConst F α + 1) *
      ((restrictLength F α a c u v : ℝ) + 1))))) ≤ exp (-(cL * (z ^ 2 / (1 + n)))) := by
    refine exp_le_exp.2 (neg_le_neg ?_)
    have hR := restrictLength_add_one_le F α a c u v
    have hB := sqExpConst_nonneg F α
    have hcL1 : cL ≤ 1 / (4 * (sqExpConst F α + 1) * ((restrictFactor F α a c : ℝ) + 1)) :=
      min_le_left _ _
    have hden : 4 * ((sqExpConst F α + 1) * ((restrictLength F α a c u v : ℝ) + 1)) ≤
        4 * (sqExpConst F α + 1) * ((restrictFactor F α a c : ℝ) + 1) * (1 + n) := by
      nlinarith
    have hpos : 0 < 4 * ((sqExpConst F α + 1) * ((restrictLength F α a c u v : ℝ) + 1)) := by
      positivity
    calc cL * (z ^ 2 / (1 + n))
        ≤ 1 / (4 * (sqExpConst F α + 1) * ((restrictFactor F α a c : ℝ) + 1)) *
            (z ^ 2 / (1 + n)) := mul_le_mul_of_nonneg_right hcL1 (by positivity)
      _ = z ^ 2 / (4 * (sqExpConst F α + 1) * ((restrictFactor F α a c : ℝ) + 1) * (1 + n)) := by
          field_simp
      _ ≤ z ^ 2 / (4 * ((sqExpConst F α + 1) * ((restrictLength F α a c u v : ℝ) + 1))) :=
          div_le_div_of_nonneg_left (sq_nonneg z) hpos hden
  calc _ ≤ P ({ω | restrictedTime F α a c u v ω ≠ passageTime ω u v} ∪
        {ω | restrictedTime F α a c u v ω ≤ EZ - z}) := measure_mono hsub
    _ ≤ P {ω | restrictedTime F α a c u v ω ≠ passageTime ω u v} +
        P {ω | restrictedTime F α a c u v ω ≤ EZ - z} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (badConst c * exp (-(decayRate F α * ((n : ℝ) + 1)))) +
        ENNReal.ofReal (exp (-(z ^ 2 / (4 * ((sqExpConst F α + 1) *
          ((restrictLength F α a c u v : ℝ) + 1)))))) :=
        add_le_add (h.measure_restrictedTime_ne_le u v) hlow
    _ ≤ ENNReal.ofReal (badConst c * exp (-(cL * (z ^ 2 / (1 + n))))) +
        ENNReal.ofReal (exp (-(cL * (z ^ 2 / (1 + n))))) :=
        add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h1 hD.le))
          (ENNReal.ofReal_le_ofReal h2)
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (exp_pos _).le]
        ring_nf

/-- **Upper tail of the passage time**: `P(T - ET ≥ z) ≤ C_U e^{-c_U min(z²/(1+n), z)}`. -/
theorem ConcHyp.measure_le_passageTime_sub_le (h : ConcHyp P F α a c) (u v : Vertex m)
    {z : ℝ} (hz : 0 ≤ z) :
    P {ω | z ≤ (passageTime ω u v : ℝ) - ∫ ω', (passageTime ω' u v : ℝ) ∂P} ≤
      ENNReal.ofReal (upperConst F α a c *
        exp (-(upperRate F α a c * min (z ^ 2 / (1 + l1Dist u v)) z))) := by
  have := IsIIDWeights.isProbabilityMeasure h.iid
  set n := l1Dist u v
  set EW := ∫ ω, (passageTime ω u v : ℝ) ∂P
  set EZ := ∫ ω, restrictedTime F α a c u v ω ∂P
  set cU := upperRate F α a c
  set q := min (z ^ 2 / (1 + n)) z
  set δ₀ := meanGap α c
  have hα := h.α_pos
  have hcU : 0 < cU := h.upperRate_pos
  have hN : 0 < 1 + (n : ℝ) := by positivity
  have hD := h.badConst_pos
  have hqz : q ≤ z := min_le_right _ _
  have hq0 : 0 ≤ q := le_min (by positivity) hz
  have hδ₀ : 0 ≤ δ₀ := by simp only [δ₀, meanGap]; positivity
  have hL := h.log_expMom_nonneg
  have hM := h.one_le_expMom
  -- every bound of the form `D' e^{-c_U q}` with `D' ≤ D + 1` suffices
  have hfin : ∀ y : ℝ, y ≤ (badConst c + 1) * exp (-(cU * q)) →
      y ≤ upperConst F α a c * exp (-(cU * q)) := by
    intro y hy
    refine hy.trans (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
    simp only [upperConst]
    have : 1 ≤ exp (2 * δ₀ * cU) := one_le_exp (by positivity)
    nlinarith
  rcases lt_or_ge z (2 * δ₀) with hzs | hzs
  · -- small deviations
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [upperConst]
    rw [mul_assoc, ← exp_add]
    have : 0 ≤ 2 * δ₀ * cU + -(cU * q) := by nlinarith
    nlinarith [one_le_exp this]
  obtain ⟨p, hp, hl⟩ := exists_isPath_length_eq_l1Dist u v
  rcases le_or_gt (2 * log (expMom F α) / α * n) z with hzb | hzb
  · -- large deviations: Chernoff for a coordinate path
    have hEW : 0 ≤ EW := integral_nonneg fun ω => NNReal.coe_nonneg _
    have hsub : {ω | z ≤ (passageTime ω u v : ℝ) - EW} ⊆ {ω | z ≤ (walkCost ω p : ℝ)} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have := passageTime_le_restrictedTime (F := F) (α := α) (a := a) (c := c) u v ω
      have := restrictedTime_le_walkCost (F := F) (α := α) (a := a) (c := c) ω p hp hl
      linarith
    refine (measure_mono hsub).trans ((IsIIDWeights.measure_le_walkCost_le h.iid p
      hp.isTrail.edges_nodup hα.le h.expMoment z).trans ?_)
    refine ENNReal.ofReal_le_ofReal (hfin _ ?_)
    rw [hl]
    have hMn : (expMom F α) ^ n = exp (n * log (expMom F α)) := by
      rw [← exp_log (show 0 < expMom F α by linarith), ← exp_nat_mul, log_exp]
    have hz' : (n : ℝ) * log (expMom F α) ≤ α * z / 2 := by
      have := hzb
      rw [div_mul_eq_mul_div, div_le_iff₀ hα] at this
      linarith
    have hcUα := h.upperRate_le_half
    calc exp (-α * z) * expMom F α ^ n = exp (-α * z + n * log (expMom F α)) := by
          rw [hMn, ← exp_add]
      _ ≤ 1 * exp (-(cU * q)) := by
          rw [one_mul]; exact exp_le_exp.2 (by nlinarith)
      _ ≤ (badConst c + 1) * exp (-(cU * q)) :=
          mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le
  · -- moderate deviations: compare with the restricted passage time
    have hD₀ := h.integral_restrictedTime_sub_le u v
    have hsub : {ω | z ≤ (passageTime ω u v : ℝ) - EW} ⊆
        {ω | restrictedTime F α a c u v ω ≠ passageTime ω u v} ∪
          {ω | EZ + z / 2 ≤ restrictedTime F α a c u v ω} := by
      intro ω hω
      by_cases hc : restrictedTime F α a c u v ω = passageTime ω u v
      · right
        simp only [Set.mem_ofPred_eq] at hω ⊢
        rw [hc]
        linarith
      · exact Or.inl hc
    have hup := measure_integral_add_le_minCost h.α_pos h.expMoment h.iid
      (pathFamily u v (restrictLength F α a c u v))
      (pathFamily_nonempty (l1Dist_le_restrictLength F α a c u v))
      (fun S hS => card_le_restrictLength hS) (t := z / 2) (by positivity)
    -- the bad event: `c_U q ≤ κ(1+n)`
    have h1 : exp (-(decayRate F α * ((n : ℝ) + 1))) ≤ exp (-(cU * q)) := by
      refine exp_le_exp.2 (neg_le_neg ?_)
      have hκ := h.one_le_decayRate
      have hcU3 : cU ≤ 1 / (2 * log (expMom F α) / α + 1) := min_le_right _ _
      have hzL : z ≤ (2 * log (expMom F α) / α + 1) * (1 + n) := by
        have : 0 ≤ 2 * log (expMom F α) / α := by positivity
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      calc cU * q ≤ cU * z := mul_le_mul_of_nonneg_left hqz hcU.le
        _ ≤ 1 / (2 * log (expMom F α) / α + 1) * ((2 * log (expMom F α) / α + 1) * (1 + n)) :=
            mul_le_mul hcU3 hzL hz (by positivity)
        _ = 1 + n := by field_simp
        _ ≤ decayRate F α * ((n : ℝ) + 1) := by nlinarith
    -- the minimum
    have h2 : exp (-min ((z / 2) ^ 2 / (4 * ((sqExpConst F α + 1) *
        ((restrictLength F α a c u v : ℝ) + 1)))) (α / 2 * (z / 2) / 2)) ≤ exp (-(cU * q)) := by
      refine exp_le_exp.2 (neg_le_neg (le_min ?_ ?_))
      · have hR := restrictLength_add_one_le F α a c u v
        have hB := sqExpConst_nonneg F α
        have hcU1 : cU ≤ 1 / (16 * (sqExpConst F α + 1) * ((restrictFactor F α a c : ℝ) + 1)) :=
          (min_le_left _ _).trans (min_le_left _ _)
        have hden : 4 * ((sqExpConst F α + 1) * ((restrictLength F α a c u v : ℝ) + 1)) ≤
            4 * (sqExpConst F α + 1) * ((restrictFactor F α a c : ℝ) + 1) * (1 + n) := by
          nlinarith
        have hpos : 0 < 4 * ((sqExpConst F α + 1) * ((restrictLength F α a c u v : ℝ) + 1)) := by
          positivity
        calc cU * q ≤ cU * (z ^ 2 / (1 + n)) := mul_le_mul_of_nonneg_left (min_le_left _ _) hcU.le
          _ ≤ 1 / (16 * (sqExpConst F α + 1) * ((restrictFactor F α a c : ℝ) + 1)) *
                (z ^ 2 / (1 + n)) := mul_le_mul_of_nonneg_right hcU1 (by positivity)
          _ = (z / 2) ^ 2 / (4 * (sqExpConst F α + 1) * ((restrictFactor F α a c : ℝ) + 1) *
                (1 + n)) := by field_simp; ring
          _ ≤ (z / 2) ^ 2 / (4 * ((sqExpConst F α + 1) * ((restrictLength F α a c u v : ℝ) + 1))) :=
              div_le_div_of_nonneg_left (sq_nonneg _) hpos hden
      · have hcU2 : cU ≤ α / 8 := (min_le_left _ _).trans (min_le_right _ _)
        calc cU * q ≤ cU * z := mul_le_mul_of_nonneg_left hqz hcU.le
          _ ≤ α / 8 * z := mul_le_mul_of_nonneg_right hcU2 hz
          _ = α / 2 * (z / 2) / 2 := by ring
    calc _ ≤ P ({ω | restrictedTime F α a c u v ω ≠ passageTime ω u v} ∪
          {ω | EZ + z / 2 ≤ restrictedTime F α a c u v ω}) := measure_mono hsub
      _ ≤ P {ω | restrictedTime F α a c u v ω ≠ passageTime ω u v} +
          P {ω | EZ + z / 2 ≤ restrictedTime F α a c u v ω} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (badConst c * exp (-(decayRate F α * ((n : ℝ) + 1)))) +
          ENNReal.ofReal (exp (-min ((z / 2) ^ 2 / (4 * ((sqExpConst F α + 1) *
            ((restrictLength F α a c u v : ℝ) + 1)))) (α / 2 * (z / 2) / 2))) :=
          add_le_add (h.measure_restrictedTime_ne_le u v) hup
      _ ≤ ENNReal.ofReal (badConst c * exp (-(cU * q))) + ENNReal.ofReal (exp (-(cU * q))) :=
          add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h1 hD.le))
            (ENNReal.ofReal_le_ofReal h2)
      _ = ENNReal.ofReal ((badConst c + 1) * exp (-(cU * q))) := by
          rw [← ENNReal.ofReal_add (by positivity) (exp_pos _).le]
          ring_nf
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hfin _ le_rfl)

end Hyp

end CurvatureVariance.Infra.FPP
