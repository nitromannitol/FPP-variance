/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.ConcentrationRestricted
public import CurvatureVariance.Infra.FPP.MinCostTails

/-!
# The restricted passage time of the concentration argument

Fix independent weights with law `F` (`IsIIDWeights P F`), a finite exponential moment
`M = E e^{α τ} < ∞`, `α > 0`, and the cheap-path estimate `CheapPaths P a c` (from Kesten's
estimate). The data are bundled in `ConcHyp P F α a c`. Put `κ = log M + 1` and choose the factor
`K₀` with `c K₀ ≥ κ` and `α a K₀ ≥ κ + log M`. For vertices at `ℓ¹` distance `n`, the restricted
passage time `T_R` minimizes over the self-avoiding paths with at most `R = K₀ (1 + n)` edges. Then:

* `T ≤ T_R`, and `T_R ≤ Γ` for a coordinate path `Γ` of `n` edges;
* `P(T_R ≠ T) ≤ D e^{-κ(1+n)}`, `D = 1 + 1/(1 - e^{-c})` (`measure_restrictedTime_ne_le`);
* `0 ≤ E T_R - E T ≤ δ₀ = 4/α² + D/2` (`integral_restrictedTime_sub_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- The hypotheses of the concentration chain: independent weights with law `F`, a finite
exponential moment at rate `α > 0`, and the cheap-path estimate at rate `a > 0` with decay
`c > 0`. -/
structure ConcHyp (P : Measure (Config m)) (F : Measure ℝ≥0) (α a c : ℝ) : Prop where
  iid : IsIIDWeights P F
  α_pos : 0 < α
  expMoment : Integrable (fun x : ℝ≥0 => exp (α * x)) F
  a_pos : 0 < a
  c_pos : 0 < c
  cheap : CheapPaths P a c

/-- The exponential moment `M = E e^{α τ}`. -/
noncomputable def expMom (F : Measure ℝ≥0) (α : ℝ) : ℝ := ∫ x, exp (α * x) ∂F

theorem one_le_expMom {F : Measure ℝ≥0} [IsProbabilityMeasure F] {α : ℝ} (hα0 : 0 ≤ α)
    (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F) : 1 ≤ expMom F α := by
  have h : ∫ _x, (1 : ℝ) ∂F ≤ expMom F α :=
    integral_mono (integrable_const 1) hα fun x =>
      one_le_exp (mul_nonneg hα0 (NNReal.coe_nonneg x))
  simpa using h

/-- The decay rate `κ = log M + 1` of `P(T_R ≠ T)`. -/
noncomputable def decayRate (F : Measure ℝ≥0) (α : ℝ) : ℝ := log (expMom F α) + 1

/-- The constant `D = 1 + 1/(1 - e^{-c})`. -/
noncomputable def badConst (c : ℝ) : ℝ := 1 + 1 / (1 - exp (-c))

/-- The factor `K₀` of the restriction length `R = K₀ (1 + n)`. -/
noncomputable def restrictFactor (F : Measure ℝ≥0) (α a c : ℝ) : ℕ :=
  ⌈decayRate F α / c + (decayRate F α + log (expMom F α)) / (α * a)⌉₊ + 1

/-- The restriction length `R = K₀ (1 + |v - u|₁)`. -/
noncomputable def restrictLength (F : Measure ℝ≥0) (α a c : ℝ) (u v : Vertex m) : ℕ :=
  restrictFactor F α a c * (l1Dist u v + 1)

theorem l1Dist_le_restrictLength (F : Measure ℝ≥0) (α a c : ℝ) (u v : Vertex m) :
    l1Dist u v ≤ restrictLength F α a c u v := by
  unfold restrictLength restrictFactor
  nlinarith [Nat.zero_le ⌈decayRate F α / c + (decayRate F α + log (expMom F α)) / (α * a)⌉₊]

/-- The restricted passage time `T_R(u, v)`: the least cost of a self-avoiding path from `u` to
`v` with at most `R = K₀ (1 + |v - u|₁)` edges. -/
noncomputable def restrictedTime (F : Measure ℝ≥0) (α a c : ℝ) (u v : Vertex m) (ω : Config m) :
    ℝ :=
  minCost (pathFamily u v (restrictLength F α a c u v))
    (pathFamily_nonempty (l1Dist_le_restrictLength F α a c u v)) ω

section

variable {F : Measure ℝ≥0} {α a c : ℝ}

theorem measurable_restrictedTime (u v : Vertex m) :
    Measurable (restrictedTime (m := m) F α a c u v) :=
  measurable_minCost

theorem restrictedTime_nonneg (u v : Vertex m) (ω : Config m) :
    0 ≤ restrictedTime F α a c u v ω :=
  minCost_nonneg ω

/-- `T ≤ T_R`. -/
theorem passageTime_le_restrictedTime (u v : Vertex m) (ω : Config m) :
    (passageTime ω u v : ℝ) ≤ restrictedTime F α a c u v ω :=
  passageTime_le_minCost_pathFamily (l1Dist_le_restrictLength F α a c u v) ω

/-- `T_R ≤ Γ`, the cost of a coordinate path. -/
theorem restrictedTime_le_walkCost {u v : Vertex m} (ω : Config m)
    (p : (latticeGraph m).Walk u v) (hp : p.IsPath) (hl : p.length = l1Dist u v) :
    restrictedTime F α a c u v ω ≤ walkCost ω p :=
  minCost_pathFamily_le_walkCost (l1Dist_le_restrictLength F α a c u v) ω p hp
    (hl ▸ l1Dist_le_restrictLength F α a c u v)

/-- Every set of the family of `T_R` has at most `R` edges. -/
theorem card_le_restrictLength {u v : Vertex m} {S : Finset (Edge m)}
    (hS : S ∈ pathFamily u v (restrictLength F α a c u v)) :
    S.card ≤ restrictLength F α a c u v :=
  card_le_of_mem_pathFamily hS

end

/-! ### The comparison event -/

section Hyp

variable {P : Measure (Config m)} {F : Measure ℝ≥0} [IsProbabilityMeasure F] {α a c : ℝ}

theorem ConcHyp.one_le_expMom (h : ConcHyp P F α a c) : 1 ≤ expMom F α :=
  Infra.FPP.one_le_expMom h.α_pos.le h.expMoment

theorem ConcHyp.log_expMom_nonneg (h : ConcHyp P F α a c) : 0 ≤ log (expMom F α) :=
  log_nonneg h.one_le_expMom

theorem ConcHyp.one_le_decayRate (h : ConcHyp P F α a c) : 1 ≤ decayRate F α := by
  unfold decayRate; linarith [h.log_expMom_nonneg]

omit [IsProbabilityMeasure F] in
theorem ConcHyp.badConst_pos (h : ConcHyp P F α a c) : 0 < badConst c := by
  have : exp (-c) < 1 := exp_lt_one_iff.2 (by linarith [h.c_pos])
  unfold badConst
  have : 0 < 1 - exp (-c) := by linarith
  positivity

/-- The factor satisfies `c K₀ ≥ κ` and `α a K₀ ≥ κ + log M`. -/
theorem ConcHyp.restrictFactor_spec (h : ConcHyp P F α a c) :
    decayRate F α ≤ c * restrictFactor F α a c ∧
      decayRate F α + log (expMom F α) ≤ α * a * restrictFactor F α a c := by
  have hc := h.c_pos
  have hαa : 0 < α * a := mul_pos h.α_pos h.a_pos
  have hκ := h.one_le_decayRate
  have hL := h.log_expMom_nonneg
  set K := restrictFactor F α a c
  have hK : decayRate F α / c + (decayRate F α + log (expMom F α)) / (α * a) ≤ K := by
    have := Nat.le_ceil (decayRate F α / c + (decayRate F α + log (expMom F α)) / (α * a))
    simp only [K, restrictFactor]
    push_cast
    linarith
  have h1 : 0 ≤ (decayRate F α + log (expMom F α)) / (α * a) := by positivity
  have h2 : 0 ≤ decayRate F α / c := by positivity
  constructor
  · have : decayRate F α / c ≤ K := by linarith
    rwa [div_le_iff₀ hc, mul_comm] at this
  · have : (decayRate F α + log (expMom F α)) / (α * a) ≤ K := by linarith
    rwa [div_le_iff₀ hαa, mul_comm] at this

/-- **`T_R = T` except with probability at most `D e^{-κ(1+n)}`.** -/
theorem ConcHyp.measure_restrictedTime_ne_le (h : ConcHyp P F α a c) (u v : Vertex m) :
    P {ω | restrictedTime F α a c u v ω ≠ passageTime ω u v} ≤
      ENNReal.ofReal (badConst c * exp (-(decayRate F α * ((l1Dist u v : ℝ) + 1)))) := by
  set n := l1Dist u v
  set R := restrictLength F α a c u v
  set κ := decayRate F α
  set M := expMom F α
  have hR : (R : ℝ) = restrictFactor F α a c * ((n : ℝ) + 1) := by
    simp only [R, restrictLength]; push_cast; ring
  obtain ⟨hK1, hK2⟩ := h.restrictFactor_spec
  have hc := h.c_pos
  have hq : exp (-c) < 1 := exp_lt_one_iff.2 (by linarith)
  have hq' : 0 < 1 - exp (-c) := by linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL := h.log_expMom_nonneg
  have hM := h.one_le_expMom
  have hb := measure_minCost_pathFamily_ne_le h.iid hc h.cheap h.α_pos.le h.expMoment
    (l1Dist_le_restrictLength F α a c u v)
  refine hb.trans ?_
  -- the two terms
  have h1 : exp (-(c * (R + 1))) / (1 - exp (-c)) ≤ 1 / (1 - exp (-c)) * exp (-(κ * (n + 1))) := by
    rw [div_eq_mul_inv, one_div, mul_comm]
    refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (inv_nonneg.2 hq'.le)
    rw [hR]
    nlinarith
  have h2 : exp (-α * (a * R)) * M ^ n ≤ exp (-(κ * (n + 1))) := by
    rw [← exp_log (show 0 < M by linarith), ← exp_nat_mul, ← exp_add]
    refine exp_le_exp.2 ?_
    rw [hR]
    have : α * (a * (restrictFactor F α a c * ((n : ℝ) + 1))) =
        α * a * restrictFactor F α a c * ((n : ℝ) + 1) := by ring
    rw [neg_mul, this]
    nlinarith
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : badConst c * exp (-(κ * (n + 1))) =
      1 / (1 - exp (-c)) * exp (-(κ * (n + 1))) + exp (-(κ * (n + 1))) := by
    unfold badConst; ring
  rw [this]
  exact add_le_add h1 h2

/-! ### The means -/

/-- With a finite exponential moment, the passage time and `T_R` are integrable. -/
theorem ConcHyp.integrable_restrictedTime (h : ConcHyp P F α a c) (u v : Vertex m) :
    Integrable (restrictedTime F α a c u v) P := by
  have := IsIIDWeights.isProbabilityMeasure h.iid
  obtain ⟨p, hp, hl⟩ := exists_isPath_length_eq_l1Dist u v
  have hΓ := IsIIDWeights.integrable_walkCost h.iid p (integrable_coe_of_exp h.α_pos h.expMoment)
  refine hΓ.mono' (measurable_restrictedTime u v).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (restrictedTime_nonneg u v ω)]
  exact restrictedTime_le_walkCost ω p hp hl

theorem ConcHyp.integrable_passageTime (h : ConcHyp P F α a c) (u v : Vertex m) :
    Integrable (fun ω => (passageTime ω u v : ℝ)) P :=
  IsIIDWeights.integrable_passageTime h.iid (integrable_coe_of_exp h.α_pos h.expMoment) u v

/-- `E T ≤ E T_R`. -/
theorem ConcHyp.integral_passageTime_le_integral_restrictedTime (h : ConcHyp P F α a c)
    (u v : Vertex m) :
    ∫ ω, (passageTime ω u v : ℝ) ∂P ≤ ∫ ω, restrictedTime F α a c u v ω ∂P :=
  integral_mono (h.integrable_passageTime u v) (h.integrable_restrictedTime u v)
    (passageTime_le_restrictedTime u v)

/-- `x² ≤ (8/α²) e^{α x/2}` for `x ≥ 0`, `α > 0`. -/
theorem sq_le_exp_half {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) :
    x ^ 2 ≤ 8 / α ^ 2 * exp (α / 2 * x) := by
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ α / 2 * x by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- The constant `δ₀ = 4/α² + D/2` of `E T_R - E T ≤ δ₀`. -/
noncomputable def meanGap (α c : ℝ) : ℝ := 4 / α ^ 2 + badConst c / 2

/-- **`E T_R - E T ≤ δ₀`.** -/
theorem ConcHyp.integral_restrictedTime_sub_le (h : ConcHyp P F α a c) (u v : Vertex m) :
    (∫ ω, restrictedTime F α a c u v ω ∂P) - ∫ ω, (passageTime ω u v : ℝ) ∂P ≤ meanGap α c := by
  have := IsIIDWeights.isProbabilityMeasure h.iid
  obtain ⟨p, hp, hl⟩ := exists_isPath_length_eq_l1Dist u v
  have hα := h.α_pos
  have hnodup : p.edges.Nodup := hp.isTrail.edges_nodup
  set n := l1Dist u v
  set M := expMom F α
  set κ := decayRate F α
  have hM := h.one_le_expMom
  have hL := h.log_expMom_nonneg
  set Γ : Config m → ℝ := fun ω => (walkCost ω p : ℝ)
  set Z := restrictedTime F α a c u v
  set W : Config m → ℝ := fun ω => (passageTime ω u v : ℝ)
  set B := {ω | Z ω ≠ W ω}
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun (measurable_restrictedTime u v) (measurable_passageTime_real u v)).compl
  have hZi := h.integrable_restrictedTime u v
  have hWi := h.integrable_passageTime u v
  -- the half-rate exponential moment of `Γ`
  have hhalf : Integrable (fun x : ℝ≥0 => exp (α / 2 * x)) F :=
    integrable_exp_mul_of_le (by linarith) h.expMoment
  have hEi : Integrable (fun ω => exp (α / 2 * Γ ω)) P :=
    IsIIDWeights.integrable_exp_mul_walkCost h.iid p hnodup hhalf
  have hE : ∫ ω, exp (α / 2 * Γ ω) ∂P = (∫ x, exp (α / 2 * x) ∂F) ^ n := by
    have := IsIIDWeights.mgf_walkCost h.iid p hnodup (α / 2)
    rw [mgf, mgf, hl] at this
    exact this
  have hMh : ∫ x, exp (α / 2 * (x : ℝ)) ∂F ≤ M :=
    integral_mono hhalf h.expMoment fun x =>
      exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) (NNReal.coe_nonneg x))
  have hMh0 : 0 ≤ ∫ x, exp (α / 2 * (x : ℝ)) ∂F := integral_nonneg fun _ => (exp_pos _).le
  -- `E Γ² ≤ (8/α²) M^n`
  have hsq : ∀ ω, Γ ω ^ 2 ≤ 8 / α ^ 2 * exp (α / 2 * Γ ω) := fun ω =>
    sq_le_exp_half hα (NNReal.coe_nonneg _)
  have hsqi : Integrable (fun ω => Γ ω ^ 2) P :=
    (hEi.const_mul (8 / α ^ 2)).mono'
      ((measurable_walkCost_real p).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsq ω)
  have hEΓ : ∫ ω, Γ ω ^ 2 ∂P ≤ 8 / α ^ 2 * M ^ n := by
    calc ∫ ω, Γ ω ^ 2 ∂P ≤ ∫ ω, 8 / α ^ 2 * exp (α / 2 * Γ ω) ∂P :=
          integral_mono hsqi (hEi.const_mul _) hsq
      _ = 8 / α ^ 2 * (∫ x, exp (α / 2 * (x : ℝ)) ∂F) ^ n := by rw [integral_const_mul, hE]
      _ ≤ 8 / α ^ 2 * M ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMh0 hMh n) (by positivity)
  -- the bad event
  have hPB : P.real B ≤ badConst c * exp (-(κ * ((n : ℝ) + 1))) :=
    ENNReal.toReal_le_of_le_ofReal (by have := h.badConst_pos; positivity)
      (h.measure_restrictedTime_ne_le u v)
  -- the pointwise bound with `ε = M^{-n}`
  set ε : ℝ := (M ^ n)⁻¹
  have hMn : 0 < M ^ n := pow_pos (by linarith) n
  have hε : 0 < ε := inv_pos.2 hMn
  have hpt : ∀ ω, Z ω - W ω ≤ ε / 2 * Γ ω ^ 2 + B.indicator (fun _ => 1 / (2 * ε)) ω := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω]
      have hZΓ : Z ω ≤ Γ ω := restrictedTime_le_walkCost ω p hp hl
      have hW0 : 0 ≤ W ω := NNReal.coe_nonneg _
      have key : Γ ω ≤ ε / 2 * Γ ω ^ 2 + 1 / (2 * ε) := by
        have h2 : ε / 2 * Γ ω ^ 2 + 1 / (2 * ε) - Γ ω = (ε * Γ ω - 1) ^ 2 / (2 * ε) := by
          field_simp; ring
        have h3 : 0 ≤ (ε * Γ ω - 1) ^ 2 / (2 * ε) := by positivity
        linarith
      linarith
    · have hZW : Z ω = W ω := by simpa [B] using hω
      rw [Set.indicator_of_notMem hω, hZW, sub_self]
      positivity
  have hint2 : Integrable (fun ω => ε / 2 * Γ ω ^ 2 + B.indicator (fun _ => 1 / (2 * ε)) ω) P :=
    (hsqi.const_mul _).add ((integrable_const _).indicator hB)
  have hexp : M ^ n * exp (-(κ * ((n : ℝ) + 1))) ≤ 1 := by
    rw [← exp_log (show 0 < M by linarith), ← exp_nat_mul, ← exp_add]
    refine exp_le_one_iff.2 ?_
    simp only [κ, decayRate]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  calc (∫ ω, Z ω ∂P) - ∫ ω, W ω ∂P = ∫ ω, (Z ω - W ω) ∂P := (integral_sub hZi hWi).symm
    _ ≤ ∫ ω, (ε / 2 * Γ ω ^ 2 + B.indicator (fun _ => 1 / (2 * ε)) ω) ∂P :=
        integral_mono (hZi.sub hWi) hint2 hpt
    _ = ε / 2 * ∫ ω, Γ ω ^ 2 ∂P + P.real B * (1 / (2 * ε)) := by
        rw [integral_add (hsqi.const_mul _) ((integrable_const _).indicator hB),
          integral_const_mul, integral_indicator_const _ hB, smul_eq_mul]
    _ ≤ ε / 2 * (8 / α ^ 2 * M ^ n) +
          badConst c * exp (-(κ * ((n : ℝ) + 1))) * (1 / (2 * ε)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hEΓ (by positivity)) ?_
        exact mul_le_mul_of_nonneg_right hPB (by positivity)
    _ = 4 / α ^ 2 + badConst c / 2 * (M ^ n * exp (-(κ * ((n : ℝ) + 1)))) := by
        simp only [ε]
        field_simp
        ring
    _ ≤ 4 / α ^ 2 + badConst c / 2 * 1 := by
        have := h.badConst_pos
        gcongr
    _ = meanGap α c := by unfold meanGap; ring

end Hyp

end CurvatureVariance.Infra.FPP
