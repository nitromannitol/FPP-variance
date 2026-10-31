/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.ConcentrationScale
public import CurvatureVariance.Infra.FPP.ConcentrationTails
public import CurvatureVariance.Infra.FPP.Hypotheses
public import CurvatureVariance.Infra.FPP.SecondMoment

/-!
# Concentration of the passage time in the form of [ADH, Theorem 3.13]

Under `ConcHyp P F α a c`, the two tails of `CurvatureVariance.Infra.FPP.ConcentrationTails`
become:

* an exponential tail of `|T − ET|` at any scale `L^{1/2}` with `1 + ‖v − u‖₁ ≤ k L`
  (`ConcHyp.measure_lt_abs_passageTime_sub_le`), hence the hypothesis
  `PassageTimeConcentration` of the time-constant and mean-rate chains
  (`ConcHyp.passageTimeConcentration`), and the variance bound `Var T(0,x) ≤ V₀ ‖x‖₁`
  (`ConcHyp.integral_sq_passageTime_sub_le`);
* the statement of [ADH, Theorem 3.13] with Gaussian bounds `e^{-C₁ t²}` without prefactor, the
  upper one for `t ≤ ‖x‖₁^{1/2}` (`ConcHyp.passageTime_concentration_adh`): a bound
  `K e^{-b t²}` from the tails absorbs its prefactor for large `t`, and for small `t` the
  variance bound gives `max(1/2, e^{-t²/(4V₀)})` (`CurvatureVariance.Infra.FPP.SecondMoment`).

The point `x = 0` is excluded: [ADH, Theorem 3.13, p. 49] leaves `x ≠ 0` implicit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### The `ℓ¹` norm of a vertex -/

theorem l1Dist_zero_eq (x : Vertex m) : l1Dist 0 x = x.1.natAbs + ∑ j, (x.2 j).natAbs := by
  simp [l1Dist, Int.natAbs_neg]

theorem one_le_l1Dist_zero {x : Vertex m} (hx : x ≠ 0) : 1 ≤ l1Dist 0 x := by
  rw [Nat.one_le_iff_ne_zero, l1Dist_zero_eq]
  intro h
  apply hx
  have h1 : x.1.natAbs = 0 := by omega
  have h2 : ∑ j, (x.2 j).natAbs = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at h2
  refine Prod.ext ?_ (funext fun j => ?_)
  · simpa using h1
  · simpa using h2 j (Finset.mem_univ j)

/-! ### A Gaussian bound without prefactor -/

/-- A bound `K e^{-b t²}` and a bound `max(1/2, e^{-a t²})` give `e^{-C t²}` with
`C = min(b/2, a, (log 2) b / (2 log (K + 1)))`: the first absorbs its prefactor when
`(b/2) t² ≥ log (K + 1)`, and below that level `C t² ≤ log 2`. -/
theorem le_exp_neg_of_le_mul_exp_of_le_max {p K b a t : ℝ} (hK : 1 ≤ K)
    (h1 : p ≤ K * exp (-(b * t ^ 2))) (h2 : p ≤ max (1 / 2) (exp (-(a * t ^ 2)))) :
    p ≤ exp (-(min (min (b / 2) a) (log 2 * b / (2 * log (K + 1))) * t ^ 2)) := by
  set C := min (min (b / 2) a) (log 2 * b / (2 * log (K + 1)))
  have hK1 : 0 < log (K + 1) := log_pos (by linarith)
  have hC1 : C ≤ b / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hC2 : C ≤ a := (min_le_left _ _).trans (min_le_right _ _)
  have hC3 : C ≤ log 2 * b / (2 * log (K + 1)) := min_le_right _ _
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  rcases le_or_gt (log (K + 1)) (b / 2 * t ^ 2) with hA | hB
  · have h3 := mul_le_mul_of_nonneg_right hC1 ht2
    calc p ≤ K * exp (-(b * t ^ 2)) := h1
      _ ≤ (K + 1) * exp (-(b * t ^ 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le
      _ = exp (log (K + 1) + -(b * t ^ 2)) := by rw [exp_add, exp_log (by linarith)]
      _ ≤ exp (-(C * t ^ 2)) := exp_le_exp.2 (by linarith)
  · refine h2.trans (max_le ?_ ?_)
    · have hlog2 : 0 < log 2 := log_pos one_lt_two
      have h4 : log 2 * b / (2 * log (K + 1)) * t ^ 2 ≤ log 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        have := mul_le_mul_of_nonneg_left (by linarith : b * t ^ 2 ≤ 2 * log (K + 1)) hlog2.le
        linarith
      have hCt : C * t ^ 2 ≤ log 2 := (mul_le_mul_of_nonneg_right hC3 ht2).trans h4
      calc (1 / 2 : ℝ) = exp (-log 2) := by rw [exp_neg, exp_log two_pos, one_div]
        _ ≤ _ := exp_le_exp.2 (by linarith)
    · exact exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right hC2 ht2])

/-! ### Constants -/

/-- The common prefactor `K = max(D + 1, C_U)` of the two tails. -/
noncomputable def tailConst (F : Measure ℝ≥0) (α a c : ℝ) : ℝ :=
  max (badConst c + 1) (upperConst F α a c)

/-- The common rate `min(c_L, c_U)` of the two tails. -/
noncomputable def tailRate (F : Measure ℝ≥0) (α a c : ℝ) : ℝ :=
  min (lowerRate F α a c) (upperRate F α a c)

/-- The variance constant `V₀`: `Var T(u, v) ≤ V₀ ‖v − u‖₁`. -/
noncomputable def varConst (F : Measure ℝ≥0) (α a c : ℝ) : ℝ :=
  1 + 12 * (2 * tailConst F α a c * exp (tailRate F α a c / 2)) * exp (tailRate F α a c / 2) /
    (tailRate F α a c / 2) ^ 3

/-- The Gaussian rate `C₁` of [ADH, Theorem 3.13]. -/
noncomputable def gaussRate (F : Measure ℝ≥0) (α a c : ℝ) : ℝ :=
  min (min (tailRate F α a c / 2 / 2) (1 / (4 * varConst F α a c)))
    (log 2 * (tailRate F α a c / 2) / (2 * log (tailConst F α a c + 1)))

section Hyp

variable {P : Measure (Config m)} {F : Measure ℝ≥0} [IsProbabilityMeasure F] {α a c : ℝ}

omit [IsProbabilityMeasure F] in
theorem ConcHyp.one_le_tailConst (h : ConcHyp P F α a c) : 1 ≤ tailConst F α a c :=
  le_max_of_le_left (by linarith [h.badConst_pos])

theorem ConcHyp.tailRate_pos (h : ConcHyp P F α a c) : 0 < tailRate F α a c :=
  lt_min h.lowerRate_pos h.upperRate_pos

theorem ConcHyp.varConst_pos (h : ConcHyp P F α a c) : 0 < varConst F α a c := by
  have := h.one_le_tailConst
  have := h.tailRate_pos
  unfold varConst
  positivity

theorem ConcHyp.gaussRate_pos (h : ConcHyp P F α a c) : 0 < gaussRate F α a c := by
  have hK := h.one_le_tailConst
  have hr := h.tailRate_pos
  have hV := h.varConst_pos
  have hK1 : 0 < log (tailConst F α a c + 1) := log_pos (by linarith)
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  unfold gaussRate
  exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)

/-- **Exponential tail at the scale `L^{1/2}`**: if `1 + ‖v − u‖₁ ≤ k L` with `k, L ≥ 1`, then
`P(|T − ET| > s L^{1/2}) ≤ 2K e^{c/k} e^{-(c/k) s}`, `c` the common rate of the tails. -/
theorem ConcHyp.measure_lt_abs_passageTime_sub_le (h : ConcHyp P F α a c) (u v : Vertex m)
    {k L : ℝ} (hk : 1 ≤ k) (hL : 1 ≤ L) (hnL : 1 + (l1Dist u v : ℝ) ≤ k * L) {s : ℝ}
    (hs : 0 ≤ s) :
    P {ω | s * √L < |(passageTime ω u v : ℝ) - ∫ ω', (passageTime ω' u v : ℝ) ∂P|} ≤
      ENNReal.ofReal (2 * tailConst F α a c * exp (tailRate F α a c / k) *
        exp (-(tailRate F α a c / k * s))) := by
  have hK := h.one_le_tailConst
  have hc := h.tailRate_pos
  have hD : badConst c + 1 ≤ tailConst F α a c := le_max_left _ _
  have hU : upperConst F α a c ≤ tailConst F α a c := le_max_right _ _
  have hcL : tailRate F α a c ≤ lowerRate F α a c := min_le_left _ _
  have hcU : tailRate F α a c ≤ upperRate F α a c := min_le_right _ _
  have hn1 : (0 : ℝ) < 1 + l1Dist u v := by positivity
  refine measure_lt_abs_sub_le_of_tails (W := fun ω => (passageTime ω u v : ℝ))
    (by linarith) hc.le (Nat.cast_nonneg _) hk hL hnL (fun z hz => ?_) (fun z hz => ?_) hs
  · refine (h.measure_passageTime_sub_le_neg_le u v hz).trans (ENNReal.ofReal_le_ofReal ?_)
    have hq : 0 ≤ z ^ 2 / (1 + l1Dist u v) := by positivity
    exact mul_le_mul hD (exp_le_exp.2 (by nlinarith)) (exp_pos _).le (by linarith)
  · refine (h.measure_le_passageTime_sub_le u v hz).trans (ENNReal.ofReal_le_ofReal ?_)
    have hq : 0 ≤ min (z ^ 2 / (1 + l1Dist u v)) z := le_min (by positivity) hz
    exact mul_le_mul hU (exp_le_exp.2 (by nlinarith)) (exp_pos _).le (by linarith)

/-- **The hypothesis `PassageTimeConcentration` of the time-constant and mean-rate chains**, with
`L = |x|` and `k = d + 1` (`1 + ‖x‖₁ ≤ (d + 1)|x|` for `|x| ≥ 2`). -/
theorem ConcHyp.passageTimeConcentration (h : ConcHyp P F α a c) :
    PassageTimeConcentration P
      (2 * tailConst F α a c * exp (tailRate F α a c / ((m : ℝ) + 2)))
      (tailRate F α a c / ((m : ℝ) + 2)) := by
  intro x hx u hu
  exact h.measure_lt_abs_passageTime_sub_le 0 x (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    (by linarith) (one_add_l1Dist_zero_le hx) hu

/-- **Variance bound**: for `u ≠ v`, `T(u,v) − E T(u,v)` is square integrable and
`E (T − ET)² ≤ V₀ ‖v − u‖₁`. -/
theorem ConcHyp.integral_sq_passageTime_sub_le (h : ConcHyp P F α a c) {u v : Vertex m}
    (huv : 1 ≤ l1Dist u v) :
    MemLp (fun ω => (passageTime ω u v : ℝ) - ∫ ω', (passageTime ω' u v : ℝ) ∂P) 2 P ∧
      ∫ ω, ((passageTime ω u v : ℝ) - ∫ ω', (passageTime ω' u v : ℝ) ∂P) ^ 2 ∂P ≤
        varConst F α a c * l1Dist u v := by
  have := IsIIDWeights.isProbabilityMeasure h.iid
  have hK := h.one_le_tailConst
  have hc := h.tailRate_pos
  have hr : (1 : ℝ) ≤ l1Dist u v := by exact_mod_cast huv
  have hm : AEMeasurable (fun ω => (passageTime ω u v : ℝ) - ∫ ω', (passageTime ω' u v : ℝ) ∂P)
      P := ((measurable_passageTime_real u v).sub measurable_const).aemeasurable
  obtain ⟨hint, hle⟩ := integral_sq_le_of_exp_tail hm (by positivity) (by positivity)
    (by linarith : (0 : ℝ) < l1Dist u v) fun s hs =>
      h.measure_lt_abs_passageTime_sub_le u v one_le_two hr (by linarith) hs
  exact ⟨(memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hint, hle⟩

/-- **[ADH, Theorem 3.13] under `ConcHyp`**: for `x ≠ 0`, `T(0,x)` is integrable,
`P(T − ET ≥ t ‖x‖₁^{1/2}) ≤ e^{-C₁ t²}` for `0 ≤ t ≤ ‖x‖₁^{1/2}`, and
`P(T − ET ≤ −t ‖x‖₁^{1/2}) ≤ e^{-C₁ t²}` for `t ≥ 0`, with `C₁ = gaussRate F α a c`. -/
theorem ConcHyp.passageTime_concentration_adh (h : ConcHyp P F α a c) {x : Vertex m}
    (hx : x ≠ 0) :
    Integrable (fun ω => (passageTime ω 0 x : ℝ)) P ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 * √(l1Dist 0 x : ℝ) →
        P {ω | t * √(l1Dist 0 x : ℝ) ≤
            (passageTime ω 0 x : ℝ) - ∫ ω', (passageTime ω' 0 x : ℝ) ∂P} ≤
          ENNReal.ofReal (exp (-(gaussRate F α a c * t ^ 2)))) ∧
      (∀ t : ℝ, 0 ≤ t →
        P {ω | (passageTime ω 0 x : ℝ) - ∫ ω', (passageTime ω' 0 x : ℝ) ∂P ≤
            -(t * √(l1Dist 0 x : ℝ))} ≤
          ENNReal.ofReal (exp (-(gaussRate F α a c * t ^ 2)))) := by
  have := IsIIDWeights.isProbabilityMeasure h.iid
  have hr : (1 : ℝ) ≤ l1Dist 0 x := by exact_mod_cast one_le_l1Dist_zero hx
  have hK := h.one_le_tailConst
  have hc := h.tailRate_pos
  have hV := h.varConst_pos
  have hT := h.integrable_passageTime 0 x
  obtain ⟨hW2, hsq⟩ := h.integral_sq_passageTime_sub_le (one_le_l1Dist_zero hx)
  have hmean : ∫ ω, ((passageTime ω 0 x : ℝ) - ∫ ω', (passageTime ω' 0 x : ℝ) ∂P) ∂P = 0 := by
    rw [integral_sub hT (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]
  have hVr : 0 < varConst F α a c * l1Dist 0 x := by positivity
  have hsr : ∀ t : ℝ, (t * √(l1Dist 0 x : ℝ)) ^ 2 / (4 * (varConst F α a c * l1Dist 0 x)) =
      1 / (4 * varConst F α a c) * t ^ 2 := by
    intro t
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    field_simp
  -- `t²/2 ≤ (t ‖x‖₁^{1/2})²/(1 + ‖x‖₁)`
  have hm1 : ∀ t : ℝ, t ^ 2 / 2 ≤ (t * √(l1Dist 0 x : ℝ)) ^ 2 / (1 + l1Dist 0 x) := by
    intro t
    rw [mul_pow, Real.sq_sqrt (by linarith), le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sq_nonneg t) (by linarith : (0 : ℝ) ≤ l1Dist 0 x - 1)]
  have finish : ∀ (S : Set (Config m)) (t : ℝ),
      P S ≤ ENNReal.ofReal (tailConst F α a c * exp (-(tailRate F α a c / 2 * t ^ 2))) →
      P.real S ≤ max (1 / 2) (exp (-(1 / (4 * varConst F α a c) * t ^ 2))) →
      P S ≤ ENNReal.ofReal (exp (-(gaussRate F α a c * t ^ 2))) := by
    intro S t h1 h2
    rw [← ofReal_measureReal (μ := P) (s := S)]
    exact ENNReal.ofReal_le_ofReal (le_exp_neg_of_le_mul_exp_of_le_max hK
      (ENNReal.toReal_le_of_le_ofReal (by positivity) h1) h2)
  refine ⟨hT, fun t ht htr => ?_, fun t ht => ?_⟩
  · apply finish _ t
    · refine (h.measure_le_passageTime_sub_le 0 x (by positivity)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hm2 : t ^ 2 / 2 ≤ t * √(l1Dist 0 x : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left htr ht]
      have hmin := le_min (hm1 t) hm2
      have hcU : tailRate F α a c ≤ upperRate F α a c := min_le_right _ _
      have hkey : tailRate F α a c / 2 * t ^ 2 ≤ upperRate F α a c *
          min ((t * √(l1Dist 0 x : ℝ)) ^ 2 / (1 + l1Dist 0 x)) (t * √(l1Dist 0 x : ℝ)) :=
        calc tailRate F α a c / 2 * t ^ 2 = tailRate F α a c * (t ^ 2 / 2) := by ring
          _ ≤ tailRate F α a c * _ := mul_le_mul_of_nonneg_left hmin hc.le
          _ ≤ _ := mul_le_mul_of_nonneg_right hcU ((by positivity : (0 : ℝ) ≤ t ^ 2 / 2).trans hmin)
      exact mul_le_mul (le_max_right _ _) (exp_le_exp.2 (by linarith)) (exp_pos _).le
        (by linarith)
    · have := measure_le_ge_le_of_integral_sq_le hW2 hmean hVr hsq
        (s := t * √(l1Dist 0 x : ℝ)) (by positivity)
      rwa [hsr t] at this
  · apply finish _ t
    · refine (h.measure_passageTime_sub_le_neg_le 0 x (by positivity)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hcL : tailRate F α a c ≤ lowerRate F α a c := min_le_left _ _
      have hkey : tailRate F α a c / 2 * t ^ 2 ≤
          lowerRate F α a c * ((t * √(l1Dist 0 x : ℝ)) ^ 2 / (1 + l1Dist 0 x)) :=
        calc tailRate F α a c / 2 * t ^ 2 = tailRate F α a c * (t ^ 2 / 2) := by ring
          _ ≤ tailRate F α a c * _ := mul_le_mul_of_nonneg_left (hm1 t) hc.le
          _ ≤ _ := mul_le_mul_of_nonneg_right hcL ((by positivity : (0 : ℝ) ≤ t ^ 2 / 2).trans
              (hm1 t))
      exact mul_le_mul (le_max_left _ _) (exp_le_exp.2 (by linarith)) (exp_pos _).le
        (by linarith)
    · have := measure_le_neg_le_of_integral_sq_le hW2 hmean hVr hsq
        (s := t * √(l1Dist 0 x : ℝ)) (by positivity)
      rwa [hsr t] at this

end Hyp

end CurvatureVariance.Infra.FPP
