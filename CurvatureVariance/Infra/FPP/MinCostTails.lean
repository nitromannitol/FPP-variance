/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.MinCost
public import CurvatureVariance.Infra.FPP.Hypotheses
import Mathlib.Probability.Independence.InfinitePi

/-!
# Tails of a minimum of edge-set costs, for weights with an exponential moment

Let the edge weights be independent with law `F` on `ℝ≥0`, with a finite exponential moment
`E e^{α τ} < ∞`, `α > 0`, and let `𝓕` be a finite nonempty family of edge sets with at most `K`
edges each. Put `B = E[τ² e^{α τ/2}]`. Then `Z = minCost 𝓕` satisfies, with `A = (B + 1)(K + 1)`:

* `Ent e^{θZ} ≤ θ² B K E e^{θZ}` for `θ ≤ α/2` (`eentropy_exp_minCost_le`), by the symmetrized
  entropy bound with at most `K` pivotal edges;
* `E e^{θ(Z - EZ)} ≤ e^{A θ²}` for `θ ≤ 0` and for `0 ≤ θ ≤ α/2`, by Herbst's argument;
* hence the Gaussian lower tail `P(Z ≤ EZ - t) ≤ e^{-t²/(4A)}` at every level
  (`measure_minCost_le_integral_sub`, and `minCostLowerTail` in the form `MinCostLowerTail`), and
  the upper tail `P(Z ≥ EZ + t) ≤ e^{-min(t²/(4A), α t/4)}` (`measure_integral_add_le_minCost`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

open Infra.Entropy

variable {m : ℕ} {F : Measure ℝ≥0} [IsProbabilityMeasure F] {α : ℝ}

/-! ### The constant of the symmetrized bound -/

/-- `B = E[τ² e^{α τ/2}]`, the constant of the symmetrized entropy bound below rate `α/2`. -/
noncomputable def sqExpConst (F : Measure ℝ≥0) (α : ℝ) : ℝ :=
  ∫ y, (y : ℝ) ^ 2 * exp (α / 2 * y) ∂F

theorem sqExpConst_nonneg (F : Measure ℝ≥0) (α : ℝ) : 0 ≤ sqExpConst F α :=
  integral_nonneg fun y => by positivity

omit [IsProbabilityMeasure F] in
/-- `τ² e^{α τ/2} ≤ (8/α²) e^{α τ}`. -/
theorem integrable_sq_mul_exp_half (hα0 : 0 < α)
    (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F) :
    Integrable (fun y : ℝ≥0 => (y : ℝ) ^ 2 * exp (α / 2 * y)) F := by
  refine (hα.const_mul (8 / α ^ 2)).mono' (by fun_prop) (ae_of_all _ fun y => ?_)
  have hy : (0 : ℝ) ≤ y := NNReal.coe_nonneg y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- `e^{x} ≥ x²/2` at `x = α y/2` gives `y² ≤ (8/α²) e^{α y/2}`
  have hx : (α / 2 * y) ^ 2 / 2 ≤ exp (α / 2 * y) := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ α / 2 * y by positivity)
    nlinarith [Real.add_one_le_exp (α / 2 * y)]
  have hsq : (y : ℝ) ^ 2 ≤ 8 / α ^ 2 * exp (α / 2 * y) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  calc (y : ℝ) ^ 2 * exp (α / 2 * y) ≤ 8 / α ^ 2 * exp (α / 2 * y) * exp (α / 2 * y) :=
        mul_le_mul_of_nonneg_right hsq (exp_pos _).le
    _ = 8 / α ^ 2 * exp (α * y) := by rw [mul_assoc, ← exp_add]; ring_nf

omit [IsProbabilityMeasure F] in
/-- For `θ ≤ α/2`, `∫ θ² y² e^{θ₊ y} dF ≤ θ² B`. -/
theorem lintegral_sq_mul_exp_le (hα0 : 0 < α) (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F)
    {θ : ℝ} (hθ : θ ≤ α / 2) :
    ∫⁻ y, ENNReal.ofReal (θ ^ 2 * (y : ℝ) ^ 2 * exp (max θ 0 * y)) ∂F ≤
      ENNReal.ofReal (θ ^ 2 * sqExpConst F α) := by
  have hI := integrable_sq_mul_exp_half hα0 hα
  rw [sqExpConst, ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hI.const_mul _)
    (ae_of_all _ fun y => by positivity)]
  refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
  have hy : (0 : ℝ) ≤ y := NNReal.coe_nonneg y
  have h1 : max θ 0 * y ≤ α / 2 * y :=
    mul_le_mul_of_nonneg_right (max_le hθ (by linarith)) hy
  have h2 := exp_le_exp.2 h1
  have h3 : 0 ≤ θ ^ 2 * (y : ℝ) ^ 2 := by positivity
  calc θ ^ 2 * (y : ℝ) ^ 2 * exp (max θ 0 * y) ≤ θ ^ 2 * (y : ℝ) ^ 2 * exp (α / 2 * y) :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = θ ^ 2 * ((y : ℝ) ^ 2 * exp (α / 2 * y)) := by ring

/-! ### Exponential integrability -/

/-- The weights of a finite set of edges have exponential moments up to rate `α`. -/
theorem integrable_exp_mul_sum_infinitePi (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F)
    {θ : ℝ} (hθ : θ ≤ α) (S : Finset (Edge m)) :
    Integrable (fun ω : Config m => exp (θ * ∑ e ∈ S, (ω e : ℝ)))
      (Measure.infinitePi fun _ : Edge m => F) := by
  have hP := isIIDWeights_infinitePi (m := m) F
  have hθF : Integrable (fun x : ℝ≥0 => exp (θ * x)) F := integrable_exp_mul_of_le hθ hα
  have h := (IsIIDWeights.iIndepFun_real hP).integrable_exp_mul_sum
    (fun e => (measurable_pi_apply e).coe_nnreal_real) (s := S) (t := θ) (fun e _ =>
      ((IsIIDWeights.identDistrib hP e).comp (measurable_id.const_mul θ).exp).integrable_iff.2 hθF)
  simpa [Finset.sum_apply] using h

variable {𝓕 : Finset (Finset (Edge m))} {h𝓕 : 𝓕.Nonempty}

/-- `e^{θ Z}` is integrable for `θ ≤ α`. -/
theorem integrable_exp_mul_minCost (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F) {θ : ℝ}
    (hθ : θ ≤ α) :
    Integrable (fun ω => exp (θ * minCost 𝓕 h𝓕 ω)) (Measure.infinitePi fun _ : Edge m => F) := by
  have hm : AEStronglyMeasurable (fun ω => exp (θ * minCost 𝓕 h𝓕 ω))
      (Measure.infinitePi fun _ : Edge m => F) :=
    (measurable_minCost.const_mul θ).exp.aestronglyMeasurable
  rcases le_or_gt θ 0 with h0 | h0
  · refine (integrable_const (1 : ℝ)).mono' hm (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg h0 (minCost_nonneg ω))
  · obtain ⟨S, hS⟩ := h𝓕
    refine (integrable_exp_mul_sum_infinitePi hα hθ S).mono' hm (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.2 (mul_le_mul_of_nonneg_left (minCost_le hS) h0.le)

/-- Every `θ < α` is an interior point of the exponential integrability set of `Z`. -/
theorem Iio_subset_interior_integrableExpSet (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F) :
    Set.Iio α ⊆ interior (integrableExpSet (minCost 𝓕 h𝓕)
      (Measure.infinitePi fun _ : Edge m => F)) :=
  interior_maximal (fun _ hθ => integrable_exp_mul_minCost hα (le_of_lt hθ)) isOpen_Iio

/-! ### The entropy bound and Herbst's argument -/

/-- **The entropy bound** for `θ ≤ α/2`: `Ent e^{θZ} ≤ θ² B K E e^{θZ}`. -/
theorem eentropy_exp_minCost_le (hα0 : 0 < α) (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F)
    {K : ℕ} (hK : ∀ S ∈ 𝓕, S.card ≤ K) {θ : ℝ} (hθ : θ ≤ α / 2) :
    eentropy (Measure.infinitePi fun _ : Edge m => F) (fun ω => exp (θ * minCost 𝓕 h𝓕 ω)) ≤
      ENNReal.ofReal (θ ^ 2 * sqExpConst F α * K *
        mgf (minCost 𝓕 h𝓕) (Measure.infinitePi fun _ : Edge m => F) θ) := by
  set P := Measure.infinitePi fun _ : Edge m => F
  have hint := integrable_exp_mul_minCost (𝓕 := 𝓕) (h𝓕 := h𝓕) hα (by linarith : θ ≤ α)
  have h := eentropy_exp_le (ν := F) measurable_minCost (measurableSet_minCostPiv)
    hasPivots_minCost (tsum_indicator_minCostPiv_le hK) θ hint
  have hc : 0 ≤ θ ^ 2 * sqExpConst F α := mul_nonneg (sq_nonneg θ) (sqExpConst_nonneg F α)
  have hI : ∫⁻ ω, ENNReal.ofReal (exp (θ * minCost 𝓕 h𝓕 ω)) ∂P =
      ENNReal.ofReal (mgf (minCost 𝓕 h𝓕) P θ) := by
    rw [mgf, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (exp_pos _).le)]
  refine h.trans ?_
  calc _ = (∫⁻ y, ENNReal.ofReal (θ ^ 2 * (y : ℝ) ^ 2 * exp (max θ 0 * y)) ∂F) *
        ENNReal.ofReal K * ENNReal.ofReal (mgf (minCost 𝓕 h𝓕) P θ) := by
        rw [← hI, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (θ ^ 2 * sqExpConst F α) * ENNReal.ofReal K *
        ENNReal.ofReal (mgf (minCost 𝓕 h𝓕) P θ) := by
        gcongr
        exact lintegral_sq_mul_exp_le hα0 hα hθ
    _ = _ := by
        rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (mul_nonneg hc (Nat.cast_nonneg K))]

/-- The entropy bound in the form of Herbst's argument, with `A = (B + 1)(K + 1)`. -/
theorem eentropy_exp_minCost_le' (hα0 : 0 < α) (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F)
    {K : ℕ} (hK : ∀ S ∈ 𝓕, S.card ≤ K) {θ : ℝ} (hθ : θ ≤ α / 2) :
    eentropy (Measure.infinitePi fun _ : Edge m => F) (fun ω => exp (θ * minCost 𝓕 h𝓕 ω)) ≤
      ENNReal.ofReal ((sqExpConst F α + 1) * (K + 1) * θ ^ 2 *
        mgf (minCost 𝓕 h𝓕) (Measure.infinitePi fun _ : Edge m => F) θ) := by
  refine (eentropy_exp_minCost_le hα0 hα hK hθ).trans (ENNReal.ofReal_le_ofReal ?_)
  have hB := sqExpConst_nonneg F α
  have hM : 0 ≤ θ ^ 2 * mgf (minCost 𝓕 h𝓕) (Measure.infinitePi fun _ : Edge m => F) θ :=
    mul_nonneg (sq_nonneg θ) mgf_nonneg
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hBK : sqExpConst F α * K ≤ (sqExpConst F α + 1) * (K + 1) := by nlinarith
  calc θ ^ 2 * sqExpConst F α * K * mgf (minCost 𝓕 h𝓕) (Measure.infinitePi fun _ : Edge m => F) θ
      = sqExpConst F α * K *
          (θ ^ 2 * mgf (minCost 𝓕 h𝓕) (Measure.infinitePi fun _ : Edge m => F) θ) := by ring
    _ ≤ (sqExpConst F α + 1) * (K + 1) *
          (θ ^ 2 * mgf (minCost 𝓕 h𝓕) (Measure.infinitePi fun _ : Edge m => F) θ) :=
        mul_le_mul_of_nonneg_right hBK hM
    _ = _ := by ring

/-- **Herbst, lower side**: `E e^{θ(Z - EZ)} ≤ e^{A θ²}` for every `θ ≤ 0`. -/
theorem mgf_sub_integral_minCost_le_of_nonpos (hα0 : 0 < α)
    (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F) {K : ℕ} (hK : ∀ S ∈ 𝓕, S.card ≤ K) {θ : ℝ}
    (hθ : θ ≤ 0) :
    mgf (fun ω => minCost 𝓕 h𝓕 ω - ∫ ω', minCost 𝓕 h𝓕 ω' ∂Measure.infinitePi fun _ : Edge m => F)
        (Measure.infinitePi fun _ : Edge m => F) θ ≤
      exp ((sqExpConst F α + 1) * (K + 1) * θ ^ 2) := by
  have hB := sqExpConst_nonneg F α
  refine mgf_sub_integral_le_of_eentropy_le_neg (θ₀ := -θ) (by positivity) measurable_minCost
    (fun x hx => Iio_subset_interior_integrableExpSet hα (by linarith [hx.2] : x < α))
    (fun θ' hθ' => eentropy_exp_minCost_le' hα0 hα hK (by linarith [hθ'.2])) θ ⟨by linarith, hθ⟩

/-- **Herbst, upper side**: `E e^{θ(Z - EZ)} ≤ e^{A θ²}` for `0 ≤ θ ≤ α/2`. -/
theorem mgf_sub_integral_minCost_le (hα0 : 0 < α)
    (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F) {K : ℕ} (hK : ∀ S ∈ 𝓕, S.card ≤ K) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ α / 2) :
    mgf (fun ω => minCost 𝓕 h𝓕 ω - ∫ ω', minCost 𝓕 h𝓕 ω' ∂Measure.infinitePi fun _ : Edge m => F)
        (Measure.infinitePi fun _ : Edge m => F) θ ≤
      exp ((sqExpConst F α + 1) * (K + 1) * θ ^ 2) := by
  have hB := sqExpConst_nonneg F α
  refine mgf_sub_integral_le_of_eentropy_le (θ₀ := α / 2) (by positivity) measurable_minCost
    (fun x hx => Iio_subset_interior_integrableExpSet hα (by linarith [hx.2] : x < α))
    (fun θ' hθ' => eentropy_exp_minCost_le' hα0 hα hK hθ'.2) θ ⟨hθ0, hθ⟩

/-! ### The tails -/

/-- **Gaussian lower tail** of a minimum of edge-set costs: if every set has at most `K` edges,
`P(Z ≤ EZ - t) ≤ e^{-t²/(4A)}` for every `t ≥ 0`, `A = (B + 1)(K + 1)`. -/
theorem measure_minCost_le_integral_sub (hα0 : 0 < α)
    (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F) {P : Measure (Config m)}
    (hP : IsIIDWeights P F) (𝓕 : Finset (Finset (Edge m))) (h𝓕 : 𝓕.Nonempty) {K : ℕ}
    (hK : ∀ S ∈ 𝓕, S.card ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | minCost 𝓕 h𝓕 ω ≤ (∫ ω', minCost 𝓕 h𝓕 ω' ∂P) - t} ≤
      ENNReal.ofReal (exp (-(t ^ 2 / (4 * ((sqExpConst F α + 1) * (K + 1)))))) := by
  rw [IsIIDWeights.eq_infinitePi hP]
  have hB := sqExpConst_nonneg F α
  exact measure_le_integral_sub_of_mgf_le (A := (sqExpConst F α + 1) * (K + 1)) (by positivity)
    (fun θ hθ => integrable_exp_mul_minCost (𝓕 := 𝓕) (h𝓕 := h𝓕) hα (by linarith))
    (fun θ hθ => mgf_sub_integral_minCost_le_of_nonpos hα0 hα hK hθ) ht

/-- **Upper tail** of a minimum of edge-set costs: if every set has at most `K` edges,
`P(Z ≥ EZ + t) ≤ e^{-min(t²/(4A), α t/4)}` for every `t ≥ 0`, `A = (B + 1)(K + 1)`. -/
theorem measure_integral_add_le_minCost (hα0 : 0 < α)
    (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F) {P : Measure (Config m)}
    (hP : IsIIDWeights P F) (𝓕 : Finset (Finset (Edge m))) (h𝓕 : 𝓕.Nonempty) {K : ℕ}
    (hK : ∀ S ∈ 𝓕, S.card ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | (∫ ω', minCost 𝓕 h𝓕 ω' ∂P) + t ≤ minCost 𝓕 h𝓕 ω} ≤
      ENNReal.ofReal
        (exp (-min (t ^ 2 / (4 * ((sqExpConst F α + 1) * (K + 1)))) (α / 2 * t / 2))) := by
  rw [IsIIDWeights.eq_infinitePi hP]
  have hB := sqExpConst_nonneg F α
  exact measure_integral_add_le_of_mgf_le (A := (sqExpConst F α + 1) * (K + 1)) (θ₀ := α / 2)
    (by positivity) (by positivity)
    (fun θ hθ => integrable_exp_mul_minCost (𝓕 := 𝓕) (h𝓕 := h𝓕) hα (by linarith [hθ.2]))
    (fun θ hθ => mgf_sub_integral_minCost_le hα0 hα hK hθ.1 hθ.2) ht

/-- The Gaussian lower tail in the form `MinCostLowerTail`, with `C = 1`, `c = 1/(4(B + 1))`. -/
theorem minCostLowerTail (hα0 : 0 < α) (hα : Integrable (fun x : ℝ≥0 => exp (α * x)) F)
    {P : Measure (Config m)} (hP : IsIIDWeights P F) :
    MinCostLowerTail P 1 (1 / (4 * (sqExpConst F α + 1))) := by
  intro 𝓕 h𝓕 K hK t ht
  refine (measure_minCost_le_integral_sub hα0 hα hP 𝓕 h𝓕 hK ht).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  have hB := sqExpConst_nonneg F α
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [one_mul]
  congr 1
  field_simp

end CurvatureVariance.Infra.FPP
