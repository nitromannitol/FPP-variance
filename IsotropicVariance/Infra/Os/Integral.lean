/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.Sum
public import IsotropicVariance.Infra.Os.Moments
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Measured families in AKM Lemma A.4

Jensen's inequality and Fubini give the sum rule for a jointly measurable
nonnegative family indexed by an arbitrary measured space with integrable scale.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace IsotropicVariance.Infra.Os

open Cited

/-- The integral Jensen step for a convex majorant of the exponential power.
The index measure is a probability measure, and each variable has unit scale. -/
theorem isOs_integral_of_convex {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (μ : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    {s B r : ℝ} (hs : 0 < s) (hB : 0 ≤ B) (hr : 1 ≤ r)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ (Ici 0) g) (hgc : Continuous g)
    (hLower : ∀ x : ℝ, 0 ≤ x → Real.exp (x ^ s) ≤ g x)
    (hUpper : ∀ x : ℝ, 0 ≤ x → g x ≤ B * Real.exp (x ^ s))
    (hBr : ENNReal.ofReal B * 2 ≤ (2 : ℝ≥0∞) ^ r)
    (X : E → Ω → ℝ) (hXm : Measurable (Function.uncurry X))
    (hX0 : ∀ x ω, 0 ≤ X x ω) (hX : ∀ x, IsOs P s 1 (X x)) :
    IsOs P s (r ^ (1 / s)) (fun ω => ∫ x, X x ω ∂μ) := by
  change Measurable (fun p : E × Ω => X p.1 p.2) at hXm
  let G : E × Ω → ℝ := fun p => g (X p.1 p.2)
  have hGm : Measurable G := hgc.measurable.comp hXm
  have hG0 (p : E × Ω) : 0 ≤ G p := (Real.exp_pos _).le.trans (hLower _ (hX0 p.1 p.2))
  have hGb : (∫⁻ p, ENNReal.ofReal (G p) ∂μ.prod P) ≤ ENNReal.ofReal B * 2 := by
    rw [lintegral_prod _ hGm.ennreal_ofReal.aemeasurable]
    apply (lintegral_mono fun x => ?_).trans_eq
      (by rw [lintegral_const, measure_univ, mul_one])
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal B * ENNReal.ofReal (Real.exp ((max (X x ω) 0 / 1) ^ s)) ∂P := by
        apply lintegral_mono
        intro ω
        dsimp only
        rw [← ENNReal.ofReal_mul hB]
        apply ENNReal.ofReal_le_ofReal
        simpa only [max_eq_left (hX0 x ω), div_one] using hUpper (X x ω) (hX0 x ω)
      _ = ENNReal.ofReal B * ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X x ω) 0 / 1) ^ s)) ∂P :=
        lintegral_const_mul'' _ (aemeasurable_exp_pos_rpow (hX x).1 s 1)
      _ ≤ _ := mul_le_mul le_rfl (hX x).2 zero_le zero_le
  have hGi : Integrable G (μ.prod P) := ⟨hGm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0)).mpr
      (hGb.trans_lt (by finiteness))⟩
  have hXi : Integrable (Function.uncurry X) (μ.prod P) := by
    refine ⟨hXm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun p : E × Ω => hX0 p.1 p.2)).mpr ?_⟩
    change (∫⁻ p : E × Ω, ENNReal.ofReal (X p.1 p.2) ∂μ.prod P) < ∞
    rw [lintegral_prod _ hXm.ennreal_ofReal.aemeasurable]
    have hM (x : E) := (hX x).lintegral_pos_rpow_le hs zero_lt_one (show (0 : ℝ) ≤ 1 by norm_num)
    have hb : (∫⁻ x, ∫⁻ ω, ENNReal.ofReal (X x ω) ∂P ∂μ) ≤
        ENNReal.ofReal (2 * (1 + ((Nat.ceil (1 / s)).factorial : ℝ))) := by
      apply (lintegral_mono fun x => ?_).trans_eq
        (by rw [lintegral_const, measure_univ, mul_one])
      simpa only [Real.one_rpow, mul_one, Real.rpow_one, max_eq_left (hX0 x _)] using hM x
    exact hb.trans_lt ENNReal.ofReal_lt_top
  have hYm : AEMeasurable (fun ω => ∫ x, X x ω ∂μ) P :=
    hXi.integral_prod_right.aemeasurable
  have hh : (∫⁻ ω, ENNReal.ofReal (Real.exp ((max (∫ x, X x ω ∂μ) 0 / 1) ^ s)) ∂P) ≤
      ENNReal.ofReal B * 2 := by
    apply le_trans _ hGb
    rw [lintegral_prod_symm _ hGm.ennreal_ofReal.aemeasurable]
    apply lintegral_mono_ae
    filter_upwards [hXi.prod_left_ae, hGi.prod_left_ae] with ω hxi hgi
    rw [div_one, max_eq_left (integral_nonneg (fun x => hX0 x ω))]
    have hj := hg.map_integral_le hgc.continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun x => hX0 x ω) hxi hgi
    apply (ENNReal.ofReal_le_ofReal ((hLower _ (integral_nonneg (fun x => hX0 x ω))).trans hj)).trans_eq
    exact ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun x => hG0 (x, ω))
  have hRes := isOs_of_exp_moment_le hs zero_lt_one hr hYm (hh.trans hBr)
  simpa only [mul_one] using hRes

/-- AKM A.4 for a probability-indexed, jointly measurable nonnegative family
whose members all have unit scale. -/
theorem isOs_integral_prob {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (μ : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (X : E → Ω → ℝ)
    (hXm : Measurable (Function.uncurry X)) (hX0 : ∀ x ω, 0 ≤ X x ω)
    (hX : ∀ x, IsOs P s 1 (X x)) :
    IsOs P s (sumConstant s) (fun ω => ∫ x, X x ω ∂μ) := by
  classical
  by_cases hs1 : 1 ≤ s
  · have hConv : ConvexOn ℝ (Ici 0) (fun x : ℝ => Real.exp (x ^ s)) := by
      refine ⟨convex_Ici 0, ?_⟩
      intro x hx y hy a b ha hb hab
      exact (Real.exp_le_exp.mpr ((convexOn_rpow hs1).2 hx hy ha hb hab)).trans
        (convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hab)
    have hh := isOs_integral_of_convex P μ hs (show (0 : ℝ) ≤ 1 by norm_num)
      (r := 1) le_rfl _ hConv
      (Real.continuous_exp.comp (Real.continuous_rpow_const hs.le))
      (fun _ _ => le_rfl) (fun x _ => by rw [one_mul]) (by norm_num) X hXm hX0 hX
    simpa only [sumConstant, ite_eq_left hs1, Real.one_rpow] using hh
  have hslt : s < 1 := lt_of_not_ge hs1
  let a := ((1 - s) / s) ^ (1 / s)
  have hapos : 0 < a := Real.rpow_pos_of_pos (div_pos (sub_pos.mpr hslt) hs) _
  have ha : a ^ s = (1 - s) / s := by
    dsimp only [a]
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hs.ne', Real.rpow_one]
  let r := 1 + a ^ s / Real.log 2
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hr : 1 ≤ r := le_add_of_nonneg_right (div_nonneg (Real.rpow_nonneg hapos.le _) hlog.le)
  have hConv := convexOn_exp_rpow_shift hs hapos (by rw [ha, mul_div_cancel₀ _ hs.ne'])
  have hLower (x : ℝ) (hx : 0 ≤ x) : Real.exp (x ^ s) ≤ Real.exp ((x + a) ^ s) :=
    Real.exp_le_exp.mpr (Real.rpow_le_rpow hx (le_add_of_nonneg_right hapos.le) hs.le)
  have hUpper (x : ℝ) (hx : 0 ≤ x) : Real.exp ((x + a) ^ s) ≤ Real.exp (a ^ s) * Real.exp (x ^ s) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr ((Real.rpow_add_le_add_rpow hx hapos.le hs.le hslt.le).trans_eq (add_comm _ _))
  have hBr : ENNReal.ofReal (Real.exp (a ^ s)) * 2 ≤ (2 : ℝ≥0∞) ^ r := by
    apply le_of_eq
    rw [← ENNReal.ofReal_ofNat, ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [show Real.log 2 * r = a ^ s + Real.log 2 by dsimp only [r]; field_simp; ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

  have hh := isOs_integral_of_convex P μ hs (Real.exp_pos _).le hr _ hConv
    (Real.continuous_exp.comp ((Real.continuous_rpow_const hs.le).comp (continuous_id.add_const a)))
    hLower hUpper hBr X hXm hX0 hX
  simpa only [sumConstant, ite_eq_right hs1, r, ha] using hh

/-- AKM A.4 in its measured-family generality: integrable positive scales and a
jointly measurable nonnegative family. No independence or finiteness assumption
on the index measure is required. -/
theorem isOs_integral {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (μ : Measure E) [IsProbabilityMeasure P]
    {s : ℝ} (hs : 0 < s) (θ : E → ℝ) (hθ : ∀ x, 0 < θ x)
    (hθm : Measurable θ) (hθi : Integrable θ μ)
    (X : E → Ω → ℝ) (hXm : Measurable (Function.uncurry X))
    (hX0 : ∀ x ω, 0 ≤ X x ω) (hX : ∀ x, IsOs P s (θ x) (X x)) :
    IsOs P s (sumConstant s * ∫ x, θ x ∂μ) (fun ω => ∫ x, X x ω ∂μ) := by
  classical
  by_cases hμ : μ = 0
  · subst μ
    simpa only [integral_zero_measure, mul_zero] using isOs_zero (P := P) hs 0
  let Θ := ∫ x, θ x ∂μ
  have hΘ : 0 < Θ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (hθ x).le) hθi).mpr
    have heq : Function.support θ = univ := by ext x; simp only [Function.mem_support, mem_univ, iff_true]; exact (hθ x).ne'
    rw [heq]
    exact pos_iff_ne_zero.mpr (fun h => hμ (Measure.measure_univ_eq_zero.mp h))
  let f := fun x => ENNReal.ofReal (θ x / Θ)
  let ν := μ.withDensity f
  have hfm : Measurable f := (hθm.div_const Θ).ennreal_ofReal
  have hν : IsProbabilityMeasure ν := by
    constructor
    change μ.withDensity f univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hθi.div_const Θ)
        (Filter.Eventually.of_forall fun x => div_nonneg (hθ x).le hΘ.le),
      integral_div, div_self hΘ.ne', ENNReal.ofReal_one]
  have : IsProbabilityMeasure ν := hν
  let Y := fun x ω => X x ω / θ x
  have hYm : Measurable (Function.uncurry Y) := hXm.div (hθm.comp measurable_fst)
  have hY0 : ∀ x ω, 0 ≤ Y x ω := fun x ω => div_nonneg (hX0 x ω) (hθ x).le
  have hY : ∀ x, IsOs P s 1 (Y x) := fun x => (isOs_div_iff (hθ x)).mpr (hX x)
  have hh := isOs_integral_prob P ν hs Y hYm hY0 hY
  have hEq (ω : Ω) : Θ * (∫ x, Y x ω ∂ν) = ∫ x, X x ω ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul hfm
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    have heq : (fun x => (f x).toReal • Y x ω) = fun x => Θ⁻¹ * X x ω := by
      funext x
      rw [smul_eq_mul, ENNReal.toReal_ofReal (div_nonneg (hθ x).le hΘ.le)]
      dsimp only [Y, f]
      field_simp [(hθ x).ne', hΘ.ne']
    rw [heq, integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hΘ.ne', one_mul]
  have hScaled := (isOs_mul_iff (P := P) (a := Θ) hΘ).mpr hh
  rw [mul_comm Θ (sumConstant s)] at hScaled
  exact hScaled.congr (Filter.Eventually.of_forall hEq)

end IsotropicVariance.Infra.Os
