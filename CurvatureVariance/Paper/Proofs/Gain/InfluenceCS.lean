/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.AVLabels
public import CurvatureVariance.Paper.Proofs.Responses.Exchange
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.MeanInequalities

/-!
# Cauchy–Schwarz for the `L¹` influences of an average

The proof of Lemma `lem:fewtranslates` (that of [AB26, Lemma 6.4]): "Jensen's inequality, and the
Cauchy–Schwarz inequality for the joint law of `m` and `ω`". For an average `F̄ = V⁻¹ ∑_{v<V} F_v`
of measurable functions and a set `G` of edges:

`(E|F̄ − F̄^G|)² ≤ (V⁻¹ ∑_v E(F_v − F_v^G)²) · (V⁻¹ ∑_v P⊗P(F_v ≠ F_v^G))`
(`l1Term_average_sq_le`). Here `E|X − X^G|` is `Gain.l1Term` and `E(X − X^G)²` is `esTerm`, both
integrals over the old and new weights.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper

variable {m : ℕ}

/-- `|V⁻¹ ∑ a − V⁻¹ ∑ b| ≤ V⁻¹ ∑ |a − b|`, in `[0, ∞]`. -/
theorem ofReal_abs_sub_average_le {V : ℕ} (hV : 0 < V) (a b : ℕ → ℝ) :
    ENNReal.ofReal |(V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, a v -
        (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, b v| ≤
      (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, ENNReal.ofReal |a v - b v| := by
  have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
  have hreal : |(V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, a v - (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, b v| ≤
      (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, |a v - b v| := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.2 hV0)]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.2 hV0).le
  refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hV0, ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun v _ => abs_nonneg _)]

/-- **The triangle inequality over an average**: the `L¹` term of `V⁻¹ ∑_{v<V} F_v` is at most the
average of those of the `F_v`. -/
theorem l1Term_average_le (P : Measure (Config m)) [SFinite P] (F : ℕ → Config m → ℝ)
    (hF : ∀ v, Measurable (F v)) {V : ℕ} (hV : 0 < V) (G : Set (Sym2 (Vertex m))) :
    Gain.l1Term P (fun ω => (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, F v ω) G ≤
      (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, Gain.l1Term P (F v) G := by
  have hjoint : ∀ v, Measurable fun p : Config m × Config m =>
      ENNReal.ofReal |F v p.1 - F v (resample G p.1 p.2)| := fun v =>
    (continuous_abs.measurable.comp (((hF v).comp measurable_fst).sub
      ((hF v).comp (Responses.measurable_resample G)))).ennreal_ofReal
  have hinner : ∀ v ω, Measurable fun ω' =>
      ENNReal.ofReal |F v ω - F v (resample G ω ω')| := fun v ω =>
    (hjoint v).comp (measurable_const.prodMk measurable_id)
  have hout : ∀ v, Measurable fun ω => ∫⁻ ω',
      ENNReal.ofReal |F v ω - F v (resample G ω ω')| ∂P := fun v =>
    (hjoint v).lintegral_prod_right'
  have hpt : ∀ ω ω', ENNReal.ofReal |(V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, F v ω -
      (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, F v (resample G ω ω')| ≤
      (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, ENNReal.ofReal |F v ω - F v (resample G ω ω')| :=
    fun ω ω' => ofReal_abs_sub_average_le hV (fun v => F v ω) (fun v => F v (resample G ω ω'))
  unfold Gain.l1Term
  refine (lintegral_mono fun ω => lintegral_mono fun ω' => hpt ω ω').trans (le_of_eq ?_)
  have h1 : ∀ ω, ∫⁻ ω', (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V,
      ENNReal.ofReal |F v ω - F v (resample G ω ω')| ∂P =
      (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, ∫⁻ ω',
        ENNReal.ofReal |F v ω - F v (resample G ω ω')| ∂P := fun ω => by
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun v _ => hinner v ω),
      lintegral_finsetSum _ fun v _ => hinner v ω]
  simp_rw [h1]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun v _ => hout v),
    lintegral_finsetSum _ fun v _ => hout v]

/-- **Cauchy–Schwarz on the old and new weights**: `E|X − X^G| ≤ (E(X − X^G)²)^{1/2}
P⊗P(X ≠ X^G)^{1/2}`. -/
theorem l1Term_le_esTerm_rpow_mul {P : Measure (Config m)} [IsProbabilityMeasure P]
    {X : Config m → ℝ} (hX : Measurable X) (G : Set (Sym2 (Vertex m))) :
    Gain.l1Term P X G ≤ esTerm P X G ^ (1 / 2 : ℝ) *
      (P.prod P) {p | X p.1 ≠ X (resample G p.1 p.2)} ^ (1 / 2 : ℝ) := by
  have h1 : Measurable fun p : Config m × Config m => X p.1 := hX.comp measurable_fst
  have h2 : Measurable fun p : Config m × Config m => X (resample G p.1 p.2) :=
    hX.comp (Responses.measurable_resample G)
  set E : Set (Config m × Config m) := {p | X p.1 ≠ X (resample G p.1 p.2)} with hEdef
  have hE : MeasurableSet E := (measurableSet_eq_fun h1 h2).compl
  set f : Config m × Config m → ℝ≥0∞ := fun p => ENNReal.ofReal |X p.1 - X (resample G p.1 p.2)|
    with hfdef
  have hf : Measurable f := (continuous_abs.measurable.comp (h1.sub h2)).ennreal_ofReal
  have hl1 : Gain.l1Term P X G = ∫⁻ p, f p ∂(P.prod P) :=
    (lintegral_prod f hf.aemeasurable).symm
  have hes : esTerm P X G = ∫⁻ p, f p ^ (2 : ℝ) ∂(P.prod P) := by
    have hsq : Measurable fun p : Config m × Config m =>
        ENNReal.ofReal ((X p.1 - X (resample G p.1 p.2)) ^ 2) :=
      ((h1.sub h2).pow_const 2).ennreal_ofReal
    rw [esTerm, ← lintegral_prod _ hsq.aemeasurable]
    refine lintegral_congr fun p => ?_
    rw [hfdef, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have hind : ∫⁻ p, E.indicator 1 p ^ (2 : ℝ) ∂(P.prod P) = (P.prod P) E := by
    have : ∀ p, E.indicator (1 : Config m × Config m → ℝ≥0∞) p ^ (2 : ℝ) = E.indicator 1 p := by
      intro p
      by_cases hp : p ∈ E
      · rw [Set.indicator_of_mem hp, Pi.one_apply, ENNReal.one_rpow]
      · rw [Set.indicator_of_notMem hp, ENNReal.zero_rpow_of_pos (by norm_num)]
    simp_rw [this]
    exact lintegral_indicator_one hE
  have hsplit : ∀ p, f p = f p * E.indicator (1 : Config m × Config m → ℝ≥0∞) p := by
    intro p
    by_cases hp : p ∈ E
    · rw [Set.indicator_of_mem hp, Pi.one_apply, mul_one]
    · have : X p.1 = X (resample G p.1 p.2) := by
        by_contra h
        exact hp h
      rw [Set.indicator_of_notMem hp, mul_zero]
      show ENNReal.ofReal |X p.1 - X (resample G p.1 p.2)| = 0
      rw [this, sub_self, abs_zero, ENNReal.ofReal_zero]
  rw [hl1, lintegral_congr hsplit]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (P.prod P) Real.HolderConjugate.two_two
    hf.aemeasurable ((measurable_one.indicator hE).aemeasurable)
  rw [hes, ← hind]
  exact hH

/-- **Cauchy–Schwarz in `v` and the weights jointly** (the proof of [AB26, Lemma 6.4]): for an
average `F̄ = V⁻¹ ∑_{v<V} F_v` of measurable functions,
`(E|F̄ − F̄^G|)² ≤ (V⁻¹ ∑_v E(F_v − F_v^G)²) · (V⁻¹ ∑_v P⊗P(F_v ≠ F_v^G))`. -/
theorem l1Term_average_sq_le {P : Measure (Config m)} [IsProbabilityMeasure P]
    (F : ℕ → Config m → ℝ) (hF : ∀ v, Measurable (F v)) {V : ℕ} (hV : 0 < V)
    (G : Set (Sym2 (Vertex m))) :
    Gain.l1Term P (fun ω => (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, F v ω) G ^ 2 ≤
      ((V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, esTerm P (F v) G) *
        ((V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V,
          (P.prod P) {p | F v p.1 ≠ F v (resample G p.1 p.2)}) := by
  set a : ℕ → ℝ≥0∞ := fun v => esTerm P (F v) G
  set b : ℕ → ℝ≥0∞ := fun v => (P.prod P) {p | F v p.1 ≠ F v (resample G p.1 p.2)}
  have hhalf : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_mul]; norm_num
  have hcs : ∑ v ∈ Finset.range V, a v ^ (1 / 2 : ℝ) * b v ^ (1 / 2 : ℝ) ≤
      (∑ v ∈ Finset.range V, a v) ^ (1 / 2 : ℝ) * (∑ v ∈ Finset.range V, b v) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.inner_le_Lp_mul_Lq (s := Finset.range V) (fun v => a v ^ (1 / 2 : ℝ))
      (fun v => b v ^ (1 / 2 : ℝ)) Real.HolderConjugate.two_two
    simpa only [hhalf] using h
  have hstep : Gain.l1Term P (fun ω => (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, F v ω) G ≤
      (V : ℝ≥0∞)⁻¹ * ((∑ v ∈ Finset.range V, a v) ^ (1 / 2 : ℝ) *
        (∑ v ∈ Finset.range V, b v) ^ (1 / 2 : ℝ)) :=
    (l1Term_average_le P F hF hV G).trans (by
      gcongr
      exact (Finset.sum_le_sum fun v _ => l1Term_le_esTerm_rpow_mul (hF v) G).trans hcs)
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc Gain.l1Term P (fun ω => (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, F v ω) G ^ 2
      ≤ ((V : ℝ≥0∞)⁻¹ * ((∑ v ∈ Finset.range V, a v) ^ (1 / 2 : ℝ) *
        (∑ v ∈ Finset.range V, b v) ^ (1 / 2 : ℝ))) ^ 2 := pow_le_pow_left' hstep 2
    _ = ((V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, a v) *
        ((V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, b v) := by
      rw [mul_pow, mul_pow, hsq, hsq]
      ring

end CurvatureVariance.Paper.Gain
