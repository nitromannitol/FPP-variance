/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Main
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# Measurable families of arc-length measures

Cumulative variation is a supremum of continuous partition sums, hence lower semicontinuous
in the curve. Its finite real value supplies a measurable Stieltjes kernel. Integrating a
jointly Borel density against this kernel proves joint measurability of the literal curve cost.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace IsotropicVariance.Infra.Measurability
open Curves

/-- Parameter integrals remain measurable when each kernel measure is finite, without a
uniform mass bound. Truncate the parameter space by the total kernel mass. -/
lemma measurable_lintegral_pointwiseFinite {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (κ : Kernel A B) (hfin : ∀ a, κ a univ ≠ ⊤)
    {f : A × B → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ b, f (a, b) ∂κ a) := by
  classical
  have hs (n : ℕ) : MeasurableSet {a | κ a univ ≤ n} :=
    measurableSet_le (κ.measurable_coe MeasurableSet.univ) measurable_const
  let κn (n : ℕ) := Kernel.piecewise (hs n) κ 0
  have hκn (n : ℕ) : IsFiniteKernel (κn n) := by
    refine ⟨n, by finiteness, ?_⟩
    intro a
    change (if a ∈ {a | κ a univ ≤ n} then κ a else (0 : Kernel A B) a) univ ≤ n
    split_ifs with h
    · exact h
    · simp
  have hm (n : ℕ) : Measurable (fun a => ∫⁻ b, f (a, b) ∂κn n a) := by
    let := hκn n
    exact hf.lintegral_kernel_prod_right'
  have heq (a : A) : (∫⁻ b, f (a, b) ∂κ a) = ⨆ n, ∫⁻ b, f (a, b) ∂κn n a := by
    apply le_antisymm
    · obtain ⟨n, hn⟩ := exists_nat_gt (κ a univ).toReal
      have hle : κ a univ ≤ n := (ENNReal.toReal_le_toReal (hfin a) (by finiteness)).mp
        (by simpa only [ENNReal.toReal_natCast] using hn.le)
      apply le_iSup_of_le n
      simp only [κn, Kernel.piecewise_apply, hle, mem_ofPred_eq, ↓reduceIte, le_refl]
    · apply iSup_le
      intro n
      dsimp [κn]
      rw [Kernel.piecewise_apply]
      split_ifs <;> simp
  have heqf : (fun a => ∫⁻ b, f (a, b) ∂κ a) =
      fun a => ⨆ n, ∫⁻ b, f (a, b) ∂κn n a := funext heq
  rw [heqf]
  exact Measurable.iSup hm

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The variation of the constant extension is measurable in a continuous curve. -/
lemma measurable_variation (s : Set ℝ) :
    Measurable (fun γ : C(unitInterval, E) =>
      eVariationOn (fun t => γ (projIcc 0 1 zero_le_one t)) s) := by
  apply LowerSemicontinuous.measurable
  intro γ r hr
  apply eVariationOn.lowerSemicontinuous_aux (f := fun t => γ (projIcc 0 1 zero_le_one t)) _ hr
  intro t _
  exact (continuous_eval_const (projIcc 0 1 zero_le_one t)).tendsto γ

/-- Continuous maps with finite variation, carrying the Borel subtype structure. -/
abbrev BVCurves (E : Type*) [MetricSpace E] :=
  {γ : C(unitInterval, E) //
    BoundedVariationOn (fun t : ℝ => γ (projIcc 0 1 zero_le_one t)) (Icc 0 1)}

namespace BVCurves

/-- The literal rectifiable curve represented by a continuous BV map. -/
noncomputable def curve (γ : BVCurves E) : RectifiableCurve E where
  toFun t := γ.1 (projIcc 0 1 zero_le_one t)
  continuousOn := (γ.1.continuous.comp continuous_projIcc).continuousOn
  boundedVariationOn := γ.2

omit [MeasurableSpace E] [BorelSpace E] in
lemma measurable_cumulativeLength (t : ℝ) :
    Measurable (fun γ : BVCurves E => γ.curve.cumulativeLength t) := by
  have h := ((measurable_variation (E := E)
    (Icc (0 : ℝ) 1 ∩ Icc 0 (projIcc 0 1 zero_le_one t))).comp (measurable_subtype_coe : Measurable (fun γ : BVCurves E => γ.1))).ennreal_toReal
  simpa only [RectifiableCurve.cumulativeLength, variationOnFromTo,
    (projIcc 0 1 zero_le_one t).property.1, ↓reduceIte, curve, Function.comp_def] using h

omit [MeasurableSpace E] [BorelSpace E] in
lemma measurable_arcLengthMeasure : Measurable (fun γ : BVCurves E => γ.curve.arcLengthMeasure) := by
  apply Measurable.measure_of_isPiSystem (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic
  · rintro s ⟨t, rfl⟩
    simp_rw [RectifiableCurve.arcLengthMeasure_Iic]
    exact (measurable_cumulativeLength t).ennreal_ofReal
  · simp_rw [RectifiableCurve.arcLengthMeasure_univ]
    have h := (measurable_cumulativeLength (E := E) 1).ennreal_ofReal
    simpa only [RectifiableCurve.cumulativeLength_of_one_le _ le_rfl,
      ENNReal.ofReal_toReal (RectifiableCurve.length_ne_top _)] using h

/-- Arc-length measure as a measurable kernel of the curve. -/
noncomputable def arcKernel : Kernel (BVCurves E) ℝ where
  toFun γ := γ.curve.arcLengthMeasure
  measurable' := measurable_arcLengthMeasure

/-- Joint measurability of cost for a jointly Borel density, directly from arc-length measures. -/
theorem measurable_cost {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Ω × E → ℝ≥0∞} (hρ : Measurable ρ) :
    Measurable (fun p : BVCurves E × Ω => p.1.curve.cost (fun x => ρ (p.2, x))) := by
  let κ : Kernel (BVCurves E × Ω) ℝ := arcKernel.comap Prod.fst measurable_fst
  have h_eval : Measurable (fun p : (BVCurves E × Ω) × ℝ =>
      ρ (p.1.2, p.1.1.1 (projIcc 0 1 zero_le_one p.2))) := by
    apply hρ.comp
    apply Measurable.prodMk (by fun_prop)
    exact continuous_eval.measurable.comp
      ((measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).prodMk
        ((continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).measurable.comp measurable_snd))
  exact measurable_lintegral_pointwiseFinite κ (fun p =>
    by change p.1.curve.arcLengthMeasure univ ≠ ⊤; exact measure_ne_top _ _) h_eval

end BVCurves
end IsotropicVariance.Infra.Measurability
