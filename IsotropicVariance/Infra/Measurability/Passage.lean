/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.ArcKernel
public import IsotropicVariance.Infra.Measurability.SectionInfENNReal
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Universal measurability of the literal rectifiable passage time

The Borel parameter space consists of all continuous maps with finite variation. Thus the
projection argument does not require compact cost sublevels or continuity of the density.
-/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal

namespace IsotropicVariance.Infra.Measurability
open Curves

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

instance BVCurves.standardBorel [CompleteSpace E] [SecondCountableTopology E] :
    StandardBorelSpace (BVCurves E) :=
  (measurableSet_eq_fun (measurable_variation (E := E) (Icc 0 1)) measurable_const).compl.standardBorel

/-- Every literal rectifiable curve has a representative in the Borel BV carrier. -/
noncomputable def BVCurves.ofRectifiable (γ : RectifiableCurve E) : BVCurves E :=
  ⟨γ.toContinuousMap, γ.boundedVariationOn_clamped.mono (subset_univ _)⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma BVCurves.ofRectifiable_eq (γ : RectifiableCurve E) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (BVCurves.ofRectifiable γ).curve.toFun t = γ.toFun t := by
  change γ.toFun (projIcc 0 1 zero_le_one t : ℝ) = γ.toFun t
  simp only [projIcc_of_mem zero_le_one ht]

/-- The infimum over exactly the rectifiable curves with the specified endpoints. -/
noncomputable def passageTime (ρ : E → ℝ≥0∞) (u v : E) : ℝ≥0∞ :=
  ⨅ γ : RectifiableCurve E, ⨅ (_ : γ.toFun 0 = u), ⨅ (_ : γ.toFun 1 = v), γ.cost ρ

omit [MeasurableSpace E] [BorelSpace E] in
lemma passageTime_eq_bv (ρ : E → ℝ≥0∞) (u v : E) :
    passageTime ρ u v =
      ⨅ γ : BVCurves E, ⨅ (_ : γ.curve.toFun 0 = u),
        ⨅ (_ : γ.curve.toFun 1 = v), γ.curve.cost ρ := by
  apply le_antisymm
  · refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => ?_
    exact iInf_le_of_le γ.curve (iInf_le_of_le h0 (iInf_le _ h1))
  · refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => ?_
    let δ := BVCurves.ofRectifiable γ
    have heq : EqOn δ.curve.toFun γ.toFun (Icc 0 1) :=
      fun _ ht => BVCurves.ofRectifiable_eq γ ht
    have hd0 : δ.curve.toFun 0 = u := (heq (by simp)).trans h0
    have hd1 : δ.curve.toFun 1 = v := (heq (by simp)).trans h1
    exact (iInf_le_of_le δ (iInf_le_of_le hd0 (iInf_le _ hd1))).trans_eq
      (RectifiableCurve.cost_congr_curve heq ρ)

/-- Borel densities give universally measurable passage times for each fixed endpoint pair. -/
theorem nullMeasurable_passageTime {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [CompleteSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [SFinite μ] {ρ : Ω × E → ℝ≥0∞} (hρ : Measurable ρ) (u v : E) :
    NullMeasurable (fun ω => passageTime (fun x => ρ (ω, x)) u v) μ := by
  let B : Set (BVCurves E × Ω) := {p | p.1.curve.toFun 0 = u ∧ p.1.curve.toFun 1 = v}
  have hm (t : ℝ) : Measurable (fun p : BVCurves E × Ω => p.1.curve.toFun t) := by
    exact (continuous_eval_const (projIcc 0 1 zero_le_one t)).measurable.comp
      (measurable_subtype_coe.comp measurable_fst)
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun (hm 0) measurable_const).inter
      (measurableSet_eq_fun (hm 1) measurable_const)
  have heq : (fun ω => passageTime (fun x => ρ (ω, x)) u v) =
      sectionInfENNReal B (fun p => p.1.curve.cost (fun x => ρ (p.2, x))) := by
    funext ω
    rw [passageTime_eq_bv]
    simp only [sectionInfENNReal, B, mem_ofPred_eq, iInf_and]
  rw [heq]
  exact nullMeasurable_sectionInfENNReal μ hB (BVCurves.measurable_cost hρ)

end IsotropicVariance.Infra.Measurability
