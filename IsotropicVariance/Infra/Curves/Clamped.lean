/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Congr
public import Mathlib.Topology.UnitInterval

/-! # Constant extension and global Lipschitz bounds -/

@[expose] public section
open Set Function
open scoped ENNReal NNReal

namespace IsotropicVariance.RectifiableCurve
variable {E : Type*} [PseudoMetricSpace E]

lemma boundedVariationOn_clamped (γ : RectifiableCurve E) :
    BoundedVariationOn γ.clamped univ := by
  apply ne_top_of_le_ne_top γ.boundedVariationOn
  exact eVariationOn.comp_le_of_monotoneOn γ.toFun
    (fun t : ℝ => (projIcc 0 1 zero_le_one t : ℝ))
    (fun s _ t _ hst => monotone_projIcc zero_le_one hst)
    (fun t _ => (projIcc 0 1 zero_le_one t).property)

lemma lipschitzWith_clamped (γ : RectifiableCurve E) {K : ℝ≥0}
    (hγ : LipschitzOnWith K γ.toFun (Icc 0 1)) : LipschitzWith K γ.clamped := by
  have hclip : LipschitzWith 1 (fun t : ℝ => (projIcc 0 1 zero_le_one t : ℝ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simpa [Real.dist_eq] using
      (abs_projIcc_sub_projIcc (a := (0 : ℝ)) (b := 1) (c := s) (d := t) zero_le_one)
  unfold clamped
  change LipschitzWith K (fun t => γ.toFun (projIcc (0 : ℝ) 1 zero_le_one t : ℝ))
  rw [← lipschitzOnWith_univ]
  simpa only [mul_one, Function.comp_def, clamped] using hγ.comp
    (hclip.lipschitzOnWith (s := univ))
    (fun t _ => (projIcc 0 1 zero_le_one t).property)

end IsotropicVariance.RectifiableCurve
