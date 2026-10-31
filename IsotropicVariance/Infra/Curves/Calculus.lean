/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Bridge
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Fundamental theorem of calculus for Lipschitz curves in finite dimension -/

@[expose] public section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace IsotropicVariance.Infra.Curves
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma integrableOn_deriv_of_lipschitz {f : ℝ → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    (a b : ℝ) : IntegrableOn (deriv f) (Icc a b) := by
  borelize E
  apply Integrable.mono' (integrable_const (K : ℝ))
    (measurable_deriv f).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => norm_deriv_le_of_lipschitz hf

/-- Vector-valued FTC, obtained by applying the scalar absolutely-continuous FTC to every
continuous linear functional. -/
theorem integral_deriv_eq_sub_of_lipschitz {f : ℝ → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) :
    (∫ t in a..b, deriv f t) = f b - f a := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro g
  have hint : IntervalIntegrable (deriv f) volume a b :=
    intervalIntegrable_iff.mpr
      ((integrableOn_deriv_of_lipschitz hf (min a b) (max a b)).mono_set Ioc_subset_Icc_self)
  rw [← g.intervalIntegral_comp_comm hint, map_sub]
  have hscalar : (∫ t in a..b, deriv (fun t => g (f t)) t) = g (f b) - g (f a) :=
    (g.lipschitzWith.comp hf).lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  rw [← hscalar]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hf.ae_differentiableAt] with t ht
  intro _
  exact (g.hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt).deriv.symm

end IsotropicVariance.Infra.Curves
