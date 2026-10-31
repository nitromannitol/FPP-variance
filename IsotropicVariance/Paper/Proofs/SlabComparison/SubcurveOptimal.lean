/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.ExistsNearOptimal
import IsotropicVariance.Paper.Proofs.Classical.NearOptimal

/-! # Literal near-optimality of subcurves -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
open IsotropicVariance.Paper.Proofs.Classical (setting_curve_cost_ne_top)
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

/-- The real subarc inequality gives the exact paper predicate for the literal subcurve. -/
theorem oneOptimal_subcurve (X : Setting m) (ω : X.Ω)
    (γ : IsotropicVariance.RectifiableCurve (Pt m)) {u v : Pt m}
    (hγ : IsOneOptimal (X.ρ ω) univ u v γ) {a c : ℝ}
    (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) :
    IsOneOptimal (X.ρ ω) univ (γ.toFun a) (γ.toFun c) (γ.subcurve a c ha hac hc) := by
  refine ⟨γ.subcurve_start ha hac hc, γ.subcurve_end ha hac hc, fun _ _ => mem_univ _, ?_⟩
  have heq : restrictedPassageTime (X.ρ ω) univ (γ.toFun a) (γ.toFun c) =
      X.passTime ω (γ.toFun a) (γ.toFun c) := by
    simp [restrictedPassageTime, Setting.passTime, IsotropicVariance.passageTime]
  rw [heq]
  apply (ENNReal.le_ofReal_iff_toReal_le (setting_curve_cost_ne_top X ω _)
    (add_nonneg ENNReal.toReal_nonneg zero_le_one)).mpr
  exact pieceCost_le_passTime_add_one X ω γ hγ ha hac hc

end IsotropicVariance.Paper.Proofs.SlabComparison
