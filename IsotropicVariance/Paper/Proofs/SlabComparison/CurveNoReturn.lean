/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.NearOptimal
public import IsotropicVariance.Paper.Proofs.SlabComparison.Excess

/-! # No radial returns for the paper's literal 1-optimal curves -/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
variable {m : ℕ}

/-- The no-return consequence of the uniform metric estimate, for every subarc of a
1-optimal curve. The first-hit parameter is supplied by continuity of the curve. -/
theorem curve_no_return (X : Setting m) (ω : X.Ω)
    (γ : IsotropicVariance.RectifiableCurve (Pt m)) {u v : Pt m}
    (hγ : IsOneOptimal (X.ρ ω) univ u v γ) {A S r : ℝ}
    (hA : 0 ≤ A) (hS : 1 ≤ S) (hr : 0 ≤ r)
    (hmetric : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      |X.passTime ω (γ.toFun a) (γ.toFun b) - dist (γ.toFun a) (γ.toFun b)| ≤
        A * (S * Real.sqrt (dist (γ.toFun a) (γ.toFun b)) + S ^ 2))
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 1)
    (hfirst : dist (γ.toFun a) (γ.toFun b) = r)
    (hlarge : noReturnScale A * S ^ 2 < r) :
    r / 2 < dist (γ.toFun a) (γ.toFun c) := by
  have ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans (hbc.trans hc)⟩
  have hb' : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab, hbc.trans hc⟩
  have hc' : c ∈ Icc (0 : ℝ) 1 := ⟨ha.trans (hab.trans hbc), hc⟩
  exact no_return_of_uniform_metric hA hS hr
    (hmetric a ha' b hb') (hmetric b hb' c hc') (hmetric a ha' c hc')
    (ordered_passTime_defect X ω γ hγ ha hab hbc hc) hfirst hlarge

end IsotropicVariance.Paper.Proofs.SlabComparison
