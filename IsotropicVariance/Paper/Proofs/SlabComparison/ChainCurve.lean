/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.ChainAdmissible
public import IsotropicVariance.Paper.Proofs.SlabComparison.ChainCost
public import IsotropicVariance.Paper.Proofs.SlabComparison.SubcurveOptimal

/-! # The slope of the admissible points of a chain -/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

lemma admissible_slope_le_two {M : ℕ} {s : ℝ} (hs : 0 < s) {τ : Pt m}
    {x : Fin (M + 1) → Pt m} (hx : IsAdmissible M s τ x) (i : Fin M) :
    (chainSlab s τ i).slope (x i.castSucc) (x i.succ) ≤ 2 := by
  have hn := hx.2.2.2 i
  have htri := norm_add_le (x i.succ - x i.castSucc - s • e₁) (s • (e₁ : Pt m))
  have heq : x i.succ - x i.castSucc - s • e₁ + s • e₁ = x i.succ - x i.castSucc := by abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hs, Paper.norm_e₁, mul_one,
    ← dist_eq_norm'] at htri
  change Real.sqrt (dist (x i.castSucc) (x i.succ) ^ 2 - s ^ 2) / s ≤ 2
  rw [div_le_iff₀ hs]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [dist_nonneg (x := x i.castSucc) (y := x i.succ)]

end IsotropicVariance.Paper.Proofs.SlabComparison
