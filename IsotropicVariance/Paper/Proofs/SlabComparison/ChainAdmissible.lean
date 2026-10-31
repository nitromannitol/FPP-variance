/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.ChainDirections
public import IsotropicVariance.Paper.Proofs.SlabComparison.HyperplaneHits

/-! # The norm of a vector with a given longitudinal coordinate -/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

lemma norm_sub_smul_e₁_of_lon {v : Pt m} {s : ℝ} (h : Pt.lon v = s) :
    ‖v - s • e₁‖ = ‖Pt.tr v‖ := by
  have hh := Profiles.norm_sq_eq_lon_tr (v - s • e₁)
  simp only [Pt.lon_sub, Pt.lon_smul, Pt.lon_e₁, h, mul_one, sub_self,
    Pt.tr_sub, Pt.tr_smul, Pt.tr_e₁, smul_zero, sub_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_add] at hh
  nlinarith [norm_nonneg (v - s • e₁), norm_nonneg (Pt.tr v)]

end IsotropicVariance.Paper.Proofs.SlabComparison
