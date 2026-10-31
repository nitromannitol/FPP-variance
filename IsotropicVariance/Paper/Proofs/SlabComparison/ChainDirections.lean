/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.GeometryScale
public import IsotropicVariance.Paper.Proofs.SlabComparison.Cones
public import IsotropicVariance.Paper.Proofs.Profiles.TreeGeometry

/-! # Directions of vectors -/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

lemma direction_neg (v : Pt m) : direction (-v) = -direction v := by
  simp only [direction, norm_neg, smul_neg]

lemma direction_smul_e₁ {ℓ : ℝ} (hℓ : 0 < ℓ) : direction (ℓ • (e₁ : Pt m)) = e₁ := by
  simp [direction, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ, Paper.norm_e₁,
    smul_smul, hℓ.ne']

end IsotropicVariance.Paper.Proofs.SlabComparison
