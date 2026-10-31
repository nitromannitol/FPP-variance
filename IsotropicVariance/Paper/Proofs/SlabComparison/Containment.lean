/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.FiniteMesh
public import IsotropicVariance.Paper.Proofs.SlabComparison.NearOptimal

/-! # A deterministic containing cube for every near-optimal curve -/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

/-- Every coordinate is bounded by the Euclidean norm. -/
lemma abs_coord_le_norm (v : Pt m) (k : Fin (m + 1)) : |Pt.coords v k| ≤ ‖v‖ := by
  refine Fin.cases ?_ (fun i => ?_) k
  · exact Profiles.abs_lon_le_norm v
  · exact Profiles.abs_tr_apply_le_norm v i

/-- The cube of half-side `L` lies in the ball of radius `(m+1)L`. -/
lemma dist_le_dim_mul_of_mem_cube {z x : Pt m} {L : ℝ} (hL : 0 ≤ L)
    (hx : x ∈ cubeAround z L) : dist x z ≤ (m + 1 : ℝ) * L := by
  rw [dist_eq_norm]
  exact norm_le_dim_mul hL (hx 0) (fun k => hx k.succ)

/-- Lower ellipticity controls every point on a near-optimal curve by its endpoint cost. -/
lemma oneOptimal_image_bound (X : Setting m) (ω : X.Ω) {a b : ℝ}
    (hbound : ∀ x y, a * dist x y ≤ X.passTime ω x y ∧ X.passTime ω x y ≤ b * dist x y)
    {u v : Pt m} (γ : IsotropicVariance.RectifiableCurve (Pt m))
    (hγ : IsOneOptimal (X.ρ ω) univ u v γ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    a * dist u (γ.toFun t) ≤ b * dist u v + 1 := by
  have hh := ordered_passTime_defect X ω γ hγ (a := 0) (b := t) (c := 1)
    le_rfl ht.1 ht.2 le_rfl
  rw [hγ.1, hγ.2.1] at hh
  have hnonneg : 0 ≤ X.passTime ω (γ.toFun t) v := ENNReal.toReal_nonneg
  linarith [(hbound u (γ.toFun t)).1, (hbound u v).2]

end IsotropicVariance.Paper.Proofs.SlabComparison
