/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.NearOptimal

/-! # Ordered passage sums and comparison with the slab minimum -/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

/-- The minimum is at most the cost of any particular admissible chain. -/
lemma slabMinimum_le_slabSum (X : Setting m) (ω : X.Ω) (b : ℝ) (M : ℕ) (s : ℝ)
    (τ : Pt m) (x : Fin (M + 1) → Pt m) (hx : IsAdmissible M s τ x) :
    X.F b M s τ ω ≤ slabSum b (X.ρ ω) M s τ x := by
  let f : {x : Fin (M + 1) → Pt m // IsAdmissible M s τ x} → ℝ :=
    fun x => slabSum b (X.ρ ω) M s τ x
  have hbounded : BddBelow (range f) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact slabSum_nonneg b (X.ρ ω) M s τ x
  exact ciInf_le (f := f) hbounded ⟨x, hx⟩

end IsotropicVariance.Paper.Proofs.SlabComparison
