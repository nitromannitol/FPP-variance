/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.GridBounds
public import IsotropicVariance.Paper.Proofs.Classical.RegionalDensity

/-! # Simultaneous density agreement outside an enlarged grid cell -/

@[expose] public section
open MeasureTheory Set Metric Filter
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra IsotropicVariance.Infra.WhiteNoise

/-- A refresh in a half-open cell preserves the entire density outside its
closed enlarged neighborhood, on one full-measure event. -/
theorem resampleLaw_ae_density_eq_grid {m : ℕ} (X : Setting m)
    (z : Coord (Pt m) → ℤ) :
    ∀ᵐ p ∂Noise.resampleLaw X.toNoiseModel (gridCell z),
      ∀ x ∉ gridNeighborhood z, X.ρ p.1 x = X.ρ p.2 x := by
  let K : Set (Pt m) := {x | ∀ i, (z i : ℝ) ≤ coord x i ∧ coord x i ≤ (z i : ℝ) + 1}
  have hK : IsClosed K := by
    have heq : K = ⋂ i, {x : Pt m | (z i : ℝ) ≤ coord x i ∧ coord x i ≤ (z i : ℝ) + 1} := by
      ext x; simp only [K, mem_ofPred_eq, mem_iInter]
    rw [heq]
    exact isClosed_iInter fun i =>
      (isClosed_le continuous_const (contDiff_coord (n := 0) i).continuous).inter
        (isClosed_le (contDiff_coord (n := 0) i).continuous continuous_const)
  have hCK : gridCell z ⊆ K := fun x hx i =>
    ⟨(coord_bounds_of_mem_gridCell hx i).1, (coord_bounds_of_mem_gridCell hx i).2.le⟩
  have hAgree := resampleLaw_ae_density_eq_on_open X hK.isOpen_compl (compl_subset_compl.mpr hCK)
  filter_upwards [hAgree] with p hp x hx
  exact hp x (closedBall_subset_core_compl_of_notMem_gridNeighborhood hx)

end IsotropicVariance.Paper.Proofs.Classical
