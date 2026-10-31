/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.LocalizedVersion
public import IsotropicVariance.Paper.Proofs.Classical.GridBoundary
public import IsotropicVariance.Paper.Proofs.Classical.RegionalProduct

/-! # Finite independent grid coordinates representing endpoint passage time -/

@[expose] public section
open MeasureTheory Set Metric Filter
open scoped Classical
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra IsotropicVariance.Infra.WhiteNoise

/-- Passage time is a Borel function of finitely many independent regional
codes, almost surely. The regions are distinct half-open unit grid cells. -/
theorem exists_finite_grid_passTime_representation {m : ℕ} (X : Setting m)
    {a b : ℝ} (ha : 0 < a) (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b)
    (u v : Pt m) :
    ∃ (n : ℕ) (_hn : 0 < n) (z : Fin n → Coord (Pt m) → ℤ), Function.Injective z ∧
      ∃ Φ : Fin n → X.Ω → ℕ → Bool,
        (∀ i, Measurable[X.info (gridCell (z i))] (Φ i)) ∧
        ∃ f : (Fin n → ℕ → Bool) → ℝ, Measurable f ∧
          ((fun ω => f (fun i => Φ i ω)) =ᵐ[X.P] fun ω => X.passTime ω u v) ∧
          X.P.map (fun ω i => Φ i ω) = Measure.pi (fun i => X.P.map (Φ i)) := by
  let R := (b * dist u v + 1) / a
  have hFinite := finite_nearoptimal_grid_family u (R + 3)
  let J := insert (gridIndex u) hFinite.toFinset
  let I := {z : Coord (Pt m) → ℤ // z ∈ J}
  let e := Fintype.equivFin I
  let n := Fintype.card I
  let z : Fin n → Coord (Pt m) → ℤ := fun i => (e.symm i).1
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨⟨gridIndex u, Finset.mem_insert_self _ _⟩⟩
  have hz : Function.Injective z := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  obtain ⟨V, hV, hVae⟩ := exists_localized_passTime_version X ha hBounds u v
  have hCover : ball u (R + 2) ⊆ ⋃ i, gridCell (z i) := by
    intro x hx
    have hxK : x ∈ gridNeighborhood (gridIndex x) := by
      intro k
      have hh := coord_bounds_of_mem_gridCell (mem_gridCell x) k
      constructor <;> linarith only [hh.1, hh.2]
    have hxJ : gridIndex x ∈ J := by
      apply Finset.mem_insert_of_mem
      apply hFinite.mem_toFinset.mpr
      refine ⟨x, ?_, hxK⟩
      change dist x u ≤ R + 3
      change dist x u < R + 2 at hx
      linarith only [hx]
    refine mem_iUnion.mpr ⟨e ⟨gridIndex x, hxJ⟩, ?_⟩
    have he : z (e ⟨gridIndex x, hxJ⟩) = gridIndex x := by
      simp only [z, Equiv.symm_apply_apply]
    rw [he]
    exact mem_gridCell x
  have hVm : Measurable[X.info (⋃ i, gridCell (z i))] V :=
    hV.mono (X.info_mono hCover) le_rfl
  have hDis : Pairwise (fun i j => Disjoint (gridCell (z i)) (gridCell (z j))) :=
    fun i j hij => pairwiseDisjoint_gridCell (fun he => hij (hz he))
  obtain ⟨Φ, hΦ, f, hf, hVf, hLaw⟩ := exists_product_representation X.toNoiseModel hn
    (fun i => gridCell (z i)) (fun i => measurableSet_gridCell (z i))
    (fun i => volume_frontier_gridCell (z i)) hDis hVm
  exact ⟨n, hn, z, hz, Φ, hΦ, f, hf, hVf.symm.trans hVae, hLaw⟩

end IsotropicVariance.Paper.Proofs.Classical
