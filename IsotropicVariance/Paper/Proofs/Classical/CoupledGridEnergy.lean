/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.CommonFirstCoupling
public import IsotropicVariance.Paper.Proofs.Classical.GridOverlap
public import IsotropicVariance.Paper.Proofs.Classical.ReplacementEnergy
public import IsotropicVariance.Paper.Proofs.Classical.GridDensity

/-! # One common old field for all conditional grid replacements -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Classical
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra IsotropicVariance.Infra.WhiteNoise

/-- Injective enumeration preserves the grid overlap bound. -/
theorem card_indexed_gridNeighborhood_near_le {m n : ℕ}
    (z : Fin n → Coord (Pt m) → ℤ) (hz : Function.Injective z) (x : Pt m) :
    (Finset.univ.filter fun i => ∃ y ∈ gridNeighborhood (z i), dist y x ≤ 1).card ≤
      9 ^ Module.finrank ℝ (Pt m) := by
  let J := Finset.univ.image z
  have hEq : (Finset.univ.filter fun i => ∃ y ∈ gridNeighborhood (z i), dist y x ≤ 1).image z =
      J.filter (fun k => ∃ y ∈ gridNeighborhood k, dist y x ≤ 1) := by
    ext k
    simp only [J, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, hi⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hi, rfl⟩
  have hCard := Finset.card_image_of_injective
    (Finset.univ.filter fun i => ∃ y ∈ gridNeighborhood (z i), dist y x ≤ 1) hz
  rw [← hCard, hEq]
  exact card_gridNeighborhood_near_le J x

/-- The actual conditional refresh laws admit a joint realization on which
the whole summed replacement energy is bounded linearly in endpoint distance. -/
theorem exists_grid_energy_coupling {m n : ℕ} (X : Setting m) {a b : ℝ} (ha : 0 < a)
    (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b)
    (z : Fin n → Coord (Pt m) → ℤ) (hz : Function.Injective z) (u v : Pt m) :
    ∃ Q : Measure (X.Ω × (Fin n → X.Ω)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = X.P ∧
      (∀ i, Q.map (fun p => (p.1, p.2 i)) = Noise.resampleLaw X.toNoiseModel (gridCell (z i))) ∧
      (∀ᵐ p ∂Q,
        let d := Module.finrank ℝ (Pt m)
        let B := (b / a) * (b * (5 * (d : ℝ)) + 1)
        (∑ i : Fin n, max (X.passTime (p.2 i) u v - X.passTime p.1 u v) 0 ^ 2) ≤
          2 * B ^ 2 * (9 ^ d : ℕ) * (b * dist u v / a + 1)) := by
  have : Nonempty X.Ω := nonempty_of_isProbabilityMeasure X.P
  obtain ⟨Q, hQ, hFirst, hPairs⟩ := exists_common_first_coupling X.P
    (fun i => Noise.resampleLaw X.toNoiseModel (gridCell (z i)))
    (fun i => (Noise.resampleLaw_old X.toNoiseModel (gridCell (z i))).map_eq)
  refine ⟨Q, hQ, hFirst, hPairs, ?_⟩
  have hAgree (i : Fin n) : ∀ᵐ p ∂Q, ∀ x ∉ gridNeighborhood (z i),
      X.ρ p.1 x = X.ρ (p.2 i) x := by
    have hh : ∀ᵐ p ∂Q.map (fun p => (p.1, p.2 i)),
        ∀ x ∉ gridNeighborhood (z i), X.ρ p.1 x = X.ρ p.2 x := by
      rw [hPairs i]
      exact resampleLaw_ae_density_eq_grid X (z i)
    exact ae_of_ae_map (by fun_prop) hh
  filter_upwards [ae_all_iff.mpr hAgree] with p hp
  exact sum_changes_sq_le X ha (by positivity) hBounds Finset.univ
    (fun i => gridNeighborhood (z i)) (9 ^ Module.finrank ℝ (Pt m))
    (fun _ _ => isClosed_gridNeighborhood _)
    (fun _ _ _ hx _ hy => dist_le_of_mem_gridNeighborhood hx hy)
    (card_indexed_gridNeighborhood_near_le z hz) p.1 p.2
    (fun i _ x hx => (hp i x hx).symm) u v

end IsotropicVariance.Paper.Proofs.Classical
