/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.ProfilesSlab
public import IsotropicVariance.Paper.Contracts.Slab
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The distances between the cubes of an admissible pair

`cubePair_dists`: bounds on the distance between two points of the cubes of an admissible pair, used
in the proof of Proposition `prop:profiles` for `s ≤ N/4`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

universe u

namespace IsotropicVariance.Paper.Proofs.Profiles

open Infra.Os Infra.Slab

variable {m : ℕ}

/-- Distances in an admissible pair of transverse cubes at distance `s` with
`4√m W ≤ s/128`. -/
lemma cubePair_dists {p : CubePair m} {s W : ℝ} (hp : p.IsAdmissible s W 1) (hs : 0 < s)
    (hW : 4 * Real.sqrt m * W ≤ s / 128) :
    (∀ u ∈ p.first, dist u p.center₁ ≤ s / 256) ∧ (∀ v ∈ p.second, dist v p.center₂ ≤ s / 256) ∧
      s ≤ dist p.center₁ p.center₂ ∧ dist p.center₁ p.center₂ ≤ 3 / 2 * s := by
  obtain ⟨hdist, h1₀, h1, h2₀, h2, hslope⟩ := hp
  have hsqm := Real.sqrt_nonneg (m : ℝ)
  have hoff : ‖p.offset‖ ≤ s := by
    have : ‖p.offset‖ / p.dist ≤ 1 := hslope
    rw [hdist, div_le_one hs] at this; exact this
  have hr_eq : dist p.center₁ p.center₂ = Real.sqrt (s ^ 2 + ‖p.offset‖ ^ 2) := by
    rw [cubePair_dist_centers, hdist]
  refine ⟨fun u hu => ?_, fun v hv => ?_, ?_, ?_⟩
  · refine (cubePair_dist_center₁_le p hu h1₀).trans ?_
    have := mul_le_mul_of_nonneg_left h1 hsqm
    linarith only [this, hW]
  · refine (cubePair_dist_center₂_le p hv h2₀).trans ?_
    have := mul_le_mul_of_nonneg_left h2 hsqm
    linarith only [this, hW]
  · rw [hr_eq]; exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))
  · rw [hr_eq, Real.sqrt_le_left (by positivity)]
    have h := pow_le_pow_left₀ (norm_nonneg _) hoff 2
    linarith only [h, sq_nonneg s]

end IsotropicVariance.Paper.Proofs.Profiles
