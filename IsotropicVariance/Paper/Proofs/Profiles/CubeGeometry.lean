/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.TreeGeometry
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Pairs of transverse cubes

Geometry of a pair of transverse cubes `(I, I')` at distance `s` (Section `sec:exponential`;
`CubePair`): the distance of the centers is `√(s² + |offset|²)`, the points of a cube of side
`a` are within `√m a/2` of its center, each cube is a rectangular box centered at its center
(degenerate in the direction across the slab), and the cubes lie on the two faces of the slab
of the pair.
-/

@[expose] public section

open Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Profiles

variable {m : ℕ}

lemma norm_le_of_abs_le {y : EuclideanSpace ℝ (Fin m)} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ k, |y k| ≤ ρ) : ‖y‖ ≤ Real.sqrt m * ρ := by
  have hsq : ‖y‖ ^ 2 ≤ (Real.sqrt m * ρ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    calc ∑ k, y k ^ 2 ≤ ∑ _k : Fin m, ρ ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h k) 2
      _ = m * ρ ^ 2 := by simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

lemma norm_le_of_lon_zero {x : Pt m} {ρ : ℝ} (hρ : 0 ≤ ρ) (h₀ : Pt.lon x = 0)
    (h : ∀ k, |Pt.tr x k| ≤ ρ) : ‖x‖ ≤ Real.sqrt m * ρ := by
  have h1 := norm_sq_eq_lon_tr x
  rw [h₀] at h1
  have h2 := norm_le_of_abs_le hρ h
  have : ‖x‖ = ‖Pt.tr x‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [h1]; ring)
  rw [this]; exact h2

section CubePair

variable (p : CubePair m)

open Paper.CubePair in

lemma cubePair_dist_centers : dist p.center₁ p.center₂ = Real.sqrt (p.dist ^ 2 + ‖p.offset‖ ^ 2) := by
  rw [Paper.CubePair.center₁, Paper.CubePair.center₂, p.motion.dist_map, dist_comm, dist_eq_norm, sub_zero,
    ← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_lon_tr]
  simp

lemma cubePair_dist_center₁_le {u : Pt m} (hu : u ∈ p.first) (h : 0 ≤ p.side₁) :
    dist u p.center₁ ≤ Real.sqrt m * (p.side₁ / 2) := by
  obtain ⟨x, ⟨hx₀, hx⟩, rfl⟩ := hu
  rw [Paper.CubePair.center₁, p.motion.dist_map, dist_eq_norm, sub_zero]
  exact norm_le_of_lon_zero (by positivity) hx₀ hx

lemma cubePair_dist_center₂_le {v : Pt m} (hv : v ∈ p.second) (h : 0 ≤ p.side₂) :
    dist v p.center₂ ≤ Real.sqrt m * (p.side₂ / 2) := by
  obtain ⟨x, ⟨hx₀, hx⟩, rfl⟩ := hv
  rw [Paper.CubePair.center₂, p.motion.dist_map, dist_eq_norm]
  apply norm_le_of_lon_zero (by positivity) (by simp [hx₀])
  intro k
  simpa using hx k

lemma cubePair_center₁_mem (h : 0 ≤ p.side₁) : p.center₁ ∈ p.first :=
  ⟨0, ⟨by simp, fun k => by simp; positivity⟩, rfl⟩

lemma cubePair_center₂_mem (h : 0 ≤ p.side₂) : p.center₂ ∈ p.second :=
  ⟨Pt.mk p.dist p.offset, ⟨by simp, fun k => by simp; positivity⟩, rfl⟩

lemma cubePair_isRectBox_first (h : 0 ≤ p.side₁) : IsRectBox p.first p.center₁ := by
  refine ⟨p.motion, 0, fun _ => p.side₁ / 2, le_rfl, fun _ => by positivity, rfl, ?_⟩
  simp only [Paper.CubePair.first, abs_nonpos_iff]

lemma cubePair_isRectBox_second (h : 0 ≤ p.side₂) : IsRectBox p.second p.center₂ := by
  refine ⟨(AffineIsometryEquiv.constVAdd ℝ (Pt m) (Pt.mk p.dist p.offset)).trans p.motion, 0,
    fun _ => p.side₂ / 2, le_rfl, fun _ => by positivity, ?_, ?_⟩
  · simp [Paper.CubePair.center₂]
  · rw [AffineIsometryEquiv.coe_trans, Set.image_comp, Paper.CubePair.second]
    congr 1
    ext x
    simp only [AffineIsometryEquiv.coe_constVAdd, vadd_eq_add, mem_image, mem_ofPred_eq,
      abs_nonpos_iff]
    constructor
    · rintro ⟨hx₀, hx⟩
      refine ⟨x - Pt.mk p.dist p.offset, ⟨by simp [hx₀], fun k => by simpa using hx k⟩, ?_⟩
      abel
    · rintro ⟨y, ⟨hy₀, hy⟩, rfl⟩
      exact ⟨by simp [hy₀], fun k => by simpa using hy k⟩

lemma cubePair_first_subset_face₀ : p.first ⊆ p.slab.face₀ := by
  rintro _ ⟨x, ⟨hx₀, -⟩, rfl⟩
  exact ⟨x, hx₀, rfl⟩

lemma cubePair_second_subset_face₁ : p.second ⊆ p.slab.face₁ := by
  rintro _ ⟨x, ⟨hx₀, -⟩, rfl⟩
  exact ⟨x, hx₀, rfl⟩

end CubePair

end IsotropicVariance.Paper.Proofs.Profiles
