/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.Restricted
public import IsotropicVariance.Infra.Measurability.SlabTime
import Mathlib.Tactic.Positivity

/-! # The deterministic small-width slab comparison -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.SlabComparison
variable {m : ℕ}

lemma face₀_subset_slab (sl : Slab m) (hw : 0 ≤ sl.width) : sl.face₀ ⊆ sl.set := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, by simp only [mem_ofPred_eq] at hx ⊢; exact ⟨hx.symm.le, hx ▸ hw⟩, rfl⟩

lemma face₁_subset_slab (sl : Slab m) (hw : 0 ≤ sl.width) : sl.face₁ ⊆ sl.set := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, by simp only [mem_ofPred_eq] at hx ⊢; exact ⟨hx ▸ hw, hx.le⟩, rfl⟩

lemma le_slabDensity (sl : Slab m) (σ : Pt m → ℝ) {b : ℝ} (hb : ∀ x, σ x ≤ b) (x : Pt m) :
    σ x ≤ sl.density b σ x := by
  unfold Slab.density
  split_ifs
  · exact hb x
  · exact le_rfl

lemma slabDensity_le (sl : Slab m) (σ : Pt m → ℝ) {b : ℝ} (hb : ∀ x, σ x ≤ b) (x : Pt m) :
    sl.density b σ x ≤ b := by
  unfold Slab.density
  split_ifs
  · exact le_rfl
  · exact hb x

lemma passageTime_le_slabTime (sl : Slab m) (hw : 0 ≤ sl.width) (σ : Pt m → ℝ)
    {b : ℝ} (hb : ∀ x, σ x ≤ b) {x y : Pt m} (hx : x ∈ sl.face₀) (hy : y ∈ sl.face₁) :
    IsotropicVariance.passageTime σ x y ≤ sl.passTime b σ x y :=
  passageTime_le_restrictedPassageTime (Infra.Slab.convex_slab_set sl) σ (sl.density b σ)
    (le_slabDensity sl σ hb) (slabDensity_le sl σ hb)
    (face₀_subset_slab sl hw hx) (face₁_subset_slab sl hw hy)

lemma slabTime_le_mul_dist (sl : Slab m) (hw : 0 ≤ sl.width) (σ : Pt m → ℝ)
    {b : ℝ} (hb : ∀ x, σ x ≤ b) (hb0 : 0 ≤ b) {x y : Pt m}
    (hx : x ∈ sl.face₀) (hy : y ∈ sl.face₁) :
    sl.passTime b σ x y ≤ b * dist x y :=
  restrictedPassageTime_le_dist (Infra.Slab.convex_slab_set sl) (sl.density b σ)
    (slabDensity_le sl σ hb) hb0
    (face₀_subset_slab sl hw hx) (face₁_subset_slab sl hw hy)

lemma dist_le_three_mul_width (sl : Slab m) (hw : 0 < sl.width) {x y : Pt m}
    (hs : sl.slope x y ≤ 2) : dist x y ≤ 3 * sl.width := by
  have hsqrt : Real.sqrt (dist x y ^ 2 - sl.width ^ 2) ≤ 2 * sl.width :=
    (div_le_iff₀ hw).mp hs
  by_cases h : 0 ≤ dist x y ^ 2 - sl.width ^ 2
  · nlinarith [Real.sq_sqrt h, Real.sqrt_nonneg (dist x y ^ 2 - sl.width ^ 2), dist_nonneg (x := x) (y := y)]
  · nlinarith [dist_nonneg (x := x) (y := y)]

end IsotropicVariance.Paper.Proofs.SlabComparison
