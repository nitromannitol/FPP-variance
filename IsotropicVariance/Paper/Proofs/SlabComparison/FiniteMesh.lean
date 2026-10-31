/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.TreeGeometry
import Mathlib.Algebra.Order.Floor.Semiring

/-! # A translated unit mesh with an explicit polynomial cardinality bound

The grid is the coordinate grid of `IsotropicVariance.Paper.Proofs.Profiles.TreeGeometry`. Its use
here precedes the slab comparison and depends only on deterministic geometry, so introduces no
contract cycle.
-/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

/-- Coordinate errors at most `δ` give Euclidean error at most `(m+1)δ`. -/
lemma norm_le_dim_mul {v : Pt m} {δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : |Pt.lon v| ≤ δ) (htr : ∀ k, |Pt.tr v k| ≤ δ) :
    ‖v‖ ≤ (m + 1 : ℝ) * δ := by
  have hs : ∑ k : Fin m, (Pt.tr v k) ^ 2 ≤ (m : ℝ) * δ ^ 2 := by
    calc
      _ ≤ ∑ _k : Fin m, δ ^ 2 := Finset.sum_le_sum fun k _ => by
        nlinarith [(abs_le.mp (htr k)).1, (abs_le.mp (htr k)).2]
      _ = _ := by simp
  have hsq := Profiles.norm_sq_eq_lon_tr v
  rw [EuclideanSpace.real_norm_sq_eq] at hsq
  have hl : Pt.lon v ^ 2 ≤ δ ^ 2 := by
    nlinarith [(abs_le.mp hlo).1, (abs_le.mp hlo).2]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hm1 : (m : ℝ) + 1 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hm1 (sq_nonneg δ)
  have hright : 0 ≤ (m + 1 : ℝ) * δ := by positivity
  nlinarith [norm_nonneg v]

lemma abs_cellCenter_le {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 ≤ L) (l : Fin n) :
    |Profiles.cellCenter n L l| ≤ L := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlR : (l : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt l.isLt)
  have hloR : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hdiv0 : 0 ≤ (2 * (l : ℝ) + 1) * L / n := by positivity
  have hdiv1 : (2 * (l : ℝ) + 1) * L / n ≤ 2 * L := by
    rw [div_le_iff₀ hnR]
    nlinarith
  rw [Profiles.cellCenter, abs_le]
  constructor <;> linarith

/-- A unit mesh of a translated cube, with at most `ceil((m+1)L)^(m+1)` points. -/
theorem exists_unit_mesh (z : Pt m) {L : ℝ} (hL : 1 ≤ L) :
    ∃ G : Finset (Pt m), G.Nonempty ∧
      G.card ≤ ⌈(m + 1 : ℝ) * L⌉₊ ^ (m + 1) ∧
      (∀ c ∈ G, c ∈ cubeAround z L) ∧
      ∀ x ∈ cubeAround z L, ∃ c ∈ G, dist x c ≤ 1 := by
  classical
  let n := ⌈(m + 1 : ℝ) * L⌉₊
  have hd : (0 : ℝ) < m + 1 := by positivity
  have hn0 : 0 < n := Nat.ceil_pos.mpr (mul_pos hd (by linarith))
  have hn : (m + 1 : ℝ) * L ≤ n := Nat.le_ceil _
  let H := Profiles.grid (m := m) n L (fun _ => L)
  let G := H.image (fun c => z + c)
  have hH : H.Nonempty := by
    change (Finset.univ.image _).Nonempty
    exact Finset.Nonempty.image (by
      exact ⟨fun _ => ⟨0, hn0⟩, Finset.mem_univ _⟩) _
  refine ⟨G, hH.image _, (Finset.card_image_le).trans (Profiles.card_grid_le _ _ _), ?_, ?_⟩
  · intro c hc k
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
    have hcancel : z + Profiles.gridPt n L (fun _ => L) l - z = Profiles.gridPt n L (fun _ => L) l := by abel
    change |Pt.coords (z + Profiles.gridPt n L (fun _ => L) l - z) k| ≤ L
    rw [hcancel]
    refine Fin.cases ?_ (fun i => ?_) k
    · exact abs_cellCenter_le hn0 (by linarith) (l 0)
    · exact abs_cellCenter_le hn0 (by linarith) (l i.succ)
  · intro x hx
    have hxlo : |Pt.lon (x - z)| ≤ L := hx 0
    have hxtr : ∀ k, |Pt.tr (x - z) k| ≤ L := fun k => hx k.succ
    obtain ⟨c, hc, hlo, htr⟩ := Profiles.exists_mem_grid hn0 (by linarith) (fun _ => by linarith)
      hxlo hxtr
    refine ⟨z + c, Finset.mem_image_of_mem _ hc, ?_⟩
    have hnorm := norm_le_dim_mul (div_nonneg (by linarith) (Nat.cast_nonneg n)) hlo htr
    have hunit : (m + 1 : ℝ) * (L / n) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one (Nat.cast_pos.mpr hn0)]
      exact hn
    rw [dist_eq_norm]
    have heq : x - (z + c) = x - z - c := by abel
    rw [heq]
    exact hnorm.trans hunit

end IsotropicVariance.Paper.Proofs.SlabComparison
