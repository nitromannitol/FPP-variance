/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.IndexTubes
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-!
# Counting lattice points in a segment tube

Unit-spaced samples of a segment and coordinate boxes around those samples
give an explicit dimension-dependent bound.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Responses.Geometry

/-- A segment admits at most `length + 2` unit-net samples. -/
theorem segment_unit_net {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (p q : V) :
    ∃ N : ℕ, (N + 1 : ℝ) ≤ ‖q - p‖ + 2 ∧
      ∀ z ∈ segment ℝ p q, ∃ n ∈ Finset.range (N + 1),
        dist z (p + ((n : ℝ) / N) • (q - p)) ≤ 1 := by
  let N : ℕ := ⌊‖q - p‖⌋₊ + 1
  have hN : 0 < (N : ℝ) := by dsimp only [N]; positivity
  have hNd : ‖q - p‖ < (N : ℝ) := by simpa only [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ‖q - p‖
  have hNl : (N : ℝ) ≤ ‖q - p‖ + 1 := by
    dsimp only [N]
    push_cast
    linarith only [Nat.floor_le (norm_nonneg (q - p))]
  refine ⟨N, by linarith only [hNl], ?_⟩
  intro z hz
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  let n : ℕ := ⌊b * N⌋₊
  have hbn : 0 ≤ b * (N : ℝ) := mul_nonneg hb hN.le
  have hnlo : (n : ℝ) ≤ b * N := Nat.floor_le hbn
  have hnhi : b * (N : ℝ) < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnN : n ≤ N := by
    apply (Nat.cast_le (α := ℝ)).mp
    have hb1 : b ≤ 1 := by linarith only [ha, hab]
    exact hnlo.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb1 hN.le)
  refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hnN), ?_⟩
  have heq : a • p + b • q - (p + ((n : ℝ) / N) • (q - p)) =
      (b - (n : ℝ) / N) • (q - p) := by
    have haeq : a = 1 - b := by linarith only [hab]
    rw [haeq]
    module
  have hd0 : 0 ≤ b - (n : ℝ) / N := by
    have h := (div_le_iff₀ hN).mpr hnlo
    linarith only [h]
  have hd1 : (b - (n : ℝ) / N) * N ≤ 1 := by
    have hid : (b - (n : ℝ) / N) * N = b * N - n := by field_simp
    rw [hid]
    linarith only [hnhi]
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd0]
  exact (mul_le_mul_of_nonneg_left hNd.le hd0).trans hd1

/-- An integer coordinate box containing the Euclidean ball with center c and radius r. -/
noncomputable def latticeBox {m : ℕ} (c : EuclideanSpace ℝ (Fin m)) (r : ℝ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc ⌊c i - r⌋ ⌊c i + r⌋)

/-- A Euclidean ball lies in the corresponding integer coordinate box. -/
theorem mem_latticeBox_of_dist_le {m : ℕ} (c : EuclideanSpace ℝ (Fin m)) {r : ℝ}
    {j : Fin m → ℤ} (hj : dist (indexPoint j) c ≤ r) : j ∈ latticeBox c r := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hcoord : |(j i : ℝ) - c i| ≤ r :=
    (PiLp.norm_apply_le (indexPoint j - c) i).trans (by simpa only [dist_eq_norm] using hj)
  have hbounds := abs_le.mp hcoord
  apply Finset.mem_Icc.mpr
  constructor
  · have h : (⌊c i - r⌋ : ℝ) ≤ (j i : ℝ) :=
      (Int.floor_le (c i - r)).trans (by linarith only [hbounds.1])
    exact Int.cast_le.mp h
  · apply Int.le_floor.mpr
    linarith only [hbounds.2]

/-- A radius-r Euclidean ball meets at most `(2r+3)^m` integer points. -/
theorem card_latticeBox_le {m : ℕ} (c : EuclideanSpace ℝ (Fin m)) {r : ℝ} (hr : 0 ≤ r) :
    ((latticeBox c r).card : ℝ) ≤ (2 * r + 3) ^ m := by
  classical
  have hcoord (i : Fin m) : ((Finset.Icc ⌊c i - r⌋ ⌊c i + r⌋).card : ℝ) ≤ 2 * r + 3 := by
    have hmono' : ⌊c i - r⌋ ≤ ⌊c i + r⌋ :=
      Int.floor_mono (by linarith only [hr] : c i - r ≤ c i + r)
    have hmono : ⌊c i - r⌋ ≤ ⌊c i + r⌋ + 1 := by omega
    have hcard : ((Finset.Icc ⌊c i - r⌋ ⌊c i + r⌋).card : ℝ) =
        (⌊c i + r⌋ : ℝ) + 1 - (⌊c i - r⌋ : ℝ) := by
      exact_mod_cast Int.card_Icc_of_le ⌊c i - r⌋ ⌊c i + r⌋ hmono
    rw [hcard]
    linarith only [Int.floor_le (c i + r), Int.lt_floor_add_one (c i - r)]
  rw [latticeBox, Fintype.card_piFinset, Nat.cast_prod]
  calc
    _ ≤ ∏ _i : Fin m, (2 * r + 3) := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hcoord i)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Explicit tube bound with `C_m = 2 * 5^m`, uniformly in both endpoints and radius. -/
theorem card_indexTube_le {m : ℕ} (j k : Fin m → ℤ) {R : ℝ} (hR : 0 ≤ R) :
    (((indexTube_finite j k R).toFinset).card : ℝ) ≤
      (2 * (5 : ℝ) ^ m) * (1 + ‖indexPoint j - indexPoint k‖) * (1 + R) ^ m := by
  classical
  obtain ⟨N, hN, hnet⟩ := segment_unit_net (indexPoint j) (indexPoint k)
  let B : ℕ → Finset (Fin m → ℤ) := fun n => latticeBox
    (indexPoint j + ((n : ℝ) / N) • (indexPoint k - indexPoint j)) (R + 1)
  have hsub : (indexTube_finite j k R).toFinset ⊆ (Finset.range (N + 1)).biUnion B := by
    intro l hl
    obtain ⟨z, hz, hdist⟩ := (mem_indexTube_iff j k l R).mp ((Set.Finite.mem_toFinset _).mp hl)
    obtain ⟨n, hn, hdn⟩ := hnet z hz
    apply Finset.mem_biUnion.mpr
    refine ⟨n, hn, mem_latticeBox_of_dist_le _ ?_⟩
    exact (dist_triangle (indexPoint l) z _).trans (add_le_add hdist hdn)
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hbox (n : ℕ) : ((B n).card : ℝ) ≤ (2 * R + 5) ^ m := by
    simpa only [show 2 * (R + 1) + 3 = 2 * R + 5 by ring] using
      card_latticeBox_le (indexPoint j + ((n : ℝ) / N) • (indexPoint k - indexPoint j))
        (by linarith only [hR] : 0 ≤ R + 1)
  have hrad : (2 * R + 5) ^ m ≤ (5 : ℝ) ^ m * (1 + R) ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hR]) m
  have hlength : (N + 1 : ℝ) ≤ 2 * (1 + ‖indexPoint j - indexPoint k‖) := by
    rw [norm_sub_rev] at hN
    linarith only [hN, norm_nonneg (indexPoint j - indexPoint k)]
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), ((B n).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _n ∈ Finset.range (N + 1), (2 * R + 5) ^ m :=
      Finset.sum_le_sum (fun n _ => hbox n)
    _ = (N + 1 : ℝ) * (2 * R + 5) ^ m := by simp
    _ ≤ (2 * (1 + ‖indexPoint j - indexPoint k‖)) *
        ((5 : ℝ) ^ m * (1 + R) ^ m) := mul_le_mul hlength hrad (by positivity) (by positivity)
    _ = _ := by ring

end CurvatureVariance.Paper.Responses.Geometry
