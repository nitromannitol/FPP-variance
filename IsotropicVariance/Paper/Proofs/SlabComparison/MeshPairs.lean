/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.Containment
public import IsotropicVariance.Paper.Proofs.SlabComparison.MetricScale

/-! # The finite family of long mesh pairs, with a nonempty harmless default pair -/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

/-- Add a unit pair to avoid a separate empty-maximum case. -/
noncomputable def meshPairs (z : Pt m) (G : Finset (Pt m)) : Finset (Pt m × Pt m) := by
  classical
  exact insert (z, z + e₁) ((G.product G).filter fun p => 1 ≤ dist p.1 p.2)

lemma meshPairs_nonempty (z : Pt m) (G : Finset (Pt m)) : (meshPairs z G).Nonempty := by
  classical
  exact ⟨(z, z + e₁), Finset.mem_insert_self _ _⟩

lemma card_meshPairs_le (z : Pt m) (G : Finset (Pt m)) :
    (meshPairs z G).card ≤ G.card ^ 2 + 1 := by
  classical
  apply (Finset.card_insert_le _ _).trans
  have h := Finset.card_filter_le (G.product G) (fun p : Pt m × Pt m => 1 ≤ dist p.1 p.2)
  have hprod : (G.product G).card = G.card * G.card := Finset.card_product G G
  rw [hprod] at h
  nlinarith

lemma mem_meshPairs {z u v : Pt m} {G : Finset (Pt m)}
    (hu : u ∈ G) (hv : v ∈ G) (h : 1 ≤ dist u v) : (u, v) ∈ meshPairs z G := by
  classical
  exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, h⟩)

lemma meshPairs_dist_bounds {z : Pt m} {G : Finset (Pt m)} {L : ℝ} (hL : 0 ≤ L)
    (hG : ∀ c ∈ G, c ∈ cubeAround z L) {p : Pt m × Pt m} (hp : p ∈ meshPairs z G) :
    1 ≤ dist p.1 p.2 ∧ dist p.1 p.2 ≤ 2 * (m + 1 : ℝ) * L + 1 := by
  classical
  rcases Finset.mem_insert.mp hp with rfl | hp
  · have hd : dist z (z + (e₁ : Pt m)) = 1 := by
      rw [dist_eq_norm]
      have hh : z - (z + (e₁ : Pt m)) = -e₁ := by abel
      rw [hh, norm_neg]
      exact Paper.norm_e₁
    simp only [hd, le_refl, true_and]
    have hh : 0 ≤ 2 * (m + 1 : ℝ) * L := by positivity
    linarith
  · obtain ⟨hp, hlong⟩ := Finset.mem_filter.mp hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
    refine ⟨hlong, ?_⟩
    have huD := dist_le_dim_mul_of_mem_cube hL (hG p.1 hu)
    have hvD := dist_le_dim_mul_of_mem_cube hL (hG p.2 hv)
    have htri := dist_triangle p.1 z p.2
    rw [dist_comm z p.2] at htri
    linarith

end IsotropicVariance.Paper.Proofs.SlabComparison
