/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.FiniteMesh
import IsotropicVariance.Paper.Proofs.Profiles.Basic
import Mathlib.Tactic.Linarith

/-!
# A polynomial finite net on a sphere

Select a sphere point from each unit grid cell that meets the sphere. The resulting
points lie exactly on the sphere and give a net of spacing two, with the containing
cube's polynomial cardinality. This is the sphere net of the proof of [HN, Lemma 4.1], which the
proof of Lemma `lem:classical` cites, with mesh `2` in place of `L^γ`
because the density is bounded.
-/

@[expose] public section

open Set Metric

namespace IsotropicVariance.Paper.Proofs.Classical

open IsotropicVariance.Paper

/-- A sphere of radius at least one has a finite two-net of polynomial cardinality,
whose points all lie on the sphere itself. -/
theorem exists_sphere_net {m : ℕ} {s : ℝ} (hs : 1 ≤ s) :
    ∃ H : Finset (Pt m), H.Nonempty ∧
      H.card ≤ ⌈(m + 1 : ℝ) * s⌉₊ ^ (m + 1) ∧
      (∀ q ∈ H, ‖q‖ = s) ∧ ∀ z : Pt m, ‖z‖ = s → ∃ q ∈ H, dist z q ≤ 2 := by
  classical
  obtain ⟨G, _hG, hcard, _hGcube, hcover⟩ := SlabComparison.exists_unit_mesh (m := m) 0 hs
  let J := G.filter (fun c => ∃ z : Pt m, ‖z‖ = s ∧ dist z c ≤ 1)
  have hex (c : {c // c ∈ J}) : ∃ z : Pt m, ‖z‖ = s ∧ dist z c ≤ 1 :=
    (Finset.mem_filter.mp c.2).2
  let pick : {c // c ∈ J} → Pt m := fun c => (hex c).choose
  let H := J.attach.image pick
  have hHcard : H.card ≤ ⌈(m + 1 : ℝ) * s⌉₊ ^ (m + 1) :=
    (Finset.card_image_le.trans (by rw [Finset.card_attach]; exact Finset.card_filter_le G _)).trans hcard
  have hHsphere : ∀ q ∈ H, ‖q‖ = s := by
    intro q hq
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hex c).choose_spec.1
  have hHcover : ∀ z : Pt m, ‖z‖ = s → ∃ q ∈ H, dist z q ≤ 2 := by
    intro z hz
    have hzcube : z ∈ cubeAround 0 s := by
      intro k
      rw [sub_zero]
      refine Fin.cases ?_ (fun j => ?_) k
      · exact (Profiles.abs_lon_le_norm z).trans_eq hz
      · exact (Profiles.abs_tr_apply_le_norm z j).trans_eq hz
    obtain ⟨c, hc, hzc⟩ := hcover z hzcube
    have hcJ : c ∈ J := Finset.mem_filter.mpr ⟨hc, z, hz, hzc⟩
    let cJ : {c // c ∈ J} := ⟨c, hcJ⟩
    refine ⟨pick cJ, Finset.mem_image.mpr ⟨cJ, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have hp := (hex cJ).choose_spec.2
    have hh := dist_triangle z c (pick cJ)
    rw [dist_comm c (pick cJ)] at hh
    linarith only [hh, hzc, hp]
  have hz : ‖s • (e₁ : Pt m)‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans hs),
      Paper.norm_e₁, mul_one]
  obtain ⟨q, hq, _⟩ := hHcover _ hz
  exact ⟨H, ⟨q, hq⟩, hHcard, hHsphere, hHcover⟩

end IsotropicVariance.Paper.Proofs.Classical
