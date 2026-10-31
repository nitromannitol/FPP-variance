/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.TubeLocality
public import IsotropicVariance.Infra.Measurability.MinimizerMeasurable
import Mathlib.Tactic.Linarith

/-!
# A replacement affects only its own slab passage time

The unit boundary buffers separate the passage-time density in a slab from the blocks of all
other slabs, as used in the competitor step of the proof of Lemma `lem:blocks`.
-/

@[expose] public section

open MeasureTheory Set Metric

namespace IsotropicVariance.Paper.Proofs.Responses

open Infra.Slab

variable {m : ℕ}

lemma infDist_block_gt_one_of_other_slab {s W : ℝ} (hs : 0 ≤ s) (hW : 0 < W)
    {L : ℕ} (hL : 1 ≤ L) {r i : ℕ} (hri : r ≠ i) (g : Fin m → ℤ) {x : Pt m}
    (hx : x ∈ (chainSlab s 0 r).set) (hface : 1 < infDist x (chainSlab s 0 r).faces) :
    1 < infDist x (block s W L i g) := by
  have hx' := (mem_chainSlab_set.mp hx)
  simp only [Pt.lon_zero, zero_add] at hx'
  have hfoot (c : ℝ) (hc : c = (r : ℝ) * s ∨ c = (r : ℝ) * s + s) :
      1 < |Pt.lon x - c| := by
    let y := Pt.mk c (Pt.tr x)
    have hy : y ∈ (chainSlab s 0 r).faces := by
      rw [mem_slab_faces_iff, slabCoord_chainSlab]
      change c - (0 + (r : ℝ) * s) = 0 ∨ c - (0 + (r : ℝ) * s) = s
      rcases hc with rfl | rfl <;> simp
    have hd : dist x y = |Pt.lon x - c| := dist_eq_abs_lon_sub rfl
    exact hface.trans_le ((infDist_le_dist_of_mem hy).trans_eq hd)
  rcases lt_or_gt_of_ne hri with hri | hri
  · have hgap := hfoot ((r : ℝ) * s + s) (Or.inr rfl)
    rw [abs_of_nonpos (by linarith only [hx'.2])] at hgap
    apply hgap.trans_le
    apply (le_infDist (block_nonempty hs hW hL i g)).mpr
    intro y hy
    have hidx : (r : ℝ) + 1 ≤ i := by exact_mod_cast hri
    have hy' := hy.1
    have hlo0 : (r : ℝ) * s + s ≤ (i : ℝ) * s := by
      nlinarith only [mul_le_mul_of_nonneg_right hidx hs]
    have hlo : (r : ℝ) * s + s ≤ Pt.lon y := hlo0.trans hy'
    have hd := Infra.Slab.abs_lon_sub_le x y
    rw [abs_of_nonpos (by linarith only [hlo, hx'.2])] at hd
    linarith only [hd, hlo]
  · have hgap := hfoot ((r : ℝ) * s) (Or.inl rfl)
    rw [abs_of_nonneg (by linarith only [hx'.1])] at hgap
    apply hgap.trans_le
    apply (le_infDist (block_nonempty hs hW hL i g)).mpr
    intro y hy
    have hidx : (i : ℝ) + 1 ≤ r := by exact_mod_cast hri
    have hy' := hy.2.1
    have hhi : Pt.lon y ≤ (r : ℝ) * s := hy'.trans
      (by nlinarith only [mul_le_mul_of_nonneg_right hidx hs])
    have hd := Infra.Slab.abs_lon_sub_le x y
    rw [abs_of_nonneg (by linarith only [hhi, hx'.1])] at hd
    linarith only [hd, hhi]

/-- All slab passage times other than that of the replaced block agree, simultaneously. -/
theorem IsBlockCoupling.ae_other_slabTime_eq {X : Setting m} (b : ℝ) {s W : ℝ}
    (hs : 0 ≤ s) (hW : 0 < W) {L : ℕ} (hL : 1 ≤ L) (i : ℕ) (g : Fin m → ℤ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (hcpl : X.IsBlockCoupling (block s W L i g) P' old new) :
    ∀ᵐ ω ∂P', ∀ r : ℕ, r ≠ i → ∀ u v : Pt m,
      X.slabTime b (chainSlab s 0 r) (new ω) u v =
        X.slabTime b (chainSlab s 0 r) (old ω) u v := by
  filter_upwards [Gain.IsBlockCoupling.ae_slabTime_eq b hcpl] with ω hω r hri u v
  exact (hω (chainSlab s 0 r)
    (fun x hx hf => infDist_block_gt_one_of_other_slab hs hW hL hri g hx hf) u v).symm

end IsotropicVariance.Paper.Proofs.Responses
