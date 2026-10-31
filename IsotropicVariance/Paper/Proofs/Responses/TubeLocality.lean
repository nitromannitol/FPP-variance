/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.TubeGeometry
public import IsotropicVariance.Paper.Proofs.Responses.ProfileResponse
public import IsotropicVariance.Paper.Proofs.Responses.Locality
import Mathlib.Tactic.Linarith
import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry

/-!
# Every positive block response has a cell in the old tube

The locality-to-cell step of the proof of Lemma `lem:blocks`. The block is
half-open; a point at distance less than two is enough, so distance attainment is unnecessary.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

open Infra.Slab

variable {m : ℕ}

lemma block_nonempty {s W : ℝ} (hs : 0 ≤ s) (hW : 0 < W) {L : ℕ} (hL : 1 ≤ L)
    (i : ℕ) (g : Fin m → ℤ) : (block s W L i g).Nonempty := by
  refine ⟨Pt.mk ((i : ℝ) * s) (W • transverseIntegerPoint g), ?_⟩
  change (i : ℝ) * s ≤ (i : ℝ) * s ∧ (i : ℝ) * s ≤ ((i : ℝ) + 1) * s ∧
    ∀ k, W * (g k : ℝ) ≤ W * (g k : ℝ) ∧ W * (g k : ℝ) < W * ((g k : ℝ) + L)
  refine ⟨le_rfl, by nlinarith only [hs], fun k => ⟨le_rfl, ?_⟩⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  nlinarith only [mul_pos hW hL0]

/-- A nonzero block gain forces a fine cell of that block into the tube of the old curves. -/
theorem IsBlockCoupling.ae_exists_cell_of_blockGain_ne_zero {X : Setting m} {b : ℝ}
    (hb : X.IsUpperBound b) {s W : ℝ} (hs : 0 ≤ s) (hW : 1 ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (o : Fin m → Fin L) (i : ℕ) (j k g : Fin m → ℤ) (hg : IsBlockIndex L o g)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (hcpl : X.IsBlockCoupling (block s W L i g) P' old new) :
    ∀ᵐ ω ∂P', ∀ D : ℝ,
      (∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 (i + 1) k,
        ∀ γ : RectifiableCurve (Pt m),
          IsOneOptimal ((chainSlab s 0 i).density b (X.ρ (old ω))) (chainSlab s 0 i).set u v γ →
          ∀ t ∈ Icc (0 : ℝ) 1, infDist (γ.toFun t) (segment ℝ u v) ≤ D) →
      X.blockGain b s W i j k (old ω) (new ω) ≠ 0 →
      ∃ z : Fin m → ℤ, cellBlockIndex L o z = g ∧
        infDist (transverseIntegerPoint z)
          (segment ℝ (transverseIntegerPoint j) (transverseIntegerPoint k)) ≤
            2 * Real.sqrt m + 2 + W⁻¹ * D := by
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one hW
  filter_upwards [IsBlockCoupling.ae_slabTime_le_of_oneOptimal_far hcpl hb
    (chainSlab s 0 i) (convex_slab_set _)] with ω hω D hcurve hgain
  by_contra hnone
  have hfar (u : Pt m) (hu : u ∈ gridCube s W 0 i j) (v : Pt m)
      (hv : v ∈ gridCube s W 0 (i + 1) k) (γ : RectifiableCurve (Pt m))
      (hγ : IsOneOptimal ((chainSlab s 0 i).density b (X.ρ (old ω)))
        (chainSlab s 0 i).set u v γ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      1 < infDist (γ.toFun t) (block s W L i g) := by
    by_contra hdist
    have hdist' : infDist (γ.toFun t) (block s W L i g) < 2 :=
      lt_of_le_of_lt (not_lt.mp hdist) (by norm_num)
    obtain ⟨y, hy, hnear⟩ := (infDist_lt_iff (block_nonempty hs hW0 hL i g)).mp hdist'
    apply hnone
    refine ⟨fun l => ⌊Pt.tr y l / W⌋, cellBlockIndex_floor_eq hW0 hL o hg hy, ?_⟩
    exact infDist_floor_near_segment_le hW hu hv (by rw [dist_comm]; exact hnear.le)
      (hcurve u hu v hv γ hγ t ht)
  have hzero : X.blockGain b s W i j k (old ω) (new ω) ≤ 0 := by
    refine Real.iSup_le (fun u => Real.iSup_le (fun v => ?_) le_rfl) le_rfl
    apply max_le _ le_rfl
    exact sub_nonpos.mpr (hω u (SmallMean.gridCube_subset_set hs _ i j u.2)
      v (SmallMean.gridCube_succ_subset_set hs _ i k v.2) (hfar u u.2 v v.2))
  exact hgain (le_antisymm hzero (blockGain_nonneg X b s W i j k _ _))

end IsotropicVariance.Paper.Proofs.Responses
