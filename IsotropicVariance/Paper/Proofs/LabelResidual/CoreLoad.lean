/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.GoodOffsets
public import IsotropicVariance.Paper.Proofs.LabelResidual.CoreResponse
public import IsotropicVariance.Paper.Proofs.Responses.TubeLocality

/-!
# Only the core block contributes on a good old tube

The positive slab response can be nonzero only for a block containing a fine cell of the old
tube. If that whole tube lies in the core of one block, all other terms of `Y_i(j,k)` vanish.
The one remaining term is bounded by the squared normalized core response. This is the
geometric and small-change comparison in the proof of Lemma `lem:residual`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.LabelResidual

variable {m : ℕ} {X : Setting.{u} m}

/-- On an old tube contained in one offset core, the normalized load is at most the square of
the response of that core block. The comparison uses old curves only. -/
theorem ae_Y_le_coreResponse_sq {b A ℓ : ℝ} {K i : ℕ} {L : ℕ+}
    (hb : X.IsUpperBound b) (hn : 0 ≤ ℓ / K) (hW : 1 ≤ W K A (ℓ / K))
    (hQ : 0 < Q K A (ℓ / K)) (o : Fin m → Fin (L : ℕ)) (g j k : Fin m → ℤ)
    (D : ℝ) (hρ : Real.sqrt m ≤ 2 * Real.sqrt m + 2 + (W K A (ℓ / K))⁻¹ * D)
    (hcore : {y : EuclideanSpace ℝ (Fin m) |
      infDist y (segment ℝ (Responses.transverseIntegerPoint j) (Responses.transverseIntegerPoint k)) ≤
        2 * Real.sqrt m + 2 + (W K A (ℓ / K))⁻¹ * D} ⊆
      OffsetGeometry.groupCore L (Real.sqrt (L : ℕ)) o g)
    (fam : X.BlockCouplingFamily (ℓ / K) (W K A (ℓ / K)) L i {z | IsBlockIndex L o z}) :
    ∀ᵐ ω ∂fam.P',
      (∀ u ∈ gridCube (ℓ / K) (W K A (ℓ / K)) 0 i j,
        ∀ v ∈ gridCube (ℓ / K) (W K A (ℓ / K)) 0 (i + 1) k,
        ∀ γ : RectifiableCurve (Pt m),
          IsOneOptimal ((chainSlab (ℓ / K) 0 i).density b (X.ρ (fam.old ω)))
            (chainSlab (ℓ / K) 0 i).set u v γ → ∀ t ∈ Icc (0 : ℝ) 1,
              infDist (γ.toFun t) (segment ℝ u v) ≤ D) →
      X.Y b (ℓ / K) (W K A (ℓ / K)) (Q K A (ℓ / K)) i j k
        {z | IsBlockIndex L o z} fam.old fam.new ω ≤
      coreResponse b K A ℓ L i (blockLowerIndex L o g)
        (fam.old ω) (fam.new (blockLowerIndex L o g) ω) ^ 2 := by
  classical
  have hW0 : 0 < W K A (ℓ / K) := lt_of_lt_of_le zero_lt_one hW
  let I := {z : Fin m → ℤ | IsBlockIndex L o z}
  let g₀ : I := ⟨blockLowerIndex L o g, isBlockIndex_blockLowerIndex L o g⟩
  have hj := gridCube_subset_coreFace_of_tube_subset (n := ℓ / K) L o g j hW0 i _
    (left_mem_segment ℝ (Responses.transverseIntegerPoint j) (Responses.transverseIntegerPoint k)) hρ hcore
  have hk := gridCube_subset_coreFace_of_tube_subset (n := ℓ / K) L o g k hW0 (i + 1) _
    (right_mem_segment ℝ (Responses.transverseIntegerPoint j) (Responses.transverseIntegerPoint k)) hρ hcore
  have hae : ∀ᵐ ω ∂fam.P', ∀ z : I, ∀ d : ℝ,
      (∀ u ∈ gridCube (ℓ / K) (W K A (ℓ / K)) 0 i j,
        ∀ v ∈ gridCube (ℓ / K) (W K A (ℓ / K)) 0 (i + 1) k,
        ∀ γ : RectifiableCurve (Pt m),
          IsOneOptimal ((chainSlab (ℓ / K) 0 i).density b (X.ρ (fam.old ω)))
            (chainSlab (ℓ / K) 0 i).set u v γ → ∀ t ∈ Icc (0 : ℝ) 1,
              infDist (γ.toFun t) (segment ℝ u v) ≤ d) →
      X.blockGain b (ℓ / K) (W K A (ℓ / K)) i j k (fam.old ω) (fam.new z ω) ≠ 0 →
      ∃ z', Responses.cellBlockIndex L o z' = z ∧
        infDist (Responses.transverseIntegerPoint z')
          (segment ℝ (Responses.transverseIntegerPoint j) (Responses.transverseIntegerPoint k)) ≤
            2 * Real.sqrt m + 2 + (W K A (ℓ / K))⁻¹ * d :=
    ae_all_iff.mpr fun z => Responses.IsBlockCoupling.ae_exists_cell_of_blockGain_ne_zero
      hb hn hW L.pos o i j k z z.2 (fam.isBlockCoupling z z.2)
  filter_upwards [hae] with ω hω hcurve
  have hzero (z : I) (hz : z ≠ g₀) :
      X.blockGain b (ℓ / K) (W K A (ℓ / K)) i j k (fam.old ω) (fam.new z ω) = 0 := by
    by_contra hgain
    obtain ⟨z',hzz',hd⟩ := hω z D hcurve hgain
    have hi := cellBlockIndex_eq_of_mem_groupCore L o g z' (hcore hd)
    exact hz (Subtype.ext (hzz'.symm.trans hi))
  unfold Setting.Y
  split_ifs with hret
  · rw [tsum_eq_single g₀ (fun z hz => by
      rw [hzero z hz, zero_div, zero_pow (by norm_num : 2 ≠ 0), ENNReal.ofReal_zero])]
    rw [ENNReal.ofReal_pow
      (div_nonneg (Responses.blockGain_nonneg X b (ℓ / K) (W K A (ℓ / K)) i j k _ _) hQ.le) 2]
    exact pow_le_pow_left' (ofReal_blockGain_div_le_coreResponse hQ hj hk _ _) 2
  · exact bot_le

end IsotropicVariance.Paper.Proofs.LabelResidual
