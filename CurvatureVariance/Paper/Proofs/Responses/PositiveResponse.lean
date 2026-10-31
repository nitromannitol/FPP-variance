/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.Finiteness
public import CurvatureVariance.Paper.Proofs.Responses.Exchange

/-!
# Positive response of the exact target minimum

The pointwise comparison behind equation `eq:blocksum`: after resampling a block, the old
minimizing tuple is still admissible, and every term outside that block's slab is unchanged. The
squared positive response is bounded by the supremum of squared positive slab responses between
the two row cubes. This holds for every minimizing tuple, without a selection convention.
-/

@[expose] public section

open Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- Replacing a block raises the minimum by at most the change of its slab distance evaluated
at the two vertices of any old minimizing tuple. -/
theorem targetMin_resample_sub_le {M : Model m} {n K ℓ w L : ℕ} (hn : 2 ≤ n)
    {y o g : Fin m → ℤ} {ω ω' : Config m} {Y : Fin (K + 1) → Fin m → ℤ}
    (hY : IsMinTuple M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y) (i : Fin K) :
    targetMin M (resample (block n w L (targetSlope ℓ y) (i + 1) o g) ω ω') n K ℓ y -
        targetMin M ω n K ℓ y ≤
      slabTimeReal (resample (block n w L (targetSlope ℓ y) (i + 1) o g) ω ω')
          ((i : ℤ) * n) (((i : ℤ) + 1) * n)
          (tuplePoint 0 n Y i.castSucc) (tuplePoint 0 n Y i.succ) -
        slabTimeReal ω ((i : ℤ) * n) (((i : ℤ) + 1) * n)
          (tuplePoint 0 n Y i.castSucc) (tuplePoint 0 n Y i.succ) := by
  have h := slabMin_sub_le_slabTime_sub
    (ω' := resample (block n w L (targetSlope ℓ y) (i + 1) o g) ω ω') hY
    (fun j => tuple_slabTime_ne_top _ 0 hn Y j)
    (fun j => tuple_slabTime_ne_top _ 0 hn Y j) i (by
      intro j hj
      simp only [Prod.fst_zero, zero_add]
      exact slabTime_resample_block_eq _ _ n w L (targetSlope ℓ y) o g
        (fun h => hj (Fin.ext h.symm)) _ _)
  simpa only [targetMin, Prod.fst_zero, zero_add] using h

/-- Squared positive response, bounded by the responses over the two row cubes containing the
old tuple's adjacent vertices. This is the pointwise step behind equation `eq:blocksum`. -/
theorem ofReal_posPart_sq_targetMin_resample_le {M : Model m} {n K ℓ w L : ℕ}
    (hn : 2 ≤ n) {y o g : Fin m → ℤ} {ω ω' : Config m}
    {Y : Fin (K + 1) → Fin m → ℤ}
    (hY : IsMinTuple M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y) (i : Fin K) :
    ENNReal.ofReal (max
      (targetMin M (resample (block n w L (targetSlope ℓ y) (i + 1) o g) ω ω') n K ℓ y -
        targetMin M ω n K ℓ y) 0 ^ 2) ≤
    ⨆ (u : Vertex m)
      (_ : u ∈ rowCube n w (targetSlope ℓ y) (i : ℤ)
        (tupleIndex n w (targetSlope ℓ y) Y i.castSucc))
      (v : Vertex m)
      (_ : v ∈ rowCube n w (targetSlope ℓ y) ((i : ℤ) + 1)
        (tupleIndex n w (targetSlope ℓ y) Y i.succ)),
      ENNReal.ofReal (max
        (slabTimeReal (resample (block n w L (targetSlope ℓ y) (i + 1) o g) ω ω')
          ((i : ℤ) * n) (((i : ℤ) + 1) * n) u v -
        slabTimeReal ω ((i : ℤ) * n) (((i : ℤ) + 1) * n) u v) 0 ^ 2) := by
  have hu : tuplePoint 0 n Y i.castSucc ∈ rowCube n w (targetSlope ℓ y) (i : ℤ)
      (tupleIndex n w (targetSlope ℓ y) Y i.castSucc) := by
    constructor <;> simp only [tuplePoint, Prod.fst_zero, zero_add, Fin.val_castSucc,
      tupleIndex]
  have hv : tuplePoint 0 n Y i.succ ∈ rowCube n w (targetSlope ℓ y) ((i : ℤ) + 1)
      (tupleIndex n w (targetSlope ℓ y) Y i.succ) := by
    constructor <;> simp only [tuplePoint, Prod.fst_zero, zero_add, Fin.val_succ,
      Nat.cast_add, Nat.cast_one, tupleIndex]
  refine le_iSup₂_of_le (tuplePoint 0 n Y i.castSucc) hu
    (le_iSup₂_of_le (tuplePoint 0 n Y i.succ) hv ?_)
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (le_max_right _ _)
    (max_le_max (targetMin_resample_sub_le hn hY i) le_rfl) 2

end CurvatureVariance.Paper.Responses
