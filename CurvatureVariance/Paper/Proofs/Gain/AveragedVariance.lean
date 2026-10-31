/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Proofs.Gain.AVBridge
public import CurvatureVariance.Paper.Proofs.Gain.AVResidual
public import CurvatureVariance.Paper.Proofs.Gain.L1Influence
import CurvatureVariance.Paper.Proofs.Gain.AVAlgebra
import CurvatureVariance.Paper.Proofs.Gain.AVMoments
import CurvatureVariance.Paper.Proofs.Responses.WidthBridge
import CurvatureVariance.Paper.Proofs.Geometry.SupportAngular
import CurvatureVariance.Paper.Proofs.LabelResidual.Blocks

/-!
# The averaged minimum `F̄` of Section `sec:gain`

`averagedMin_eq_of_forall_block`: the averaged minimum `F̄` is unchanged by resampling a block
when every translate of the minimum is.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper

variable {m : ℕ}

/-! ### The averaged minimum is a function of the blocks -/

/-- **`F̄` is a function of the weights of the blocks of the `K` slabs**, for any offsets. -/
theorem averagedMin_eq_of_forall_block {M : Model m} {K : ℕ} {A : ℝ} {L n ℓ : ℕ}
    {y : Fin m → ℤ} (hL : 1 ≤ L) (o : ℕ → Fin m → ℤ) {ω ω' : Config m}
    (h : ∀ e : Edge m, (∃ i < K, ∃ g, e.1 ∈ block n (wInt M K A n) L (targetSlope ℓ y) (i + 1)
      (o (i + 1)) g) → ω e = ω' e) :
    averagedMin M K A L ω n ℓ y = averagedMin M K A L ω' n ℓ y := by
  unfold averagedMin
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun v _ => ?_)
  unfold translatedMin slabMin
  refine congrArg ENNReal.toReal (iInf_congr fun Y => iInf_congr fun _ => ?_)
  unfold tupleCost
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold slabTime
  refine Responses.restrictedTime_congr _ _ _ fun e he => h e ?_
  have he' : e.1 ∈ slabEdges (((((k : ℕ) + 1 : ℕ) : ℤ) - 1) * n) ((((k : ℕ) + 1 : ℕ) : ℤ) * n) := by
    have h1 : (((((k : ℕ) + 1 : ℕ) : ℤ) - 1) * n) = (0 : ℤ) + (k : ℤ) * n := by push_cast; ring
    have h2 : ((((k : ℕ) + 1 : ℕ) : ℤ) * n) = (0 : ℤ) + ((k : ℤ) + 1) * n := by push_cast; ring
    rw [h1, h2]
    exact he
  obtain ⟨g, hg⟩ := Gain.LabelResidual.exists_mem_block (n := n) (w := wInt M K A n)
      (t := targetSlope ℓ y)
    hL (o ((k : ℕ) + 1)) he'
  exact ⟨k, k.isLt, g, hg⟩

end CurvatureVariance.Paper.Gain
