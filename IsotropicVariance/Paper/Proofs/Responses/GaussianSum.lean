/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Blocks
public import IsotropicVariance.Paper.Proofs.Localization.Os
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Int.Order.Lemmas

/-!
# Gaussian sums on the transverse integer lattice

The Gaussian cell weights in the proof of Lemma `lem:blocks` are summable. The bound is obtained
from the finite-box estimate `Localization.sum_exp_neg_sq_le` by increasing the box; it is
independent of its location.
-/

@[expose] public section

open Set Finset MeasureTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

/-- The integer transverse vector regarded as a Euclidean vector. -/
def transverseIntegerPoint {m : ℕ} (z : Fin m → ℤ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => (z i : ℝ)

lemma norm_transverseIntegerPoint {m : ℕ} (z : Fin m → ℤ) :
    ‖transverseIntegerPoint z‖ = zNorm z := by
  rw [EuclideanSpace.norm_eq]
  simp only [transverseIntegerPoint, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, zNorm]

lemma transverseIntegerPoint_sub {m : ℕ} (z q : Fin m → ℤ) :
    transverseIntegerPoint (z - q) = transverseIntegerPoint z - transverseIntegerPoint q := by
  ext i
  simp only [transverseIntegerPoint, Pi.sub_apply, Int.cast_sub, PiLp.sub_apply,
    PiLp.toLp_apply]

/-- The transverse Gaussian lattice sum is bounded independently of a finite cutoff. -/
theorem tsum_exp_neg_sq_le {c : ℝ} (hc : 0 < c) (m : ℕ) :
    (∑' z : Fin m → ℤ, ENNReal.ofReal (Real.exp (-c * ∑ i, ((z i : ℝ)) ^ 2))) ≤
      ENNReal.ofReal ((2 / (1 - Real.exp (-c))) ^ m) := by
  classical
  apply ENNReal.summable.tsum_le_of_sum_le
  intro T
  let M : ℕ := T.sup fun z => Finset.univ.sup fun i : Fin m => (z i).natAbs
  have hM (z : Fin m → ℤ) (hz : z ∈ T) (i : Fin m) : (z i).natAbs ≤ M :=
    (Finset.le_sup (f := fun i : Fin m => (z i).natAbs) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun z => Finset.univ.sup fun i : Fin m => (z i).natAbs) hz)
  have hsub : T ⊆ Fintype.piFinset (fun _ : Fin m => Finset.Icc (-(M : ℤ)) M) := by
    intro z hz
    simp only [Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h := hM z hz i
    have h1 := (Int.le_natAbs (a := z i))
    have h2 := Int.le_natAbs (a := -(z i))
    rw [Int.natAbs_neg] at h2
    constructor <;> omega
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (Real.exp_pos _).le)).trans
    (Localization.sum_exp_neg_sq_le hc m M)

end IsotropicVariance.Paper.Proofs.Responses
