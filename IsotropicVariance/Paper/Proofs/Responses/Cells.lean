/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Blocks
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fine cells in a block partition

The cell assignment and summation step of the proof of Lemma `lem:blocks`. The indices here are
the lower corners in the definition `IsBlockIndex`.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

variable {m : ℕ}

/-- The lower corner of the unique block containing the integer cell `z`. -/
def cellBlockIndex (L : ℕ) (o : Fin m → Fin L) (z : Fin m → ℤ) : Fin m → ℤ :=
  fun k => z k - (z k - (o k : ℕ)) % (L : ℤ)

lemma isBlockIndex_cellBlockIndex (L : ℕ) (o : Fin m → Fin L) (z : Fin m → ℤ) :
    IsBlockIndex L o (cellBlockIndex L o z) := by
  intro k
  have h : cellBlockIndex L o z k - (o k : ℕ) =
      (z k - (o k : ℕ)) - (z k - (o k : ℕ)) % (L : ℤ) := by
    dsimp [cellBlockIndex]
    ring
  rw [h]
  exact Int.dvd_self_sub_emod

lemma cellBlockIndex_eq {L : ℕ} (hL : 1 ≤ L) (o : Fin m → Fin L)
    {z g : Fin m → ℤ} (hg : IsBlockIndex L o g)
    (hz : ∀ k, g k ≤ z k ∧ z k < g k + L) : cellBlockIndex L o z = g := by
  have hL0 : (0 : ℤ) < L := by exact_mod_cast hL
  funext k
  have heq : z k - (o k : ℕ) = (z k - g k) + (g k - (o k : ℕ)) := by ring
  have hmod : (z k - g k) % (L : ℤ) = z k - g k :=
    Int.emod_eq_of_lt (by linarith [(hz k).1]) (by linarith [(hz k).2])
  simp only [cellBlockIndex, heq, Int.add_emod, Int.emod_eq_zero_of_dvd (hg k),
    add_zero, hmod]
  ring

/-- The fine cell of a point in a block has that block's lower corner. -/
lemma cellBlockIndex_floor_eq {n W : ℝ} (hW : 0 < W) {L : ℕ} (hL : 1 ≤ L)
    (o : Fin m → Fin L) {i : ℕ} {g : Fin m → ℤ} (hg : IsBlockIndex L o g)
    {x : Pt m} (hx : x ∈ block n W L i g) :
    cellBlockIndex L o (fun k => ⌊Pt.tr x k / W⌋) = g := by
  apply cellBlockIndex_eq hL o hg
  intro k
  constructor
  · apply Int.le_floor.mpr
    exact (le_div_iff₀ hW).mpr (by simpa only [mul_comm] using (hx.2.2 k).1)
  · apply Int.floor_lt.mpr
    exact (div_lt_iff₀ hW).mpr (by simpa only [Int.cast_add, Int.cast_natCast, mul_comm]
      using (hx.2.2 k).2)

/-- A sum over contributing blocks is at most the sum over their contributing fine cells. -/
theorem tsum_blocks_le_tsum_cells {L : ℕ} (o : Fin m → Fin L)
    (T : Set (Fin m → ℤ)) (V : {g : Fin m → ℤ | IsBlockIndex L o g} → ℝ≥0∞)
    (h : ∀ g, V g ≠ 0 → ∃ z ∈ T, cellBlockIndex L o z = g) :
    ∑' g, V g ≤ ∑' z : Fin m → ℤ, T.indicator (fun z =>
      V ⟨cellBlockIndex L o z, isBlockIndex_cellBlockIndex L o z⟩) z := by
  classical
  let F : (Fin m → ℤ) → ℝ≥0∞ := T.indicator fun z =>
    V ⟨cellBlockIndex L o z, isBlockIndex_cellBlockIndex L o z⟩
  calc
    _ ≤ ∑' g : {g : Fin m → ℤ | IsBlockIndex L o g}, ∑' z : Fin m → ℤ,
        if cellBlockIndex L o z = g then F z else 0 := by
      apply ENNReal.tsum_le_tsum
      intro g
      by_cases hg : V g = 0
      · rw [hg]
        exact bot_le
      · obtain ⟨z, hz, hzg⟩ := h g hg
        apply le_trans _ (ENNReal.le_tsum z)
        simp only [hzg, ↓reduceIte, F, indicator_of_mem hz, le_refl]
    _ = ∑' z : Fin m → ℤ, ∑' g : {g : Fin m → ℤ | IsBlockIndex L o g},
        if cellBlockIndex L o z = g then F z else 0 := ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro z
      have heq : ∀ g : {g : Fin m → ℤ | IsBlockIndex L o g},
          (cellBlockIndex L o z = g) ↔
            (⟨cellBlockIndex L o z, isBlockIndex_cellBlockIndex L o z⟩ :
              {g : Fin m → ℤ | IsBlockIndex L o g}) = g := fun g => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      simp_rw [heq]
      simp [F]

end IsotropicVariance.Paper.Proofs.Responses
