/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.ProfileResponse
public import IsotropicVariance.Infra.Measurability.MinimizerMeasurable
import Mathlib.Tactic.Linarith

/-!
# Keeping the old minimizing tuple after a replacement

The deterministic competitor step at the end of the proof of Lemma `lem:blocks`.
If all other slab passage times agree, the increase of the full minimum is at most the change
in the replaced slab evaluated at the old minimizing points.
-/

@[expose] public section

open Set MeasureTheory

namespace IsotropicVariance.Paper.Proofs.Responses

variable {m : ℕ}

/-- Changing one slab can increase the minimum by at most its change on the old minimizer. -/
theorem F_sub_le_slabTime_sub (X : Setting m) {b s : ℝ} (hs : 0 ≤ s) {M : ℕ}
    (i : Fin M) (old new : X.Ω)
    (hsame : ∀ r : Fin M, r ≠ i → ∀ u v : Pt m,
      X.slabTime b (chainSlab s 0 r) new u v = X.slabTime b (chainSlab s 0 r) old u v) :
    X.F b M s 0 new - X.F b M s 0 old ≤
      X.slabTime b (chainSlab s 0 i) new
          (lexMinimizer b (X.ρ old) M s 0 i.castSucc) (lexMinimizer b (X.ρ old) M s 0 i.succ) -
        X.slabTime b (chainSlab s 0 i) old
          (lexMinimizer b (X.ρ old) M s 0 i.castSucc) (lexMinimizer b (X.ρ old) M s 0 i.succ) := by
  classical
  let x := lexMinimizer b (X.ρ old) M s 0
  have hmin := Paper.isLexLeastMinimizer_lexMinimizer b (X.isValidChain old hs) M 0
  have hnew : X.F b M s 0 new ≤ slabSum b (X.ρ new) M s 0 x := by
    apply ciInf_le (f := fun y : {y // IsAdmissible M s 0 y} => slabSum b (X.ρ new) M s 0 y)
      ⟨0, ?_⟩ ⟨x, hmin.1⟩
    rintro _ ⟨y, rfl⟩
    exact slabSum_nonneg _ _ _ _ _ _
  have hsum : slabSum b (X.ρ new) M s 0 x - slabSum b (X.ρ old) M s 0 x =
      X.slabTime b (chainSlab s 0 i) new (x i.castSucc) (x i.succ) -
        X.slabTime b (chainSlab s 0 i) old (x i.castSucc) (x i.succ) := by
    unfold slabSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single i
    · intro r _ hri
      exact sub_eq_zero.mpr (hsame r hri _ _)
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hminEq : slabSum b (X.ρ old) M s 0 x = X.F b M s 0 old := hmin.2.1
  linarith only [hnew, hsum, hminEq]

/-- Every endpoint response is bounded by the block-gain supremum. -/
lemma pos_slabTime_sub_le_blockGain (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    {s W : ℝ} (hs : 0 ≤ s) (hW : 0 ≤ W) (i : ℕ) (j k : Fin m → ℤ) (old new : X.Ω)
    {u v : Pt m} (hu : u ∈ gridCube s W 0 i j) (hv : v ∈ gridCube s W 0 (i + 1) k) :
    max (X.slabTime b (chainSlab s 0 i) new u v - X.slabTime b (chainSlab s 0 i) old u v) 0 ≤
      X.blockGain b s W i j k old new := by
  let A := slabProfile X b (Profiles.gridPair s W i j k) old +
    slabProfile X b (Profiles.gridPair s W i j k) new
  have hB : BddAbove (range fun q : gridCube s W 0 i j × gridCube s W 0 (i + 1) k =>
      max (X.slabTime b (chainSlab s 0 i) new q.1 q.2 -
        X.slabTime b (chainSlab s 0 i) old q.1 q.2) 0) := by
    refine ⟨A, ?_⟩
    rintro _ ⟨⟨u, v⟩, rfl⟩
    have ho := le_slabProfile X hb (Profiles.gridPair s W i j k) hs hW hW old
      (Profiles.gridCube_subset_first s W hW i j k u.2)
      (Profiles.gridCube_subset_second s W hW i j k v.2)
    have hn := le_slabProfile X hb (Profiles.gridPair s W i j k) hs hW hW new
      (Profiles.gridCube_subset_first s W hW i j k u.2)
      (Profiles.gridCube_subset_second s W hW i j k v.2)
    rw [Profiles.slabTime_gridPair] at ho hn
    apply max_le _ (add_nonneg (slabProfile_nonneg X b _ _) (slabProfile_nonneg X b _ _))
    linarith only [(abs_le.mp ho).1, (abs_le.mp hn).2]
  unfold Setting.blockGain
  rw [Profiles.iSup_iSup_eq_iSup_prod hB]
  exact le_ciSup hB (⟨u, hu⟩, ⟨v, hv⟩)

/-- The positive change of the minimum is bounded by the selected block gain. -/
theorem pos_F_sub_le_blockGain (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    {s W : ℝ} (hs : 0 ≤ s) (hW : 0 < W) {M : ℕ} (i : Fin M) (old new : X.Ω)
    (hsame : ∀ r : Fin M, r ≠ i → ∀ u v : Pt m,
      X.slabTime b (chainSlab s 0 r) new u v = X.slabTime b (chainSlab s 0 r) old u v) :
    max (X.F b M s 0 new - X.F b M s 0 old) 0 ≤
      X.blockGain b s W i (X.J b M s W 0 old i.castSucc) (X.J b M s W 0 old i.succ) old new := by
  apply (max_le_max_right 0 (F_sub_le_slabTime_sub X hs i old new hsame)).trans
  exact pos_slabTime_sub_le_blockGain X hb hs hW.le i _ _ old new
    (lexMinimizer_mem_gridCube b (X.isValidChain old hs) M hW 0 i.castSucc)
    (by simpa only [Fin.val_succ, Setting.J] using
      lexMinimizer_mem_gridCube b (X.isValidChain old hs) M hW 0 i.succ)

end IsotropicVariance.Paper.Proofs.Responses
