/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Blocks
public import IsotropicVariance.Infra.Measurability.SlabVersion
public import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry
public import IsotropicVariance.Paper.Proofs.SmallMean.Fluctuation

/-!
# The gain of a block replacement as a function of the slab information

The gain `sup_{u ∈ I_i(j), v ∈ I_{i+1}(k)} (D_i^G(u, v) − D_i(u, v))₊` of a replacement
(`Setting.blockGain`, Section `sec:gain`), for old and new outcomes with the law of the
noise, is almost surely equal to a function of the old and new information of the slab `i`
(`exists_measurable_blockGain_ae`): replace the slab passage time by its continuous version
measurable for the information of the slab (`Infra.Slab.exists_slabTime_version`) and the
supremum over the two compact cubes by one along a dense sequence (`iSup_iSup_eq_iSup_seq`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.BlockReplacement

variable {m : ℕ}

/-- The supremum of a continuous function over the product of two nonempty compact sets is its
supremum along a sequence of the product whose closure contains it. -/
theorem iSup_iSup_eq_iSup_seq {A B : Set (Pt m)} (hA : IsCompact A) (hB : IsCompact B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) {f : Pt m × Pt m → ℝ} (hf : Continuous f)
    {q : ℕ → Pt m × Pt m} (hq : ∀ n, q n ∈ A ×ˢ B) (hd : A ×ˢ B ⊆ closure (range q)) :
    (⨆ (u : A) (v : B), f (u, v)) = ⨆ n, f (q n) := by
  obtain ⟨M, hM⟩ := ((hA.prod hB).image hf).bddAbove
  have hfM : ∀ x ∈ A ×ˢ B, f x ≤ M := fun x hx => hM ⟨x, hx, rfl⟩
  have hseq : BddAbove (range fun n => f (q n)) :=
    ⟨M, by rintro _ ⟨n, rfl⟩; exact hfM _ (hq n)⟩
  have hin : ∀ u : A, BddAbove (range fun v : B => f (u, v)) := fun u =>
    ⟨M, by rintro _ ⟨v, rfl⟩; exact hfM _ ⟨u.2, v.2⟩⟩
  have : Nonempty A := hAn.to_subtype
  have : Nonempty B := hBn.to_subtype
  have hout : BddAbove (range fun u : A => ⨆ v : B, f (u, v)) :=
    ⟨M, by rintro _ ⟨u, rfl⟩; exact ciSup_le fun v => hfM _ ⟨u.2, v.2⟩⟩
  apply le_antisymm
  · exact ciSup_le fun u => ciSup_le fun v =>
      SmallMean.le_iSup_of_denseSeq hf hseq (hd ⟨u.2, v.2⟩)
  · refine ciSup_le fun n => ?_
    obtain ⟨hu, hv⟩ := hq n
    exact (le_ciSup (hin ⟨_, hu⟩) ⟨_, hv⟩).trans (le_ciSup hout ⟨_, hu⟩)

/-- **The gain of a replacement is a function of the slab information.** For old and new outcomes
with the law of the noise, the gain of the slab `i` between the cubes `I_i(j)` and `I_{i+1}(k)` is
almost surely equal to a function measurable for the old and new information of the slab. -/
theorem exists_measurable_blockGain_ae (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {s W : ℝ}
    (hs : 0 < s) (hW : 0 < W) (i : ℕ) (j k : Fin m → ℤ) {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} {old new : Ω' → X.Ω} (hold : MeasurePreserving old P' X.P)
    (hnew : MeasurePreserving new P' X.P) :
    ∃ g : Ω' → ℝ, Measurable[(X.info (chainSlab s 0 i).set).comap old ⊔
        (X.info (chainSlab s 0 i).set).comap new] g ∧
      (fun ω => X.blockGain b s W i j k (old ω) (new ω)) =ᵐ[P'] g := by
  obtain ⟨V, -, hVc, hVi, hVae⟩ := Infra.Slab.exists_slabTime_version X hb (chainSlab s 0 i)
  have hA := SmallMean.isCompact_gridCube (m := m) s W i j
  have hB := SmallMean.isCompact_gridCube (m := m) s W (i + 1) k
  have hAn := SmallMean.gridCube_nonempty (m := m) s hW.le i j
  have hBn := SmallMean.gridCube_nonempty (m := m) s hW.le (i + 1) k
  have hAS := SmallMean.gridCube_subset_set (m := m) hs.le W i j
  have hBS := SmallMean.gridCube_succ_subset_set (m := m) hs.le W i k
  obtain ⟨q, hq, hd⟩ := SmallMean.exists_dense_seq_in (hAn.prod hBn)
  refine ⟨fun ω => ⨆ n, max (V (new ω) (q n) - V (old ω) (q n)) 0, ?_, ?_⟩
  · refine Measurable.iSup fun n => ?_
    have hn' : Measurable[(X.info (chainSlab s 0 i).set).comap new]
        fun ω => V (new ω) (q n) :=
      (measurable_pi_apply (q n)).comp (hVi.comp (comap_measurable new))
    have ho' : Measurable[(X.info (chainSlab s 0 i).set).comap old]
        fun ω => V (old ω) (q n) :=
      (measurable_pi_apply (q n)).comp (hVi.comp (comap_measurable old))
    exact ((hn'.mono le_sup_right le_rfl).sub (ho'.mono le_sup_left le_rfl)).max measurable_const
  · filter_upwards [hold.quasiMeasurePreserving.ae hVae, hnew.quasiMeasurePreserving.ae hVae]
      with ω ho hn
    have hf : Continuous fun p : Pt m × Pt m => max (V (new ω) p - V (old ω) p) 0 :=
      ((hVc _).sub (hVc _)).max continuous_const
    rw [← iSup_iSup_eq_iSup_seq hA hB hAn hBn hf hq hd]
    refine iSup_congr fun u => iSup_congr fun v => ?_
    rw [ho u (hAS u.2) v (hBS v.2), hn u (hAS u.2) v (hBS v.2)]

end IsotropicVariance.Paper.Proofs.BlockReplacement
