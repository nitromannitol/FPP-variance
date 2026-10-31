/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.Responses
public import IsotropicVariance.Paper.Proofs.Profiles.RowEnergySetup
import Mathlib.Tactic.Linarith
import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry

/-!
# Measurable block responses and profile bounds

The uniform profile estimate bounds every response in Lemma `lem:blocks`.
The supremum defining `blockGain` is almost everywhere measurable on
any block coupling, since the endpoint dependence is continuous on a separable space.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace IsotropicVariance.Paper.Proofs.Responses

variable {m : ℕ}

open Infra.Slab

/-- The endpoint profile error for a pair of cubes and its slab. -/
noncomputable def slabProfile (X : Setting m) (b : ℝ) (p : CubePair m) (ω : X.Ω) : ℝ :=
  ⨆ (u : p.first) (v : p.second), |X.slabTime b p.slab ω u v - dist (u : Pt m) v|

lemma slabProfile_nonneg (X : Setting m) (b : ℝ) (p : CubePair m) (ω : X.Ω) :
    0 ≤ slabProfile X b p ω :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _

lemma slabProfile_bddAbove (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (p : CubePair m) (hs : 0 ≤ p.dist) (h1 : 0 ≤ p.side₁) (h2 : 0 ≤ p.side₂)
    (ω : X.Ω) : BddAbove (range fun q : p.first × p.second =>
      |X.slabTime b p.slab ω q.1 q.2 - dist (q.1 : Pt m) q.2|) := by
  have : CompactSpace p.first := isCompact_iff_compactSpace.mp
    (Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_first p h1))
  have : CompactSpace p.second := isCompact_iff_compactSpace.mp
    (Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_second p h2))
  exact (isCompact_range (Profiles.continuous_abs_slabTime_sub_dist hb p.slab ω
    (Profiles.cubePair_first_subset_set p hs) (Profiles.cubePair_second_subset_set p hs))).bddAbove

lemma le_slabProfile (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (p : CubePair m) (hs : 0 ≤ p.dist) (h1 : 0 ≤ p.side₁) (h2 : 0 ≤ p.side₂)
    (ω : X.Ω) {u v : Pt m} (hu : u ∈ p.first) (hv : v ∈ p.second) :
    |X.slabTime b p.slab ω u v - dist u v| ≤ slabProfile X b p ω := by
  unfold slabProfile
  rw [Profiles.iSup_iSup_eq_iSup_prod (slabProfile_bddAbove X hb p hs h1 h2 ω)]
  exact le_ciSup (slabProfile_bddAbove X hb p hs h1 h2 ω) (⟨u, hu⟩, ⟨v, hv⟩)

/-- The response is bounded by the two old and new slab profile errors. -/
lemma blockGain_le_slabProfiles (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    {s W : ℝ} (hs : 0 ≤ s) (hW : 0 ≤ W) (i : ℕ) (j k : Fin m → ℤ) (c c' : X.Ω) :
    X.blockGain b s W i j k c c' ≤ slabProfile X b (Profiles.gridPair s W i j k) c +
      slabProfile X b (Profiles.gridPair s W i j k) c' := by
  have h (ω : X.Ω) (u : Pt m) (hu : u ∈ gridCube s W 0 i j) (v : Pt m)
      (hv : v ∈ gridCube s W 0 (i + 1) k) :
      |X.slabTime b (chainSlab s 0 i) ω u v - dist u v| ≤
        slabProfile X b (Profiles.gridPair s W i j k) ω := by
    rw [← Profiles.slabTime_gridPair X b s W i j k]
    exact le_slabProfile X hb _ hs hW hW ω (Profiles.gridCube_subset_first s W hW i j k hu)
      (Profiles.gridCube_subset_second s W hW i j k hv)
  have H := blockGain_le_of_profiles X b s W i j k c c' (h c) (h c')
  simpa only [max_eq_left (slabProfile_nonneg X b _ _)] using H

/-- The response over the two endpoint cubes is an almost everywhere measurable function of
an arbitrary coupling with the correct two marginals. -/
lemma aemeasurable_blockGain {X : Setting m} {b : ℝ} (hb : X.IsUpperBound b)
    {s W : ℝ} (hs : 0 ≤ s) (hW : 0 ≤ W) (i : ℕ) (j k : Fin m → ℤ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (ho : MeasurePreserving old P' X.P) (hn : MeasurePreserving new P' X.P) :
    AEMeasurable (fun ω => X.blockGain b s W i j k (old ω) (new ω)) P' := by
  let I := gridCube s W 0 i j
  let I' := gridCube s W 0 (i + 1) k
  have hI := SmallMean.gridCube_subset_set hs W i j
  have hI' := SmallMean.gridCube_succ_subset_set hs W i k
  have hc (ω : Ω') : Continuous fun q : I × I' =>
      max (X.slabTime b (chainSlab s 0 i) (new ω) q.1 q.2 -
        X.slabTime b (chainSlab s 0 i) (old ω) q.1 q.2) 0 :=
    ((Profiles.continuous_slabTime_on X hb _ _ hI hI').sub
      (Profiles.continuous_slabTime_on X hb _ _ hI hI')).max continuous_const
  have hB (ω : Ω') : BddAbove (range fun q : I × I' =>
      max (X.slabTime b (chainSlab s 0 i) (new ω) q.1 q.2 -
        X.slabTime b (chainSlab s 0 i) (old ω) q.1 q.2) 0) := by
    refine ⟨slabProfile X b (Profiles.gridPair s W i j k) (old ω) +
      slabProfile X b (Profiles.gridPair s W i j k) (new ω), ?_⟩
    rintro _ ⟨⟨u, v⟩, rfl⟩
    have ho' := le_slabProfile X hb (Profiles.gridPair s W i j k) hs hW hW (old ω)
      (Profiles.gridCube_subset_first s W hW i j k u.2)
      (Profiles.gridCube_subset_second s W hW i j k v.2)
    have hn' := le_slabProfile X hb (Profiles.gridPair s W i j k) hs hW hW (new ω)
      (Profiles.gridCube_subset_first s W hW i j k u.2)
      (Profiles.gridCube_subset_second s W hW i j k v.2)
    rw [Profiles.slabTime_gridPair] at ho' hn'
    apply max_le _ (add_nonneg (slabProfile_nonneg X b _ _) (slabProfile_nonneg X b _ _))
    linarith only [(abs_le.mp ho').1, (abs_le.mp hn').2]
  exact Profiles.aemeasurable_iSup₂_of_continuous hc hB fun u v =>
    (((aemeasurable_slabTime X hb (chainSlab s 0 i) u v).comp_quasiMeasurePreserving hn.quasiMeasurePreserving).sub
      ((aemeasurable_slabTime X hb (chainSlab s 0 i) u v).comp_quasiMeasurePreserving ho.quasiMeasurePreserving)).max
      aemeasurable_const

end IsotropicVariance.Paper.Proofs.Responses
