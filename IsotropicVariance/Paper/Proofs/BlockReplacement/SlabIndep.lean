/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Blocks
public import IsotropicVariance.Paper.Proofs.BlockReplacement.CondIndep
public import IsotropicVariance.Infra.Measurability.MinimizerMeasurable
public import IsotropicVariance.Paper.Proofs.Gain.BridgeGeometry
public import IsotropicVariance.Paper.Proofs.Gain.AveragedMin
public import IsotropicVariance.Paper.Defs.Minimum
import IsotropicVariance.Paper.Proofs.Gain.BridgeCoupling

/-!
# A block replacement and the other slabs

For a coupling replacing the noise of a block `G` of the slab `S = S_i` (Lemma `lem:blocks`), the
old and new information in `S` is independent of the old information in the other slabs
(`IsBlockCoupling.indep_slab`). This is what makes the conditional rewards of different slabs
independent in the proof of Lemma `lem:blocks`, whatever randomness outside the noise the coupling
uses.

The proof: the pair in `G` is independent of the old noise off `G` (the coupling); the old noise
in `S \ G` and in the other slabs are independent (`iIndep_info`); the information of another
slab is almost surely that of its part off `G`, the two meeting in a null face; the information of
`S` is almost surely that of `G` and `S \ G` (`union_ae`); and off `G` the new noise is almost
surely the old one.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.BlockReplacement

open Gain.Bridge

/-! ### Almost sure closures -/

section Closure

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]

/-- The preimage of the almost sure closure lies in the closure of the preimage. -/
theorem comap_aeClosure_le {P : Measure Ω} {Q : Measure E} {f : Ω → E}
    (hf : Measure.QuasiMeasurePreserving f P Q) (m₀ : MeasurableSpace E) :
    (aeClosure m₀ Q).comap f ≤ aeClosure (m₀.comap f) P := by
  rintro _ ⟨t, ⟨t', ht', htt'⟩, rfl⟩
  exact ⟨f ⁻¹' t', ⟨t', ht', rfl⟩, hf.preimage_ae_eq htt'⟩

end Closure

/-! ### The information of a set split by a subset -/

section Split

variable {m : ℕ} (N : NoiseModel m)

/-- If `G ⊆ S`, every event of the noise in `S` is almost surely an event of the noise in `G` and
in `S \ G` (`union_ae`). -/
theorem info_le_aeClosure_sup {S G : Set (Pt m)} (hS : MeasurableSet S)
    (hSfr : volume (frontier S) = 0) (hG : MeasurableSet G) (hGfr : volume (frontier G) = 0)
    (hGS : G ⊆ S) : N.info S ≤ aeClosure (N.info G ⊔ N.info (S \ G)) N.P := by
  have h := info_union_le_aeClosure N hG hGfr (hS.diff hG) (null_frontier_diff hSfr hGfr)
    disjoint_sdiff_right
  rwa [union_sdiff_cancel hGS] at h

end Split

/-! ### Slabs and blocks -/

section Geometry

variable {m : ℕ}

/-- Two different slabs of a chain meet in a null set. -/
theorem volume_chainSlab_inter {s : ℝ} (hs : 0 < s) {r i : ℕ} (hri : r ≠ i) :
    volume ((chainSlab (m := m) s 0 r).set ∩ (chainSlab s 0 i).set) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (volume_lon_eq (m := m) ((max r i : ℕ) * s))
  rw [mem_inter_iff, mem_chainSlab_set, mem_chainSlab_set] at hx
  simp only [Pt.lon_zero, zero_add] at hx
  change Pt.lon x = ((max r i : ℕ) : ℝ) * s
  rcases lt_or_gt_of_ne hri with h | h
  · have h' : (r : ℝ) + 1 ≤ i := by exact_mod_cast h
    rw [max_eq_right h.le]
    nlinarith [hx.1.2, hx.2.1]
  · have h' : (i : ℝ) + 1 ≤ r := by exact_mod_cast h
    rw [max_eq_left h.le]
    nlinarith [hx.1.1, hx.2.2]

end Geometry

/-! ### The replacement and the other slabs -/

section Coupling

variable {m : ℕ} {X : Setting m}

/-- The information of the slabs of a chain other than the slab `i`. -/
@[instance_reducible]
def otherSlabsInfo (X : Setting m) (s : ℝ) {K : ℕ} (i : Fin K) : MeasurableSpace X.Ω :=
  ⨆ r : {r : Fin K // r ≠ i}, X.info (chainSlab s 0 r).set

/-- **A block replacement and the other slabs.** For a coupling replacing the noise of a block of
the slab `S_i`, the old and new information in `S_i` is independent of the old information in the
other slabs of the chain. -/
theorem IsBlockCoupling.indep_slab {s W : ℝ} (hs : 0 < s) {L K : ℕ} (i : Fin K)
    {z : Fin m → ℤ} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {old new : Ω' → X.Ω} (hcpl : X.IsBlockCoupling (block s W L i z) P' old new) :
    Indep ((X.info (chainSlab s 0 i).set).comap old ⊔ (X.info (chainSlab s 0 i).set).comap new)
      ((otherSlabsInfo X s i).comap old) P' := by
  set S := (chainSlab s 0 (i : ℕ)).set with hSdef
  set G := block s W L i z with hGdef
  set T := S \ G with hTdef
  have hold := hcpl.measurePreserving_old
  have hnew := hcpl.measurePreserving_new
  have hS : MeasurableSet S := Infra.Slab.measurableSet_slab_set _
  have hSfr : volume (frontier S) = 0 := Infra.Slab.volume_frontier_slab_set _
  have hG : MeasurableSet G := measurableSet_block s W L i z
  have hGfr : volume (frontier G) = 0 := volume_frontier_block s W L i z
  have hGS : G ⊆ S := block_subset_chainSlab s W L i z
  have hmΩ : ∀ U, (X.info U).comap old ≤ ‹MeasurableSpace Ω'› := fun U =>
    (MeasurableSpace.comap_mono (X.info_le U)).trans hold.measurable.comap_le
  have hmΩ' : ∀ U, (X.info U).comap new ≤ ‹MeasurableSpace Ω'› := fun U =>
    (MeasurableSpace.comap_mono (X.info_le U)).trans hnew.measurable.comap_le
  have hc_le : (otherSlabsInfo X s i) ≤ X.measurableSpace := iSup_le fun r => X.info_le _
  -- the other slabs are, up to null sets, off `G`
  have hcG : (otherSlabsInfo X s i) ≤ aeClosure (X.info Gᶜ) X.P := by
    refine iSup_le fun r => ?_
    have hri : (r.1 : ℕ) ≠ i := fun h => r.2 (Fin.ext h)
    have hnull : volume ((chainSlab s 0 r.1).set ∩ G) = 0 :=
      measure_mono_null (inter_subset_inter_right _ hGS) (volume_chainSlab_inter hs hri)
    refine (info_le_aeClosure_diff X.toNoiseModel (Infra.Slab.measurableSet_slab_set _)
      (Infra.Slab.volume_frontier_slab_set _) hG hGfr hnull).trans (aeClosure_mono ?_)
    exact X.info_mono fun x hx => hx.2
  have h𝒜c : Indep ((X.info G).comap old ⊔ (X.info G).comap new) (((X.info T).comap old) ⊔ (otherSlabsInfo X s i).comap old) P' := by
    have h1 : Indep ((X.info G).comap old ⊔ (X.info G).comap new) (aeClosure ((X.info Gᶜ).comap old) P') P' :=
      (indep_aeClosure_left hcpl.indep.symm).symm
    refine indep_of_indep_of_le_right h1 (sup_le ?_ ?_)
    · exact (MeasurableSpace.comap_mono (X.info_mono fun x hx => hx.2)).trans le_aeClosure
    · exact (MeasurableSpace.comap_mono hcG).trans (comap_aeClosure_le hold.quasiMeasurePreserving _)
  -- the old noise in `S \ G` and in the other slabs
  have hℬc : Indep ((X.info T).comap old) ((otherSlabsInfo X s i).comap old) P' := by
    let U : Fin K → Set (Pt m) := fun r => if r = i then T else (chainSlab s 0 r).set
    have hU : ∀ r, MeasurableSet (U r) := fun r => by
      by_cases h : r = i
      · simp only [U, h, ite_true]; exact hS.diff hG
      · simp only [U, h, ite_false]; exact Infra.Slab.measurableSet_slab_set _
    have hUfr : ∀ r, volume (frontier (U r)) = 0 := fun r => by
      by_cases h : r = i
      · simp only [U, h, ite_true]; exact null_frontier_diff hSfr hGfr
      · simp only [U, h, ite_false]; exact Infra.Slab.volume_frontier_slab_set _
    have hUd : Pairwise (Function.onFun Disjoint fun r => interior (U r)) := by
      intro r r' hrr'
      have hsub : ∀ r, interior (U r) ⊆ interior (chainSlab s 0 r).set := fun r => by
        by_cases h : r = i
        · simp only [U, h, ite_true]
          exact interior_mono (by rw [hTdef]; exact sdiff_subset)
        · simp only [U, h, ite_false]; exact le_rfl
      exact (Infra.Slab.pairwise_disjoint_interior_chainSlab hs 0 K hrr').mono (hsub r) (hsub r')
    have hind := X.iIndep_info (Fin K) U hU hUfr hUd
    have h := indep_iSup_of_disjoint (fun r => X.info_le (U r)) hind
      (S := {i}) (T := {r | r ≠ i}) (by simp)
    have hl : (⨆ r ∈ ({i} : Set (Fin K)), X.info (U r)) = X.info T := by
      rw [iSup_singleton]
      simp [U]
    have hr : (⨆ r ∈ {r : Fin K | r ≠ i}, X.info (U r)) = otherSlabsInfo X s i := by
      rw [iSup_subtype']
      refine iSup_congr fun r => ?_
      simp only [U]
      rw [ite_eq_right r.2]
    rw [hl, hr] at h
    exact Gain.Bridge.indep_comap_of_measurePreserving hold (X.info_le T) hc_le h
  have h𝒜ℬc : Indep (((X.info G).comap old ⊔ (X.info G).comap new) ⊔ ((X.info T).comap old)) ((otherSlabsInfo X s i).comap old) P' :=
    indep_sup_left_of_indep (sup_le (hmΩ G) (hmΩ' G)) (hmΩ T)
      ((MeasurableSpace.comap_mono hc_le).trans hold.measurable.comap_le) h𝒜c hℬc
  -- the information in `S` is, up to null sets, that of the pair in `G` and the old noise in `T`
  have hold_S : (X.info S).comap old ≤ aeClosure (((X.info G).comap old ⊔ (X.info G).comap new) ⊔ ((X.info T).comap old)) P' := by
    refine (MeasurableSpace.comap_mono (info_le_aeClosure_sup X.toNoiseModel hS hSfr hG hGfr hGS)).trans
      ((comap_aeClosure_le hold.quasiMeasurePreserving _).trans (aeClosure_mono ?_))
    rw [MeasurableSpace.comap_sup]
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hnew_T : (X.info T).comap new ≤ aeClosure ((X.info T).comap old) P' := by
    rintro _ ⟨A, hA, rfl⟩
    refine ⟨old ⁻¹' A, ⟨A, hA, rfl⟩, ?_⟩
    have h := hcpl.agree_compl A (X.info_mono (fun x hx => hx.2) A hA)
    exact Filter.eventuallyEqSet_iff.2 (h.mono fun ω hω => hω.symm)
  have hnew_S : (X.info S).comap new ≤ aeClosure (((X.info G).comap old ⊔ (X.info G).comap new) ⊔ ((X.info T).comap old)) P' := by
    refine (MeasurableSpace.comap_mono (info_le_aeClosure_sup X.toNoiseModel hS hSfr hG hGfr hGS)).trans
      ((comap_aeClosure_le hnew.quasiMeasurePreserving _).trans (aeClosure_le_of_le ?_))
    rw [MeasurableSpace.comap_sup]
    refine sup_le ((le_sup_right.trans le_sup_left).trans le_aeClosure) ?_
    exact hnew_T.trans (aeClosure_mono le_sup_right)
  exact indep_of_indep_of_le_left (indep_aeClosure_left h𝒜ℬc) (sup_le hold_S hnew_S)

end Coupling

end IsotropicVariance.Paper.Proofs.BlockReplacement
