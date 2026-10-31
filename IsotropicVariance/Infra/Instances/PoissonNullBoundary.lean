/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonInformation
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Poisson independence over null-boundary regions with disjoint interiors

Null sets have zero mass almost surely, including unbounded null sets by closed-ball exhaustion.
Thus a Borel null-boundary restriction agrees a.s. with the restriction to its interior.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace IsotropicVariance.Infra.Instances

/-- A deterministic Borel volume-null set has zero Poisson mass almost surely, without
boundedness. -/
theorem isPoissonProcess_null_count {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {lam : ℝ≥0} {η : Ω → Measure (Pt m)} {P : Measure Ω}
    (h : IsotropicVariance.IsPoissonProcess lam η P) {B : Set (Pt m)}
    (hB : MeasurableSet B) (hvol : volume B = 0) :
    (fun ω => η ω B) =ᵐ[P] fun _ => 0 := by
  have := (isPoissonProcess_coordinates h).isProbabilityMeasure
  have hn (n : ℕ) : (fun ω => η ω (B ∩ Metric.closedBall 0 n)) =ᵐ[P] fun _ => 0 := by
    have hb : Bornology.IsBounded (B ∩ Metric.closedBall (0 : Pt m) n) :=
      Metric.isBounded_closedBall.subset inter_subset_right
    have hl := isPoissonProcess_count_law h (hB.inter Metric.isClosed_closedBall.measurableSet) hb
    have hv : volume (B ∩ Metric.closedBall (0 : Pt m) n) = 0 :=
      measure_mono_null inter_subset_left hvol
    simp only [hv, ENNReal.toNNReal_zero, mul_zero, Poisson.poissonCountLaw_zero] at hl
    exact hasLaw_dirac_iff.mp hl
  filter_upwards [ae_all_iff.mpr hn] with ω hω
  have hm : Monotone (fun n : ℕ => B ∩ Metric.closedBall (0 : Pt m) n) := by
    intro i j hij
    exact inter_subset_inter_right B (Metric.closedBall_subset_closedBall (by exact_mod_cast hij))
  rw [← Metric.iUnion_inter_closedBall_nat B (0 : Pt m), hm.directed_le.measure_iUnion]
  simp only [hω, iSup_const]

/-- Removing the boundary of a region does not change its Poisson restriction almost surely. -/
theorem isPoissonProcess_restrict_interior_ae {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {lam : ℝ≥0} {η : Ω → Measure (Pt m)} {P : Measure Ω}
    (h : IsotropicVariance.IsPoissonProcess lam η P) {S : Set (Pt m)}
    (hb : volume (frontier S) = 0) :
    (fun ω => (η ω).restrict S) =ᵐ[P] fun ω => (η ω).restrict (interior S) := by
  filter_upwards [isPoissonProcess_null_count h isClosed_frontier.measurableSet hb] with ω hω
  apply Measure.restrict_congr_set
  apply measure_symmDiff_eq_zero_iff.mp
  apply measure_mono_null _ hω
  intro x hx
  rcases hx with (⟨hS, hnot⟩ | ⟨hI, hnot⟩)
  · exact ⟨subset_closure hS, hnot⟩
  · exact (hnot (interior_subset hI)).elim

/-- The Poisson independence field of the setting, with null boundaries before disjoint
interiors. -/
theorem isPoissonProcess_iIndep_info {m : ℕ} {Ω ι : Type*} [MeasurableSpace Ω]
    {lam : ℝ≥0} {η : Ω → Measure (Pt m)} {P : Measure Ω}
    (h : IsotropicVariance.IsPoissonProcess lam η P) (S : ι → Set (Pt m))
    (hS : ∀ i, MeasurableSet (S i)) (hb : ∀ i, volume (frontier (S i)) = 0)
    (hd : Pairwise (fun i j => Disjoint (interior (S i)) (interior (S j)))) :
    iIndep (fun i => (Paper.Noise.info (Paper.Noise.poisson lam) (S i)).comap η) P := by
  have hh := (isPoissonProcess_iIndepFun_restrict h (fun i => interior (S i))
    (fun _ => isOpen_interior.measurableSet) hd).congr
      (fun i => (isPoissonProcess_restrict_interior_ae h (hb i)).symm)
  have hinfo := (iIndepFun_iff_iIndep _ _ _).mp hh
  simpa only [poisson_info_eq_comap_restrict (hS _), MeasurableSpace.comap_comp,
    Function.comp_def] using hinfo

end IsotropicVariance.Infra.Instances
