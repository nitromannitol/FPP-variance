/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Poisson.Counts
public import IsotropicVariance.Infra.Poisson.Basic

/-!
# Finite-dimensional uniqueness for Poisson counts

A finite family of bounded Borel regions is split into its disjoint membership atoms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace IsotropicVariance.Infra.Poisson

/-- The finite disjoint-count independence axiom, with an arbitrary finite index type. -/
theorem IsPoissonProcess.iIndepFun_counts {d : ℕ} {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {lam : ℝ≥0} {η : Ω → Measure (E d)} {P : Measure Ω} (h : IsPoissonProcess lam η P)
    (B : ι → Set (E d)) (hB : ∀ i, MeasurableSet (B i))
    (hb : ∀ i, Bornology.IsBounded (B i)) (hd : Pairwise (fun i j => Disjoint (B i) (B j))) :
    iIndepFun (fun i ω => η ω (B i)) P := by
  let e := (Fintype.equivFin ι).symm
  have hh := h.independent (Fintype.card ι) (fun i => B (e i))
    (fun i => hB (e i)) (fun i => hb (e i))
    (fun i j hij => hd (e.injective.ne hij))
  exact (iIndepFun_precomp_of_bijective e.bijective).mp hh

/-- The Boolean membership vector of a point in a finite family of regions. -/
noncomputable def membershipPattern {X ι : Type*} (B : ι → Set X) (x : X) : ι → Bool := by
  classical
  exact fun i => if x ∈ B i then true else false

/-- Membership-pattern fibers inside the union of the regions. -/
def regionAtom {X ι : Type*} (B : ι → Set X) (s : ι → Bool) : Set X :=
  (⋃ i, B i) ∩ membershipPattern B ⁻¹' {s}

/-- Pattern coordinates encode region membership exactly. -/
theorem membershipPattern_eq_true {X ι : Type*} (B : ι → Set X) (x : X) (i : ι) :
    membershipPattern B x i = true ↔ x ∈ B i := by
  classical
  simp [membershipPattern]

/-- Membership patterns are measurable. -/
theorem measurable_membershipPattern {X ι : Type*} [MeasurableSpace X]
    (B : ι → Set X) (hB : ∀ i, MeasurableSet (B i)) : Measurable (membershipPattern B) := by
  classical
  apply Measurable.of_eval
  intro i
  exact Measurable.ite (hB i) measurable_const measurable_const

/-- Membership atoms are Borel. -/
theorem measurableSet_regionAtom {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (B : ι → Set X) (hB : ∀ i, MeasurableSet (B i)) (s : ι → Bool) :
    MeasurableSet (regionAtom B s) :=
  (MeasurableSet.iUnion hB).inter ((measurable_membershipPattern B hB) (measurableSet_singleton s))

/-- Bounded regions have bounded membership atoms. -/
theorem isBounded_regionAtom {d : ℕ} {ι : Type*} [Fintype ι]
    (B : ι → Set (E d)) (hb : ∀ i, Bornology.IsBounded (B i)) (s : ι → Bool) :
    Bornology.IsBounded (regionAtom B s) :=
  (Bornology.isBounded_iUnion.mpr hb).subset inter_subset_left

/-- Distinct membership atoms are disjoint. -/
theorem pairwiseDisjoint_regionAtom {X ι : Type*} (B : ι → Set X) :
    Pairwise (fun s t : ι → Bool => Disjoint (regionAtom B s) (regionAtom B t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hst (hx.2.symm.trans hy.2)

/-- Reconstruct a region from the atoms whose membership coordinate is true. -/
theorem region_eq_iUnion_atoms {X ι : Type*} [Fintype ι] (B : ι → Set X) (i : ι) :
    B i = ⋃ s : ι → Bool, if s i then regionAtom B s else ∅ := by
  classical
  ext x
  constructor
  · intro hx
    apply Set.mem_iUnion.mpr
    refine ⟨membershipPattern B x, ?_⟩
    rw [(membershipPattern_eq_true B x i).mpr hx]
    exact ⟨Set.mem_iUnion.mpr ⟨i, hx⟩, rfl⟩
  · intro hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    split_ifs at hs with hi
    · exact (membershipPattern_eq_true B x i).mp (by rw [hs.2]; exact hi)
    · exact hs.elim

/-- Counts on overlapping Borel regions are deterministic sums of the disjoint atom counts. -/
theorem count_eq_sum_atoms {X ι : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι]
    (ν : Measure X) (B : ι → Set X) (hB : ∀ i, MeasurableSet (B i)) (i : ι) :
    ν (B i) = ∑ s : ι → Bool, if s i then ν (regionAtom B s) else 0 := by
  classical
  rw [region_eq_iUnion_atoms B i, measure_iUnion]
  · rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp
  · intro s t hst
    by_cases hs : s i = true <;> by_cases ht : t i = true
    · simpa only [Function.onFun, hs, ht, ↓reduceIte] using pairwiseDisjoint_regionAtom B hst
    · simp [Function.onFun, ht]
    · simp [Function.onFun, hs]
    · simp [Function.onFun, hs]
  · intro s
    split_ifs
    · exact measurableSet_regionAtom B hB s
    · exact MeasurableSet.empty

/-- Any two Poisson processes of the same intensity have the same finite joint bounded counts. -/
theorem IsPoissonProcess.map_bounded_counts_eq {d : ℕ} {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι]
    {lam : ℝ≥0} {η : Ω → Measure (E d)} {ξ : Ω' → Measure (E d)}
    {P : Measure Ω} {Q : Measure Ω'} (hη : IsPoissonProcess lam η P)
    (hξ : IsPoissonProcess lam ξ Q) (B : ι → Set (E d))
    (hB : ∀ i, MeasurableSet (B i)) (hb : ∀ i, Bornology.IsBounded (B i)) :
    P.map (fun ω => fun i => η ω (B i)) = Q.map (fun ω => fun i => ξ ω (B i)) := by
  classical
  let A := regionAtom B
  have hmA (s : ι → Bool) : MeasurableSet (A s) := measurableSet_regionAtom B hB s
  have hbA (s : ι → Bool) : Bornology.IsBounded (A s) := isBounded_regionAtom B hb s
  have hdA : Pairwise (fun s t => Disjoint (A s) (A t)) := pairwiseDisjoint_regionAtom B
  have hlη := (hη.iIndepFun_counts A hmA hbA hdA).hasLaw_pi (fun s => hη.count_law (A s) (hmA s) (hbA s))
  have hlξ := (hξ.iIndepFun_counts A hmA hbA hdA).hasLaw_pi (fun s => hξ.count_law (A s) (hmA s) (hbA s))
  let H (v : (ι → Bool) → ℝ≥0∞) : ι → ℝ≥0∞ :=
    fun i => ∑ s : ι → Bool, if s i then v s else 0
  have hmH : Measurable H := by
    apply Measurable.of_eval
    intro i
    apply Finset.measurable_sum
    intro s _
    split_ifs
    · exact measurable_pi_apply s
    · exact measurable_const
  have hmη : Measurable (fun ω => fun s => η ω (A s)) :=
    Measurable.of_eval fun s => hη.measurable_count (hmA s)
  have hmξ : Measurable (fun ω => fun s => ξ ω (A s)) :=
    Measurable.of_eval fun s => hξ.measurable_count (hmA s)
  have heqη : H ∘ (fun ω => fun s => η ω (A s)) = (fun ω => fun i => η ω (B i)) := by
    funext ω i
    exact (count_eq_sum_atoms (η ω) B hB i).symm
  have heqξ : H ∘ (fun ω => fun s => ξ ω (A s)) = (fun ω => fun i => ξ ω (B i)) := by
    funext ω i
    exact (count_eq_sum_atoms (ξ ω) B hB i).symm
  have hh := congrArg (Measure.map H) (hlη.map_eq.trans hlξ.map_eq.symm)
  rwa [Measure.map_map hmH hmη, Measure.map_map hmH hmξ, heqη, heqξ] at hh

end IsotropicVariance.Infra.Poisson
