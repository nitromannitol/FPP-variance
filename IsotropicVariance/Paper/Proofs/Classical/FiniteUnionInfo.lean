/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.AEVersions

/-! # The finite regional form of the noise union law

Padding a nonempty finite partition by empty sets reduces to the model's
countable union law. Empty-set information is already contained in any one
region, so padding adds no information.
-/

@[expose] public section
open MeasureTheory Set
namespace IsotropicVariance.Paper.Proofs.Classical

/-- Transfer of events in a finite union to the join of regional information. -/
theorem finite_union_event_transfer {m n : ℕ} (N : NoiseModel m) (hn : 0 < n)
    (S : Fin n → Set (Pt m)) (hS : ∀ i, MeasurableSet (S i))
    (hNull : ∀ i, volume (frontier (S i)) = 0)
    (hDisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (A : Set N.Ω) (hA : MeasurableSet[N.info (⋃ i, S i)] A) :
    ∃ B : Set N.Ω, MeasurableSet[⨆ i, N.info (S i)] B ∧ N.P (symmDiff A B) = 0 := by
  let T := fun k : ℕ => if h : k < n then S ⟨k, h⟩ else ∅
  have hTm (k : ℕ) : MeasurableSet (T k) := by
    by_cases hk : k < n
    · simpa only [T, dite_eq_left hk] using hS ⟨k, hk⟩
    · simp only [T, dite_eq_right hk, MeasurableSet.empty]
  have hTn (k : ℕ) : volume (frontier (T k)) = 0 := by
    by_cases hk : k < n
    · simpa only [T, dite_eq_left hk] using hNull ⟨k, hk⟩
    · simp only [T, dite_eq_right hk, frontier_empty, measure_empty]
  have hTd : Pairwise (fun i j => Disjoint (T i) (T j)) := by
    intro i j hij
    by_cases hi : i < n
    · by_cases hj : j < n
      · simpa only [T, dite_eq_left hi, dite_eq_left hj] using
          hDisjoint (fun h => hij (congrArg Fin.val h) : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩)
      · simp only [T, dite_eq_right hj, disjoint_empty]
    · simp only [T, dite_eq_right hi, empty_disjoint]
  have hUnion : (⋃ k, T k) = ⋃ i, S i := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      by_cases hkn : k < n
      · exact ⟨⟨k, hkn⟩, by simpa only [T, dite_eq_left hkn] using hk⟩
      · simp only [T, dite_eq_right hkn, mem_empty_iff_false] at hk
    · rintro ⟨i, hi⟩
      exact ⟨i, by simpa only [T, dite_eq_left i.isLt] using hi⟩
  have hLe : (⨆ k, N.info (T k)) ≤ ⨆ i, N.info (S i) := by
    apply iSup_le
    intro k
    by_cases hk : k < n
    · simpa only [T, dite_eq_left hk] using le_iSup (fun i => N.info (S i)) ⟨k, hk⟩
    · simp only [T, dite_eq_right hk]
      exact (N.info_mono (empty_subset (S ⟨0, hn⟩))).trans (le_iSup (fun i => N.info (S i)) ⟨0, hn⟩)
  obtain ⟨B, hB, hAB⟩ := N.union_ae T hTm hTn hTd A (by rwa [hUnion])
  exact ⟨B, hLe B hB, hAB⟩

/-- A regional observable has an almost-sure version measurable for the finite
join, rather than requiring exact equality of regional sigma algebras. -/
theorem exists_version_finite_union {m n : ℕ} (N : NoiseModel m) (hn : 0 < n)
    (S : Fin n → Set (Pt m)) (hS : ∀ i, MeasurableSet (S i))
    (hNull : ∀ i, volume (frontier (S i)) = 0)
    (hDisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    {f : N.Ω → Z} (hf : Measurable[N.info (⋃ i, S i)] f) :
    ∃ g : N.Ω → Z, Measurable[⨆ i, N.info (S i)] g ∧ f =ᵐ[N.P] g :=
  exists_measurable_version_of_event_transfer N.P _ _
    (finite_union_event_transfer N hn S hS hNull hDisjoint) hf

end IsotropicVariance.Paper.Proofs.Classical
