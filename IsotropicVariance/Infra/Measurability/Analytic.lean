/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Tactic.FunProp

/-!
# Universal measurability of analytic sets

Measurable envelopes of the images of Baire cylinders form a countable tree. Outside one
null set, membership in an envelope continues to a child envelope. A branch then gives a
preimage by continuity. This envelope proof works directly for s-finite measures and avoids
assuming that a Borel cost sublevel is compact.
-/

@[expose] public section

open Set Function Filter MeasureTheory PiNat
open scoped Topology

namespace IsotropicVariance.Infra.Measurability

variable {α : Type*} [TopologicalSpace α] [T2Space α]
  [MeasurableSpace α] [OpensMeasurableSpace α]

/-- The finite prefix specified by `s`. -/
def prefixSet {n : ℕ} (s : Fin n → ℕ) : Set (ℕ → ℕ) :=
  {x | ∀ i : Fin n, x i = s i}

lemma prefixSet_snoc {n : ℕ} (s : Fin n → ℕ) :
    prefixSet s = ⋃ k : ℕ, prefixSet (Fin.snoc s k) := by
  ext x
  constructor
  · intro hx
    refine mem_iUnion.mpr ⟨x n, ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using hx j
  · intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    intro i
    simpa using hk i.castSucc

/-- A measurable envelope lying in the closure of the set. -/
noncomputable def closedEnvelope (μ : Measure α) (s : Set α) : Set α :=
  toMeasurable μ s ∩ closure s

omit [T2Space α] in
lemma measurableSet_closedEnvelope (μ : Measure α) (s : Set α) :
    MeasurableSet (closedEnvelope μ s) :=
  (measurableSet_toMeasurable μ s).inter isClosed_closure.measurableSet

omit [T2Space α] [OpensMeasurableSpace α] in
lemma subset_closedEnvelope (μ : Measure α) (s : Set α) : s ⊆ closedEnvelope μ s :=
  subset_inter (subset_toMeasurable μ s) subset_closure

omit [T2Space α] [OpensMeasurableSpace α] in
lemma closedEnvelope_ae_subset (μ : Measure α) [SFinite μ] {s t : Set α}
    (ht : MeasurableSet t) (hst : s ⊆ t) : closedEnvelope μ s ≤ᵐ[μ] t := by
  apply ae_le_set.mpr
  apply measure_mono_null (show closedEnvelope μ s \ t ⊆ toMeasurable μ s ∩ tᶜ by
    intro x hx; exact ⟨hx.1.1, hx.2⟩)
  rw [μ.measure_toMeasurable_inter_of_sFinite ht.compl]
  apply measure_mono_null (show s ∩ tᶜ ⊆ ∅ by
    intro x hx; exact (hx.2 (hst hx.1)).elim) (measure_empty)

/-- Continuous images of Baire space are null measurable for s-finite measures. -/
theorem nullMeasurableSet_range_baire (μ : Measure α) [SFinite μ]
    {f : (ℕ → ℕ) → α} (hf : Continuous f) : NullMeasurableSet (range f) μ := by
  classical
  let A (n : ℕ) (s : Fin n → ℕ) := f '' prefixSet s
  let E (n : ℕ) (s : Fin n → ℕ) := closedEnvelope μ (A n s)
  have hE (n : ℕ) (s : Fin n → ℕ) : MeasurableSet (E n s) :=
    measurableSet_closedEnvelope μ _
  have hsplit (n : ℕ) (s : Fin n → ℕ) :
      E n s ≤ᵐ[μ] ⋃ k : ℕ, E (n + 1) (Fin.snoc s k) := by
    apply closedEnvelope_ae_subset μ (MeasurableSet.iUnion fun k => hE _ _)
    dsimp [A]
    rw [prefixSet_snoc, image_iUnion]
    exact iUnion_mono fun k => subset_closedEnvelope μ _
  have hgood : ∀ᵐ y ∂μ, ∀ n (s : Fin n → ℕ),
      y ∈ E n s → ∃ k : ℕ, y ∈ E (n + 1) (Fin.snoc s k) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro s
    filter_upwards [hsplit n s] with y hy
    exact fun h => mem_iUnion.mp (hy h)
  let s0 : Fin 0 → ℕ := Fin.elim0
  have hsub : range f ⊆ E 0 s0 := by
    apply (show range f ⊆ A 0 s0 by simp [A, prefixSet]).trans
    exact subset_closedEnvelope μ _
  have heq : E 0 s0 =ᵐ[μ] range f := by
    filter_upwards [hgood] with y hy
    apply propext
    refine ⟨?_, fun h => hsub h⟩
    intro hy0
    have hnext (n : ℕ) (x : ℕ → ℕ) :
        ∃ k : ℕ, y ∈ E n (fun i => x i) →
          y ∈ E (n + 1) (fun i => update x n k i) := by
      by_cases hx : y ∈ E n (fun i => x i)
      · obtain ⟨k, hk⟩ := hy n _ hx
        refine ⟨k, fun _ => ?_⟩
        convert hk using 2
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp [j.isLt.ne]
      · exact ⟨0, fun h => False.elim (hx h)⟩
    choose next hnext using hnext
    let p : ℕ → (ℕ → ℕ) := fun n => Nat.rec (fun _ => 0)
      (fun n x => update x n (next n x)) n
    have hp (n : ℕ) : p (n + 1) = update (p n) n (next n (p n)) := rfl
    have hpE (n : ℕ) : y ∈ E n (fun i => p n i) := by
      induction n with
      | zero =>
        convert hy0 using 2
      | succ n ih => exact hnext n (p n) ih
    have hstationary (i : ℕ) : ∀ n, i + 1 ≤ n → p n i = p (i + 1) i := by
      apply Nat.le_induction
      · rfl
      · intro n hn ih
        rw [hp, update_of_ne (by omega), ih]
    let x : ℕ → ℕ := fun i => p (i + 1) i
    have hxE (n : ℕ) : y ∈ closure (f '' cylinder x n) := by
      have h := (hpE n).2
      have hcyl : prefixSet (fun i : Fin n => p n i) = cylinder x n := by
        ext z
        constructor
        · intro hz i hi
          exact (hz ⟨i, hi⟩).trans (hstationary i n hi)
        · intro hz i
          exact (hz i i.isLt).trans (hstationary i n i.isLt).symm
      change y ∈ closure (f '' prefixSet (fun i : Fin n => p n i)) at h
      rwa [hcyl] at h
    refine ⟨x, ?_⟩
    by_contra hne
    obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hne
    obtain ⟨w, ⟨z, n, rfl⟩, hxw, hw⟩ :=
      (isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).exists_subset_of_mem_open
        hxu (hu.preimage hf)
    have hcy : f '' cylinder x n ⊆ u := by
      rw [mem_cylinder_iff_eq.mp hxw]
      exact image_subset_iff.mpr hw
    have hc : closure (f '' cylinder x n) ⊆ vᶜ :=
      closure_minimal (hcy.trans (disjoint_left.mp huv)) hv.isClosed_compl
    exact hc (hxE n) hyv
  exact (hE 0 s0).nullMeasurableSet.congr heq

end IsotropicVariance.Infra.Measurability

/-- Analytic sets are universally measurable, here for every s-finite measure (in particular
for finite and sigma-finite measures). The target need only be Hausdorff with measurable opens. -/
theorem MeasureTheory.AnalyticSet.nullMeasurableSet {α : Type*} [TopologicalSpace α]
    [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α] {s : Set α}
    (hs : AnalyticSet s) (μ : Measure α) [SFinite μ] : NullMeasurableSet s μ := by
  rw [AnalyticSet] at hs
  rcases hs with rfl | ⟨f, hf, rfl⟩
  · exact MeasurableSet.empty.nullMeasurableSet
  · exact IsotropicVariance.Infra.Measurability.nullMeasurableSet_range_baire μ hf
