/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Selection.Stages
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The measurable lexicographically least compact minimizer

First minimize the cost, then each coordinate in order. The characterization uses the
first differing coordinate; it also gives uniqueness and translation covariance.
-/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace IsotropicVariance.Infra.Selection
open CompactFamily

/-- Characterization of the lexicographically least minimizer by its initial coordinates. -/
def IsLexMinimizer {k : ℕ} (K : Set (Fin k → ℝ)) (f : (Fin k → ℝ) → ℝ)
    (x : Fin k → ℝ) : Prop :=
  x ∈ K ∧ (∀ y ∈ K, f x ≤ f y) ∧ ∀ y ∈ K, f y = f x →
    ∀ i : Fin k, (∀ j : Fin k, j < i → y j = x j) → x i ≤ y i

section Construction
variable {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (K : Set (Fin k → ℝ)) (hK : IsCompact K) (hne : K.Nonempty)
  (F : Ω → (Fin k → ℝ) → ℝ)
  (hc : ∀ ω, ContinuousOn (F ω) K)

/-- The cost followed by coordinates in their specified order. -/
noncomputable def objectives (n : ℕ) (ω : Ω) (x : K) : ℝ :=
  match n with
  | 0 => F ω x
  | n + 1 => if hi : n < k then x.1 ⟨n, hi⟩ else 0

include hc in
omit [MeasurableSpace Ω] in
lemma objectives_continuous (n : ℕ) (ω : Ω) :
    Continuous (objectives K F n ω) := by
  cases n with
  | zero => exact (hc ω).domRestrict
  | succ n =>
    change Continuous (fun x : K => if hi : n < k then x.1 ⟨n, hi⟩ else 0)
    split_ifs
    · exact (continuous_apply _).comp continuous_subtype_val
    · exact continuous_const

/-- The lexicographic selector, defined by finitely many compact minimizations. -/
noncomputable def lexMinimizer (ω : Ω) : Fin k → ℝ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : Nonempty K := hne.to_subtype
  exact ((stage (objectives K F) (objectives_continuous K F hc) (k + 1) ω).minPoint
    (fun _ => 0) continuous_const).1

omit [MeasurableSpace Ω] in
lemma lexMinimizer_stage (ω : Ω) :
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let : Nonempty K := hne.to_subtype
    ∃ x : K, x.1 = lexMinimizer K hK hne F hc ω ∧
      ∀ j < k + 1, objectives K F j ω x =
        stageValue (objectives K F) (objectives_continuous K F hc) j ω := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Nonempty K := hne.to_subtype
  let S := stage (objectives K F) (objectives_continuous K F hc) (k + 1) ω
  exact ⟨S.minPoint (fun _ => 0) continuous_const, rfl,
    (mem_stage_iff _ _ _ _ _).mp (S.minPoint_mem _ continuous_const)⟩

omit [MeasurableSpace Ω] in
/-- The selector attains the cost minimum and is first in lexicographic order among ties. -/
theorem isLexMinimizer_lexMinimizer (ω : Ω) :
    IsLexMinimizer K (F ω) (lexMinimizer K hK hne F hc ω) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Nonempty K := hne.to_subtype
  obtain ⟨x, hx, hstage⟩ := lexMinimizer_stage K hK hne F hc ω
  rw [← hx]
  have hmin (y : K) : F ω x ≤ F ω y := by
    have H := (whole K).minValue_le (objectives K F 0 ω)
      (objectives_continuous K F hc 0 ω) (mem_univ y)
    change stageValue (objectives K F) (objectives_continuous K F hc) 0 ω ≤
      objectives K F 0 ω y at H
    rw [← hstage 0 (by omega)] at H
    exact H
  refine ⟨x.2, fun y hy => hmin ⟨y, hy⟩, ?_⟩
  intro y hy hcost i hp
  let yK : K := ⟨y, hy⟩
  have hmem : yK ∈ (stage (objectives K F) (objectives_continuous K F hc)
      (i.val + 1) ω).carrier := by
    rw [mem_stage_iff]
    intro j hj
    rw [← hstage j (by omega)]
    cases j with
    | zero => exact hcost
    | succ j =>
      have hjk : j < k := by omega
      simp only [objectives, dite_eq_left hjk]
      exact hp ⟨j, hjk⟩ (by change j < i.val; omega)
  have H := (stage (objectives K F) (objectives_continuous K F hc) (i.val + 1) ω).minValue_le
    _ (objectives_continuous K F hc (i.val + 1) ω) hmem
  change stageValue (objectives K F) (objectives_continuous K F hc) (i.val + 1) ω ≤
    objectives K F (i.val + 1) ω yK at H
  rw [← hstage (i.val + 1) (by omega)] at H
  simpa only [objectives, dite_eq_left i.isLt] using H

/-- The lexicographically least compact minimizer is measurable, for any measurable base. -/
theorem measurable_lexMinimizer (hm : ∀ x ∈ K, Measurable (fun ω => F ω x)) :
    Measurable (lexMinimizer K hK hne F hc) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Nonempty K := hne.to_subtype
  have hm' (n : ℕ) (x : K) : Measurable (fun ω => objectives K F n ω x) := by
    cases n with
    | zero => exact hm x.1 x.2
    | succ n =>
      change Measurable (fun _ : Ω => if hi : n < k then x.1 ⟨n, hi⟩ else 0)
      exact measurable_const
  apply Measurable.of_eval
  intro i
  have heq : (fun ω => lexMinimizer K hK hne F hc ω i) =
      stageValue (objectives K F) (objectives_continuous K F hc) (i.val + 1) := by
    funext ω
    obtain ⟨x, hx, hstage⟩ := lexMinimizer_stage K hK hne F hc ω
    rw [← hx]
    simpa only [objectives, dite_eq_left i.isLt] using hstage (i.val + 1) (by omega)
  rw [heq]
  exact measurable_stageValue _ _ hm' _
end Construction
end IsotropicVariance.Infra.Selection
