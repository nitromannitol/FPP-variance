/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Selection.MeasurableMin
import Mathlib.Tactic.Positivity

/-! # Successive compact minimization with measurable values -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace IsotropicVariance.Infra.Selection
open CompactFamily
variable {K Ω : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

/-- Successively retain the minimizers of each objective. -/
noncomputable def stage (f : ℕ → Ω → K → ℝ) (hc : ∀ n ω, Continuous (f n ω)) :
    ℕ → Ω → CompactFamily K
  | 0, _ => whole K
  | n + 1, ω => (stage f hc n ω).argmin (f n ω) (hc n ω)

/-- The value of the next objective on a stage. -/
noncomputable def stageValue (f : ℕ → Ω → K → ℝ) (hc : ∀ n ω, Continuous (f n ω))
    (n : ℕ) (ω : Ω) : ℝ := (stage f hc n ω).minValue (f n ω)

lemma mem_stage_iff (f : ℕ → Ω → K → ℝ) (hc : ∀ n ω, Continuous (f n ω))
    (n : ℕ) (ω : Ω) (x : K) :
    x ∈ (stage f hc n ω).carrier ↔ ∀ j < n, f j ω x = stageValue f hc j ω := by
  induction n with
  | zero => simp [stage, whole]
  | succ n ih =>
    change (x ∈ (stage f hc n ω).carrier ∧ f n ω x = stageValue f hc n ω) ↔ _
    rw [ih]
    constructor
    · rintro ⟨h, hn⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h j hj
      · exact hn
    · intro h
      exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)⟩

/-- All values in finite successive minimization are measurable on an arbitrary base. -/
lemma measurable_stageValue [SeparableSpace K] [MeasurableSpace Ω]
    (f : ℕ → Ω → K → ℝ) (hc : ∀ n ω, Continuous (f n ω))
    (hm : ∀ n x, Measurable (fun ω => f n ω x)) (n : ℕ) :
    Measurable (stageValue f hc n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let g : Ω → K → ℝ := fun ω x =>
      ∑ j ∈ Finset.range n, |f j ω x - stageValue f hc j ω|
    have hgc (ω : Ω) : Continuous (g ω) := by
      apply continuous_finsetSum
      intro j _
      exact ((hc j ω).sub continuous_const).abs
    have hgm (x : K) : Measurable (fun ω => g ω x) := by
      apply Finset.measurable_sum
      intro j hj
      exact continuous_abs.measurable.comp ((hm j x).sub (ih j (Finset.mem_range.mp hj)))
    have hpos (ω : Ω) (x : K) : 0 ≤ g ω x := by
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hS (ω : Ω) : (stage f hc n ω).carrier = {x | g ω x = 0} := by
      ext x
      rw [mem_stage_iff]
      simp only [g, mem_ofPred_eq, Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg
        (f j ω x - stageValue f hc j ω)), Finset.mem_range, abs_eq_zero, sub_eq_zero]
    exact measurable_minValue_zero hgc (hc n) hgm (hm n) hpos (stage f hc n) hS

end IsotropicVariance.Infra.Selection
