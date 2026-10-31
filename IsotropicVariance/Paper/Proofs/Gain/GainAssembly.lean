/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.GainVariance
import IsotropicVariance.Paper.Proofs.Profiles.Basic

/-!
# Proposition `prop:gain`: elementary facts of the assembly

* `le_one_of_atomsGe`: atoms of mass at least `τ` force `τ ≤ 1`.
* `card_offsets`: the number of choices of the offsets of the `K` slabs.
* `one_le_colCount`: there is at least one translate.

The proof of the proposition is `gainStatement_of_contracts`
(`IsotropicVariance.Paper.Proofs.Gain.Main`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper IsotropicVariance.Paper.Contracts

variable {m : ℕ}

/-- The atom bound of a label forces `τ ≤ 1`. -/
theorem le_one_of_atomsGe (X : Setting.{u} m) {Λ : X.LabelFamily} {τ : ℝ} (hat : Λ.AtomsGe τ) :
    τ ≤ 1 := by
  by_contra hτ
  push Not at hτ
  have hzero : ∀ v, X.P ((Λ.label 0 0) ⁻¹' {v}) = 0 := by
    intro v
    rcases hat 0 0 v with h | h
    · exact h
    · exfalso
      have h1 : X.P ((Λ.label 0 0) ⁻¹' {v}) ≤ 1 := prob_le_one
      have h2 : (1 : ℝ≥0∞) < ENNReal.ofReal τ := by
        rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hτ
      exact absurd (h.trans h1) (not_le.2 h2)
  have hcover : (univ : Set X.Ω) ⊆ ⋃ v, (Λ.label 0 0) ⁻¹' {v} := fun ω _ =>
    mem_iUnion.2 ⟨Λ.label 0 0 ω, rfl⟩
  have := (measure_mono hcover).trans (measure_iUnion_null hzero).le
  rw [measure_univ] at this
  exact absurd this (by norm_num)

/-- The number of offsets of the `K` slabs is `L^{mK}`. -/
theorem card_offsets (K m L : ℕ) :
    (Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞) = (L : ℝ≥0∞) ^ (m * K) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
    ← pow_mul, Nat.cast_pow]

/-- `⌈K^{2/3}⌉ ≥ 1` for `K ≥ 1`. -/
theorem one_le_colCount {K : ℕ} (hK : 1 ≤ K) : 1 ≤ colCount K := by
  unfold colCount
  rw [Nat.one_le_ceil_iff]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hK) _

end IsotropicVariance.Paper.Proofs.Gain
