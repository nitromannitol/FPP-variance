/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.Steps
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Changes on the core of a block under a label-preserving resampling

The proof of Lemma `lem:residual` uses equation `eq:labelprofile` before and after
resampling. The label value cancels, so the normalized change of any passage time between the two
core faces is bounded by the sum of the two profile errors. The errors have the same norm as before
resampling, because both marginals have the original law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.LabelResidual

open IsotropicVariance.Paper IsotropicVariance.Paper.Proofs.Gain

variable {m : ℕ} {X : Setting.{u} m}

/-- The error in equation `eq:labelprofile` for the block `(i,z)`, with the supremum in
`[0,∞]`. -/
noncomputable def profileError (Λ : X.LabelFamily) (b : ℝ) (K : ℕ) (A ℓ : ℝ)
    (L i : ℕ) (z : Fin m → ℤ) (ω : X.Ω) : ℝ≥0∞ :=
  ⨆ (u : coreFace (ℓ / K) (W K A (ℓ / K)) L i z)
    (v : coreFace (ℓ / K) (W K A (ℓ / K)) L (i + 1) z),
    ENNReal.ofReal |(X.slabTime b (chainSlab (ℓ / K) 0 i) ω u v - ℓ / K) /
      Q K A (ℓ / K) -
      Λ.value (Λ.label i z ω) ((u : Pt m) - blockCorner (ℓ / K) (W K A (ℓ / K)) i z)
        ((v : Pt m) - blockCorner (ℓ / K) (W K A (ℓ / K)) i z)|

/-- The bound of equation `eq:labelprofile` is precisely the norm bound for `profileError`. -/
theorem eLpNorm_profileError_le {Λ : X.LabelFamily} {b A ℓ ε : ℝ} {K L i : ℕ}
    {z : Fin m → ℤ} (h : LabelProfileBound X b K A ℓ L Λ ε) (hi : i < K) :
    eLpNorm (profileError Λ b K A ℓ L i z) (8 * (m + 1) : ℝ≥0∞) X.P ≤
      ENNReal.ofReal ε :=
  h i hi z

/-- Finite profile error bounds give the measurability required to transfer its norm. -/
theorem aestronglyMeasurable_profileError {Λ : X.LabelFamily} {b A ℓ ε : ℝ} {K L i : ℕ}
    {z : Fin m → ℤ} (h : LabelProfileBound X b K A ℓ L Λ ε) (hi : i < K) :
    AEStronglyMeasurable (profileError Λ b K A ℓ L i z) X.P :=
  aestronglyMeasurable_of_eLpNorm_ne_top
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eLpNorm_profileError_le h hi))

/-- The label value cancels between two configurations having the same label. -/
theorem ofReal_abs_normalized_sub_le {Λ : X.LabelFamily} {b A ℓ : ℝ} {K L i : ℕ}
    {z : Fin m → ℤ} {old new : X.Ω}
    (hlabel : Λ.label i z new = Λ.label i z old)
    (u : coreFace (ℓ / K) (W K A (ℓ / K)) L i z)
    (v : coreFace (ℓ / K) (W K A (ℓ / K)) L (i + 1) z) :
    ENNReal.ofReal |(X.slabTime b (chainSlab (ℓ / K) 0 i) new u v -
      X.slabTime b (chainSlab (ℓ / K) 0 i) old u v) / Q K A (ℓ / K)| ≤
      profileError Λ b K A ℓ L i z new + profileError Λ b K A ℓ L i z old := by
  let a := Λ.value (Λ.label i z old)
    ((u : Pt m) - blockCorner (ℓ / K) (W K A (ℓ / K)) i z)
    ((v : Pt m) - blockCorner (ℓ / K) (W K A (ℓ / K)) i z)
  have hnew : ENNReal.ofReal |(X.slabTime b (chainSlab (ℓ / K) 0 i) new u v - ℓ / K) /
      Q K A (ℓ / K) - a| ≤ profileError Λ b K A ℓ L i z new := by
    unfold profileError
    rw [hlabel]
    exact le_iSup_of_le u (le_iSup_of_le v le_rfl)
  have hold : ENNReal.ofReal |(X.slabTime b (chainSlab (ℓ / K) 0 i) old u v - ℓ / K) /
      Q K A (ℓ / K) - a| ≤ profileError Λ b K A ℓ L i z old :=
    le_iSup_of_le u (le_iSup_of_le v le_rfl)
  calc
    _ = ENNReal.ofReal |((X.slabTime b (chainSlab (ℓ / K) 0 i) new u v - ℓ / K) /
          Q K A (ℓ / K) - a) -
        ((X.slabTime b (chainSlab (ℓ / K) 0 i) old u v - ℓ / K) /
          Q K A (ℓ / K) - a)| := by
      congr 2
      ring
    _ ≤ ENNReal.ofReal (|(X.slabTime b (chainSlab (ℓ / K) 0 i) new u v - ℓ / K) /
          Q K A (ℓ / K) - a| +
        |(X.slabTime b (chainSlab (ℓ / K) 0 i) old u v - ℓ / K) /
          Q K A (ℓ / K) - a|) := ENNReal.ofReal_le_ofReal (abs_sub _ _)
    _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add hnew hold

/-- Both error marginals have norm at most `ε`, so their sum has norm at most `2ε`.
This estimate is uniform in the block and in the label-resampling coupling. -/
theorem eLpNorm_profileError_pair_le_of_measurePreserving {Λ : X.LabelFamily} {b A ℓ ε : ℝ} {K L i : ℕ}
    {z : Fin m → ℤ} (h : LabelProfileBound X b K A ℓ L Λ ε) (hi : i < K)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (hold : MeasurePreserving old P' X.P) (hnew : MeasurePreserving new P' X.P) :
    eLpNorm (fun ω => profileError Λ b K A ℓ L i z (new ω) +
      profileError Λ b K A ℓ L i z (old ω)) (8 * (m + 1) : ℝ≥0∞) P' ≤
      ENNReal.ofReal (2 * ε) := by
  have hf := aestronglyMeasurable_profileError h hi (z := z)
  have hnewNorm := eLpNorm_comp_measurePreserving (p := (8 * (m + 1) : ℝ≥0∞)) hf hnew
  have holdNorm := eLpNorm_comp_measurePreserving (p := (8 * (m + 1) : ℝ≥0∞)) hf hold
  calc
    _ ≤ eLpNorm (profileError Λ b K A ℓ L i z ∘ new) (8 * (m + 1) : ℝ≥0∞) P' +
        eLpNorm (profileError Λ b K A ℓ L i z ∘ old) (8 * (m + 1) : ℝ≥0∞) P' :=
      eLpNorm_add_le (by exact_mod_cast (show 1 ≤ 8 * (m + 1) by omega))
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := by
      rw [hnewNorm, holdNorm]
      exact add_le_add (eLpNorm_profileError_le h hi) (eLpNorm_profileError_le h hi)
    _ = ENNReal.ofReal (2 * ε) := by
      by_cases hε : 0 ≤ ε
      · rw [← ENNReal.ofReal_add hε hε]
        congr 1
        ring
      · have hε' : ε ≤ 0 := (lt_of_not_ge hε).le
        rw [ENNReal.ofReal_of_nonpos hε', ENNReal.ofReal_of_nonpos
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hε')]
        exact add_zero 0

end IsotropicVariance.Paper.Proofs.LabelResidual
