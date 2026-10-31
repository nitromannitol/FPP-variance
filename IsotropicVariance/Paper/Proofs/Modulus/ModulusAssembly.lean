/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.ModulusInstances
public import IsotropicVariance.Paper.Proofs.Modulus.ModulusMoments
public import IsotropicVariance.Paper.Proofs.Profiles.OsTools
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The modulus for one pair: two elementary bounds

* `pairSup_nonneg`: the profile supremum of a pair is nonnegative.
* `modulusSup_le_two_mul`: the modulus is at most twice the profile supremum.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Modulus

open Infra.Slab Infra.Os

variable {m : ℕ}

lemma pairSup_nonneg (D : Pt m → Pt m → ℝ) (I I' : Set (Pt m)) : 0 ≤ pairSup D I I' :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _

/-- The modulus is at most twice the profile supremum. -/
lemma modulusSup_le_two_mul {D : Pt m → Pt m → ℝ} {I I' : Set (Pt m)} {c : ℝ}
    (hc : ∀ u ∈ I, ∀ v ∈ I', |D u v - dist u v| ≤ c) (r : ℝ) :
    Contracts.modulusSup D I I' r ≤ 2 * pairSup D I I' := by
  have h0 : 0 ≤ 2 * pairSup D I I' := by have := pairSup_nonneg D I I'; positivity
  refine Real.iSup_le (fun u => Real.iSup_le (fun u₁ => Real.iSup_le (fun v =>
    Real.iSup_le (fun v₁ => Real.iSup_le (fun _ => ?_) h0) h0) h0) h0) h0
  obtain ⟨a1, a2⟩ := abs_le.mp (le_pairSup hc u.2 v.2)
  obtain ⟨b1, b2⟩ := abs_le.mp (le_pairSup hc u₁.2 v₁.2)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end IsotropicVariance.Paper.Proofs.Modulus
