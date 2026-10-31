/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.ModulusThresholds
public import IsotropicVariance.Paper.Proofs.Profiles.Asymptotics
public import IsotropicVariance.Paper.Contracts.Profiles
public import IsotropicVariance.Paper.Contracts.Localization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Equation `eq:profiles` for the small pairs of Lemma `lem:modulus`

`isOs_smallFamily`: equation `eq:profiles` at the length `κn` for every small pair of the union
bound. Lemma `lem:modulus` is `IsotropicVariance.Paper.Proofs.Modulus.modulusStatement_of`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Modulus

open Cited Infra.Os

variable {m : ℕ}

/-- **The hypothesis of the union bound**: equation `eq:profiles` at the length `κn` for every
small pair. -/
lemma isOs_smallFamily (X : Setting m) (b : ℝ) {p : CubePair m} {κn σ Wκ θ : ℝ} {L : ℕ}
    (hn : 0 < p.dist) (hoff : ‖p.offset‖ ≤ p.dist / 2) (hκ0 : 0 < κn) (hσ : 0 ≤ σ)
    (hσW : σ ≤ 4 * Wκ) (hσL : σ * (Real.sqrt m * L) ≤ κn / 4)
    (hprof : ∀ q : CubePair m, q.IsAdmissible κn Wκ 1 →
      IsOs X.P 1 θ (fun ω => pairSup (X.passTime ω) q.first q.second) ∧
        IsOs X.P 1 θ (fun ω => pairSup (X.slabTime b q.slab ω) q.first q.second)) :
    ∀ q ∈ smallIndex m L, IsOs X.P 1 θ (smallFamily X b p κn σ q) := by
  rintro ⟨i, a, a'⟩ hq
  obtain ⟨-, hq2⟩ := Finset.mem_product.mp hq
  obtain ⟨ha, ha'⟩ := Finset.mem_product.mp hq2
  have hN := hprof _ (nearPair_isAdmissible p hσ hσW
    (small_offset_le hn hoff hκ0 hσ hσL ha ha').1)
  have hF := hprof _ (farPair_isAdmissible p hσ hσW
    (small_offset_le hn hoff hκ0 hσ hσL ha' ha).2)
  fin_cases i
  · exact hN.1
  · exact hN.2
  · exact hF.1
  · exact hF.2

end IsotropicVariance.Paper.Proofs.Modulus

