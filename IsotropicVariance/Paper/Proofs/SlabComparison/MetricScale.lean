/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.ClassicalPairs
public import IsotropicVariance.Paper.Proofs.SlabComparison.OsScale

/-! # A common random metric scale for a finite family of long pairs -/

@[expose] public section
open MeasureTheory
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper Contracts
universe u
variable {m : ℕ}

/-- Add the deterministic mean error and the prescribed floor to the finite centered maximum.
The two constants are chosen before the mesh, its diameter, and the floor. -/
theorem finite_metric_scale_of (hclassical : ClassicalBoundsStatement.{u}) (hm : 1 ≤ m)
    (X : Setting.{u} m) (hnorm : X.IsNormalized) :
    ∃ Cb Cz : ℝ, 0 < Cb ∧ 0 < Cz ∧
      ∀ (T : Finset (Pt m × Pt m)) (_hT : T.Nonempty) (D L : ℝ), 1 ≤ D → 1 ≤ L →
      (∀ p ∈ T, 1 ≤ dist p.1 p.2 ∧ dist p.1 p.2 ≤ D) →
      ∃ S : X.Ω → ℝ, (∀ ω, L ≤ S ω) ∧
        Cited.IsOs X.P 2
          ((Real.log (2 * (T.card : ℝ)) / Real.log 2) ^ (1 / (2 : ℝ)) * Cz +
            (L + Cb * Real.sqrt (Real.log (2 + D)) + 2) / Real.sqrt (Real.log 2)) S ∧
        ∀ ω, ∀ p ∈ T, |X.passTime ω p.1 p.2 - dist p.1 p.2| ≤
          S ω * Real.sqrt (dist p.1 p.2) := by
  obtain ⟨Cb, hCb, hbias⟩ := classical_pairs_of hclassical hm X hnorm
  obtain ⟨Cz, hCz, hcenter⟩ := finite_centered_max_of hclassical hm X hnorm
  refine ⟨Cb, Cz, hCb, hCz, fun T hT D L hD hL hpairs => ?_⟩
  obtain ⟨Z, hZ, hZbound⟩ := hcenter T hT (fun p hp => (hpairs p hp).1)
  let c := L + Cb * Real.sqrt (Real.log (2 + D)) + 1
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcard : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
  have htheta : 0 < (Real.log (2 * (T.card : ℝ)) / Real.log 2) ^ (1 / (2 : ℝ)) * Cz := by
    apply mul_pos _ hCz
    apply Real.rpow_pos_of_pos
    exact div_pos (Real.log_pos (by linarith)) hlog
  refine ⟨fun ω => Z ω + c, fun ω => ?_, ?_, fun ω p hp => ?_⟩
  · have hz0 := (hZbound ω).1
    dsimp [c]
    nlinarith [mul_nonneg hCb.le (Real.sqrt_nonneg (Real.log (2 + D)))]
  · convert isOs_two_add_const hZ htheta hc using 1; dsimp [c]; congr 2; ring
  · obtain ⟨hlo, hhi⟩ := (hbias p.1 p.2 (hpairs p hp).1).2
    have hlogD : Real.log (2 + dist p.1 p.2) ≤ Real.log (2 + D) :=
      Real.log_le_log (by linarith [(hpairs p hp).1]) (by linarith [(hpairs p hp).2])
    have hroot := Real.sqrt_le_sqrt hlogD
    have hb : X.mean (dist p.1 p.2) - dist p.1 p.2 ≤
        Cb * Real.sqrt (dist p.1 p.2) * Real.sqrt (Real.log (2 + D)) := by
      rw [Real.sqrt_mul dist_nonneg] at hhi
      have hh := mul_le_mul_of_nonneg_left hroot
        (mul_nonneg hCb.le (Real.sqrt_nonneg (dist p.1 p.2)))
      nlinarith
    have hsplit : |X.passTime ω p.1 p.2 - dist p.1 p.2| ≤
        |X.passTime ω p.1 p.2 - X.mean (dist p.1 p.2)| +
          (X.mean (dist p.1 p.2) - dist p.1 p.2) := by
      have hh := abs_add_le (X.passTime ω p.1 p.2 - X.mean (dist p.1 p.2))
        (X.mean (dist p.1 p.2) - dist p.1 p.2)
      rw [abs_of_nonneg hlo] at hh
      convert hh using 1; congr 1; ring
    have hz := (hZbound ω).2 p hp
    dsimp [c]
    nlinarith [Real.sqrt_nonneg (dist p.1 p.2)]

end IsotropicVariance.Paper.Proofs.SlabComparison
