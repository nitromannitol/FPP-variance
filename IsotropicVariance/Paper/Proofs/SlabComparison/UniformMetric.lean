/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.MeshPairs
public import IsotropicVariance.Paper.Proofs.SlabComparison.MeshExtension

/-! # Extending the long-pair finite maximum to a pathwise uniform metric estimate -/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

/-- Short pairs require only the deterministic upper density bound. -/
lemma metric_error_short (X : Setting m) (ω : X.Ω) {B : ℝ} (hB : X.IsUpperBound B)
    (hB0 : 0 ≤ B) {u v : Pt m} (h : dist u v ≤ 1) :
    |X.passTime ω u v - dist u v| ≤ B + 1 := by
  have hT := Profiles.passTime_le_mul_dist hB hB0 ω u v
  have hT0 := Profiles.passTime_nonneg (X := X) ω u v
  rw [abs_le]
  constructor <;> nlinarith [dist_nonneg (x := u) (y := v)]

/-- Long-pair control on a unit mesh suffices for all pairs in the covered region. -/
theorem uniform_metric_of_mesh (X : Setting m) (ω : X.Ω) {B S : ℝ}
    (hB : X.IsUpperBound B) (hB0 : 0 ≤ B) (hS : 1 ≤ S)
    {G : Finset (Pt m)} {U : Set (Pt m)}
    (hcover : ∀ x ∈ U, ∃ c ∈ G, dist x c ≤ 1)
    (hlong : ∀ u ∈ G, ∀ v ∈ G, 1 ≤ dist u v →
      |X.passTime ω u v - dist u v| ≤ S * Real.sqrt (dist u v)) :
    ∀ u ∈ U, ∀ v ∈ U, |X.passTime ω u v - dist u v| ≤
      (5 * B + 8) * (S * Real.sqrt (dist u v) + S ^ 2) := by
  intro u hu v hv
  obtain ⟨u', hu', huu'⟩ := hcover u hu
  obtain ⟨v', hv', hvv'⟩ := hcover v hv
  have hS0 : 0 ≤ S := by linarith
  have hSsq : 1 ≤ S ^ 2 := by nlinarith
  have hgrid : |X.passTime ω u' v' - dist u' v'| ≤
      (B + 2) * (S * Real.sqrt (dist u' v') + S ^ 2) := by
    have hbase0 : 0 ≤ S * Real.sqrt (dist u' v') := by positivity
    by_cases hd : 1 ≤ dist u' v'
    · have hh := hlong u' hu' v' hv' hd
      have hm := mul_nonneg (show 0 ≤ B + 1 by linarith) hbase0
      have hs := mul_nonneg (show 0 ≤ B + 2 by linarith) (sq_nonneg S)
      nlinarith
    · have hh := metric_error_short X ω hB hB0 (le_of_not_ge hd)
      have hm := mul_le_mul_of_nonneg_left hSsq (show 0 ≤ B + 2 by linarith)
      have hs := mul_nonneg (show 0 ≤ B + 2 by linarith) hbase0
      nlinarith
  have hh := metric_error_of_nearby_pair X ω (A := B + 2) (by linarith) hS hB0
    (Profiles.abs_passTime_sub_le hB hB0 ω) huu' hvv' hgrid
  convert hh using 1; ring

end IsotropicVariance.Paper.Proofs.SlabComparison
