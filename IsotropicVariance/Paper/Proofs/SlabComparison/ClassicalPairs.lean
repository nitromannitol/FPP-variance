/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Classical
public import IsotropicVariance.Paper.Proofs.Profiles.Basic
public import IsotropicVariance.Infra.Os.Maximum

/-! # The classical bounds for arbitrary endpoint pairs

The proper-motion transport is the API of `IsotropicVariance.Paper.Proofs.Profiles.Basic`. No new
isotropy assumption or conclusion about a preferred coordinate direction is added to the classical
contract.
-/

@[expose] public section
open MeasureTheory
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper Contracts
universe u
variable {m : ℕ}

/-- The canonical classical estimate transports to all pairs of endpoints, with the same
constant and the canonical mean at their distance. -/
theorem classical_pairs_of (hclassical : ClassicalBoundsStatement.{u}) (hm : 1 ≤ m)
    (X : Setting.{u} m) (hnorm : X.IsNormalized) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Pt m, 1 ≤ dist u v →
      Cited.IsOs X.P 2 (C * Real.sqrt (dist u v))
        (fun ω => |X.passTime ω u v - X.mean (dist u v)|) ∧
      0 ≤ X.mean (dist u v) - dist u v ∧
      X.mean (dist u v) - dist u v ≤ C * Real.sqrt (dist u v * Real.log (2 + dist u v)) := by
  obtain ⟨C, hC, h⟩ := hclassical m hm X hnorm
  refine ⟨C, hC, fun u v huv => ?_⟩
  obtain ⟨hOs, hlo, hhi⟩ := h (dist u v) huv
  refine ⟨?_, hlo, hhi⟩
  apply Profiles.isOs_passTime_of_TRV (X := X) hm
    (continuous_abs.measurable.comp (measurable_id.sub_const (X.mean (dist u v)))) u v
  exact hOs

/-- Normalizing by the square root of distance leaves a uniform stochastic scale. -/
theorem classical_pairs_normalized_of (hclassical : ClassicalBoundsStatement.{u}) (hm : 1 ≤ m)
    (X : Setting.{u} m) (hnorm : X.IsNormalized) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Pt m, 1 ≤ dist u v →
      Cited.IsOs X.P 2 C
        (fun ω => |X.passTime ω u v - X.mean (dist u v)| / Real.sqrt (dist u v)) := by
  obtain ⟨C, hC, h⟩ := classical_pairs_of hclassical hm X hnorm
  refine ⟨C, hC, fun u v huv => ?_⟩
  have hr : 0 < Real.sqrt (dist u v) := Real.sqrt_pos.mpr (by linarith)
  have hh := (Infra.Os.isOs_mul_iff (P := X.P) (s := 2) (θ := C)
    (X := fun ω => |X.passTime ω u v - X.mean (dist u v)| / Real.sqrt (dist u v)) hr).mp
  apply hh
  convert (h u v huv).1 using 1
  · exact mul_comm _ _
  · funext ω
    field_simp

/-- A single finite maximum controls all centered fluctuations of mesh pairs. Independence
is neither available nor needed. The cardinality loss is the square root of its logarithm. -/
theorem finite_centered_max_of (hclassical : ClassicalBoundsStatement.{u}) (hm : 1 ≤ m)
    (X : Setting.{u} m) (hnorm : X.IsNormalized) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (Pt m × Pt m)) (_hT : T.Nonempty),
      (∀ p ∈ T, 1 ≤ dist p.1 p.2) →
      ∃ Z : X.Ω → ℝ,
        Cited.IsOs X.P 2
          ((Real.log (2 * (T.card : ℝ)) / Real.log 2) ^ (1 / (2 : ℝ)) * C) Z ∧
        ∀ ω, 0 ≤ Z ω ∧ ∀ p ∈ T,
          |X.passTime ω p.1 p.2 - X.mean (dist p.1 p.2)| ≤
            Z ω * Real.sqrt (dist p.1 p.2) := by
  classical
  obtain ⟨C, hC, h⟩ := classical_pairs_normalized_of hclassical hm X hnorm
  refine ⟨C, hC, fun T hT hlong => ?_⟩
  let Y : (Pt m × Pt m) → X.Ω → ℝ := fun p ω =>
    |X.passTime ω p.1 p.2 - X.mean (dist p.1 p.2)| / Real.sqrt (dist p.1 p.2)
  let Z := T.sup' hT Y
  refine ⟨Z, Infra.Os.isOs_finset_sup' (by norm_num) hC T hT Y
    (fun p hp => h p.1 p.2 (hlong p hp)), fun ω => ?_⟩
  have hle (p : Pt m × Pt m) (hp : p ∈ T) : Y p ω ≤ Z ω := by
    change Y p ω ≤ (T.sup' hT Y) ω
    rw [Finset.sup'_apply]
    exact Finset.le_sup' (fun p => Y p ω) hp
  constructor
  · obtain ⟨p, hp⟩ := hT
    exact (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)).trans (hle p hp)
  · intro p hp
    have hr : 0 < Real.sqrt (dist p.1 p.2) := Real.sqrt_pos.mpr (by linarith [hlong p hp])
    exact (div_le_iff₀ hr).mp (hle p hp)

end IsotropicVariance.Paper.Proofs.SlabComparison
